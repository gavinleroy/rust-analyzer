// pub mod serialize_tree;
mod types;
mod writer;
pub(crate) mod utils;
pub(crate) mod resolve;

use serde::Serialize;
use ts_rs::TS;

use chalk_ir::cast::Cast;
use chalk_ir::debug::Fmt;
use chalk_ir::fold::TypeFoldable;
use chalk_ir::Fallible;
use chalk_ir::{interner::HasInterner, zip::Zip, UniverseIndex};
use chalk_solve::RustIrDatabase;
use either::Either;
use hir_def::lang_item::LangItem;
use index_vec::IndexVec;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    infer::unify::{ChalkInferenceTable, InferenceTable},
    proof_tree::resolve::ResolvedTrace,
    CanonicalVarKind, DebruijnIndex, GenericArg, Goal, HirDatabase, InferenceVar, Interner,
    ProgramClauseImplication, Solution, Substitution, VariableKind,
};

use argus::{
    proof_tree::{
        indices::ProofNodeIdx,
        navigation::{BuildControlFlow, Navigation, TreeView, ViewBuilder},
        ChildRelKind, TreeDescription,
    },
    topology::TreeTopology,
    utils::SexpExt,
};

#[derive(TS, Serialize, Debug, Clone, PartialEq, Eq)]
pub struct SerializedTree {
    pub descr: TreeDescription,
    pub nodes: IndexVec<ProofNodeIdx, String>,
    pub topology: TreeTopology<ProofNodeIdx, ProofNodeIdx>,
}

pub(crate) trait NavigationExt {
    fn without_sized_impls<'a>(
        &'a self,
        ctx: &crate::traits::ChalkContext<'_>,
    ) -> TreeView<'a, Interner>;
}

impl<T: Navigation<Interner>> NavigationExt for T {
    fn without_sized_impls<'a>(
        &'a self,
        ctx: &crate::traits::ChalkContext<'_>,
    ) -> TreeView<'a, Interner> {
        use crate::mapping::to_chalk_trait_id;
        use chalk_ir::{TraitRef, WhereClause};

        struct Walker<'b> {
            new_topo: TreeTopology<ProofNodeIdx, ProofNodeIdx>,
            tree: &'b dyn Navigation<Interner>,
            ctx: &'b crate::traits::ChalkContext<'b>,
        }

        impl ViewBuilder<Interner> for Walker<'_> {
            fn get_nav(&self) -> &dyn Navigation<Interner> {
                self.tree
            }

            fn get_new_topology(&mut self) -> &mut TreeTopology<ProofNodeIdx, ProofNodeIdx> {
                &mut self.new_topo
            }

            fn node_pred(&self, node: ProofNodeIdx) -> BuildControlFlow {
                use chalk_ir::WhereClause;
                let node = self.get_nav().get_node(node);

                let sized_trait = self
                    .ctx
                    .db
                    .lang_item(self.ctx.krate, LangItem::Sized)
                    .and_then(|item| item.as_trait())
                    .map(|sized_trait_| to_chalk_trait_id(sized_trait_));

                match (node.as_where_clause(Interner), sized_trait) {
                    // Remove nodes of the form: `???: Sized`.
                    (Some(WhereClause::Implemented(TraitRef { trait_id, .. })), Some(sized))
                        if trait_id == sized =>
                    {
                        BuildControlFlow::NoStop
                    }
                    _ => BuildControlFlow::YesContinue,
                }
            }
        }

        let mut walker = Walker { new_topo: TreeTopology::new(), tree: &*self, ctx };

        walker.run();

        TreeView { from: self, topology: walker.new_topo }
    }
}

pub fn serialize_resolved_tree(
    db: &dyn HirDatabase,
    resolved: ResolvedTrace<'_>,
) -> SerializedTree {
    use crate::traits::ChalkContext;
    use writer::DeepDebug;

    let ir = &ChalkContext { db, krate: resolved.info.krate, block: resolved.info.block };

    macro_rules! _to_string {
        ($e:expr) => {
            format!(
                "{:?}",
                Fmt(|fmt| {
                    let ctx = &mut writer::DebugContext { db, ir, mapping: FxHashMap::default() };
                    $e.fmt_deep(fmt, ctx)
                })
            )
        };
    }

    let n = resolved.resolved_goals.len();

    let string_nodes: IndexVec<ProofNodeIdx, String> = IndexVec::from_iter(
        resolved.resolved_goals.into_iter().sorted_by(|a, b| a.0.cmp(&b.0)).map(|(idx, node)| {
            match node {
                Either::Left(goal) => {
                    let mut table = resolved.tables[&idx].clone();
                    let goal = resolve_completely(&mut table, goal);
                    _to_string!(&goal)
                }
                Either::Right(fsol) => _to_string!(&fsol),
            }
        }),
    );

    SerializedTree {
        descr: resolved.query.trace.descr,
        nodes: string_nodes,
        topology: resolved.query.trace.topology,
    }
}

// ------------------------------------

pub(crate) fn resolve_with_fallback<T>(
    table: &mut InferenceTable<'_>,
    t: T,
    fallback: &dyn Fn(InferenceVar, VariableKind, GenericArg, DebruijnIndex) -> GenericArg,
) -> T
where
    T: HasInterner<Interner = Interner> + TypeFoldable<Interner>,
{
    resolve_with_fallback_inner(table, &mut Vec::new(), t, &fallback)
}

fn resolve_with_fallback_inner<T>(
    table: &mut InferenceTable<'_>,
    var_stack: &mut Vec<InferenceVar>,
    t: T,
    fallback: &dyn Fn(InferenceVar, VariableKind, GenericArg, DebruijnIndex) -> GenericArg,
) -> T
where
    T: HasInterner<Interner = Interner> + TypeFoldable<Interner>,
{
    t.fold_with(
        &mut internal_resolve::Resolver { table, var_stack, fallback },
        DebruijnIndex::INNERMOST,
    )
}

pub(crate) fn resolve_completely<T>(table: &mut InferenceTable<'_>, t: T) -> T
where
    T: HasInterner<Interner = Interner> + TypeFoldable<Interner>,
{
    resolve_with_fallback(table, t, &|_, _, d, _| d)
}

mod internal_resolve {
    use super::InferenceTable;
    use crate::{
        ConcreteConst, Const, ConstData, ConstScalar, ConstValue, DebruijnIndex, GenericArg,
        InferenceVar, Interner, Lifetime, Ty, TyVariableKind, VariableKind,
    };
    use chalk_ir::{
        cast::Cast,
        fold::{TypeFoldable, TypeFolder},
    };

    #[derive(chalk_derive::FallibleTypeFolder)]
    #[has_interner(Interner)]
    pub(super) struct Resolver<
        'a,
        'b,
        F: Fn(InferenceVar, VariableKind, GenericArg, DebruijnIndex) -> GenericArg,
    > {
        pub(super) table: &'a mut InferenceTable<'b>,
        pub(super) var_stack: &'a mut Vec<InferenceVar>,
        pub(super) fallback: F,
    }

    impl<F> TypeFolder<Interner> for Resolver<'_, '_, F>
    where
        F: Fn(InferenceVar, VariableKind, GenericArg, DebruijnIndex) -> GenericArg,
    {
        fn as_dyn(&mut self) -> &mut dyn TypeFolder<Interner, Error = Self::Error> {
            self
        }

        fn interner(&self) -> Interner {
            Interner
        }

        fn fold_inference_ty(
            &mut self,
            var: InferenceVar,
            kind: TyVariableKind,
            outer_binder: DebruijnIndex,
        ) -> Ty {
            let var = self.table.var_unification_table.inference_var_root(var);
            if self.var_stack.contains(&var) {
                // recursive type
                let default = self.table.fallback_value(var, kind).cast(Interner);
                return (self.fallback)(var, VariableKind::Ty(kind), default, outer_binder)
                    .assert_ty_ref(Interner)
                    .clone();
            }
            let result = if let Some(known_ty) = self.table.var_unification_table.probe_var(var) {
                // known_ty may contain other variables that are known by now
                self.var_stack.push(var);
                let result = known_ty.fold_with(self, outer_binder);
                self.var_stack.pop();
                result.assert_ty_ref(Interner).clone()
            } else {
                let default = self.table.fallback_value(var, kind).cast(Interner);
                (self.fallback)(var, VariableKind::Ty(kind), default, outer_binder)
                    .assert_ty_ref(Interner)
                    .clone()
            };
            result
        }

        fn fold_inference_const(
            &mut self,
            ty: Ty,
            var: InferenceVar,
            outer_binder: DebruijnIndex,
        ) -> Const {
            let var = self.table.var_unification_table.inference_var_root(var);
            let default = ConstData {
                ty: ty.clone(),
                value: ConstValue::Concrete(ConcreteConst { interned: ConstScalar::Unknown }),
            }
            .intern(Interner)
            .cast(Interner);
            if self.var_stack.contains(&var) {
                // recursive
                return (self.fallback)(var, VariableKind::Const(ty), default, outer_binder)
                    .assert_const_ref(Interner)
                    .clone();
            }
            if let Some(known_ty) = self.table.var_unification_table.probe_var(var) {
                // known_ty may contain other variables that are known by now
                self.var_stack.push(var);
                let result = known_ty.fold_with(self, outer_binder);
                self.var_stack.pop();
                result.assert_const_ref(Interner).clone()
            } else {
                (self.fallback)(var, VariableKind::Const(ty), default, outer_binder)
                    .assert_const_ref(Interner)
                    .clone()
            }
        }

        fn fold_inference_lifetime(
            &mut self,
            _var: InferenceVar,
            _outer_binder: DebruijnIndex,
        ) -> Lifetime {
            // fall back all lifetimes to 'static -- currently we don't deal
            // with any lifetimes, but we can sometimes get some lifetime
            // variables through Chalk's unification, and this at least makes
            // sure we don't leak them outside of inference
            crate::static_lifetime()
        }
    }
}
