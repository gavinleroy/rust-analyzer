//! Serialize Tree

use chalk_ir::{
    fold::{shift::Shift, FallibleTypeFolder, TypeFoldable, TypeFolder},
    interner::HasInterner,
    *,
};
use chalk_solve::RustIrDatabase;

use rustc_hash::FxHashMap;

use argus::{
    proof_tree::{self as pt, flat as ft, navigation::*},
    topology::{HasTopology, TreeTopology},
};

use super::{utils::*, writer::DeepDebug, *};
use crate::{infer::unify::InferenceTable, HirDatabase, Interner};

fn wrap_goal(s: String) -> GoalInfo {
    GoalInfo { goal: s }
}

macro_rules! sexp_it {
    ($e:expr, $db:expr) => {
        format!("{:?}", debug::Fmt(|fmt| $e.nfmt(fmt, $db.ir)))
    };
}

macro_rules! write_it {
    ($e:expr, $db:expr) => {
        format!(
            "{:?}",
            debug::Fmt(|fmt| {
                let c = &mut writer::DebugContext {
                    db: $db.db,
                    ir: $db.ir,
                    mapping: FxHashMap::default(),
                };
                $e.fmt_deep(fmt, c)
            })
        )
    };
}

macro_rules! to_string_goal {
    ($e:expr, $db:expr) => {
        wrap_goal(write_it!($e, $db))
    };
}

pub(crate) struct TreeContext<'a> {
    db: &'a dyn HirDatabase,
    ir: &'a dyn RustIrDatabase<Interner>,
    infer: &'a InferenceTable<'a>,
    proof: &'a dyn Navigation<Interner>,
}

impl From<TracedTraitQuery<'_>> for SerializeTree {
    fn from(query: TracedTraitQuery<'_>) -> Self {
        use super::NavigationExt;
        use crate::traits::ChalkContext;

        let TracedTraitQuery { krate, block, kind } = query;
        let relationship = FxHashMap::default();

        match kind {
            AttemptKind::Try(QueryAttempt { context, canonicalized, solution, trace }) => {
                let ir = &ChalkContext { db: context.db, krate, block };

                let trace = trace.without_fromenv(Interner);
                let trace = trace.without_duplicate_clauses(Interner);
                let trace = trace.without_obligations(Interner);
                let trace = trace.without_nonessential_goals(Interner);
                let trace = trace.without_sized_impls(ir);
                let trace = trace.prune_branches(Interner);

                let tctx = TreeContext { db: context.db, ir, infer: &context, proof: &trace };

                let mut new_nodes = IndexVec::default();
                let (new_root, TreeTopology { children, parent }) =
                    trace.get_topology().map_from(trace.get_root(), |nidx| {
                        let n = tctx.convert_node(nidx);
                        new_nodes.push(n)
                    });

                SerializeTree { root: new_root, nodes: new_nodes, children, parent, relationship }
            }
            AttemptKind::Required(attempts) => {
                let mut new_nodes = IndexVec::default();
                let mut new_topology = TreeTopology::new();

                let children = attempts
                    .into_iter()
                    .map(|attempt| {
                        let QueryAttempt { context, canonicalized, solution, trace } = attempt;
                        let ir = &ChalkContext { db: context.db, krate, block };

                        let trace = trace.without_fromenv(Interner);
                        let trace = trace.without_duplicate_clauses(Interner);
                        let trace = trace.without_obligations(Interner);
                        let trace = trace.without_nonessential_goals(Interner);
                        let trace = trace.without_sized_impls(ir);
                        let trace = trace.prune_branches(Interner);

                        let tctx =
                            TreeContext { db: context.db, ir, infer: &context, proof: &trace };

                        let (new_root, new_topo) =
                            trace.get_topology().map_from(trace.get_root(), |nidx| {
                                let n = tctx.convert_node(nidx);
                                new_nodes.push(n)
                            });

                        new_topology.add_in(new_topo).unwrap();

                        new_root
                    })
                    .collect::<Vec<_>>();

                let root = new_nodes.push(NodeGoal::Fixpoint);
                for child in children.into_iter() {
                    new_topology.add(root, child);
                }

                let TreeTopology { children, parent } = new_topology;

                SerializeTree { root, nodes: new_nodes, children, parent, relationship }
            }
        }
    }
}

impl TreeContext<'_> {
    fn resolve_from<T>(&self, from: ft::ProofNodeIdx, value: T) -> T
    where
        T: TypeFoldable<Interner> + HasInterner<Interner = Interner> + std::fmt::Debug,
    {
        return value;

        let path_tr = self.proof.path_to_root(from);

        let inference_path =
            path_tr.iter().filter_map(|&idx| self.proof.get_node(idx).inference_info());

        eprintln!("\n\n\n\n[RESOLVING] {:#?}\n", value);
        let value = inference_path.fold(value, |v, (tbl, subst)| {
            let table = &mut tbl.clone();

            eprint!("    · applying ");
            // eprint!(" [{subst:#?}]");
            // eprint!(" to: {v:#?}  -> ");
            let n = subst
                .apply(v, Interner)
                .try_fold_with(&mut convert::Resolver { table }, DebruijnIndex::INNERMOST)
                .expect("Resolving inference vars is Infallible.");

            eprintln!("{n:#?}\n");

            n
        });

        // TODO: if this works we can thread the mutability through
        let mut table = self.infer.clone();

        table.resolve_completely(value)
    }

    fn convert_node(&self, idx: ft::ProofNodeIdx) -> NodeGoal {
        let value = self.proof.get_node(idx);

        match value {
            pt::ProofTree::FromClauses(walker) => {
                NodeGoal::Goal { data: self.convert_clauses(idx, walker).tag("CLAUSES") }
            }
            pt::ProofTree::Fulfill(walker) => {
                NodeGoal::Goal { data: self.convert_fulfill(idx, walker).tag("FULFILL") }
            }
            pt::ProofTree::Obligation(walker) => {
                NodeGoal::Goal { data: self.convert_obligation(idx, walker).tag("OBLIGATION") }
            }
            pt::ProofTree::Leaf(leaf) => NodeGoal::Leaf { leaf: self.convert_leaf(idx, leaf) },
        }
    }

    fn convert_clauses(
        &self,
        idx: ft::ProofNodeIdx,
        value: &pt::SolveFromClauses<Interner>,
    ) -> GoalInfo {
        let goal = self.resolve_from(idx, value.goal().canonical.clone());
        to_string_goal!(goal, self)
    }

    fn convert_fulfill(
        &self,
        idx: ft::ProofNodeIdx,
        value: &pt::Fulfillment<Interner>,
    ) -> GoalInfo {
        match value.goal() {
            pt::FulfillmentKind::WithClause { goal, .. } => {
                let v = self.resolve_from(idx, goal.goal.clone());
                to_string_goal!(v, self)
            }
            pt::FulfillmentKind::WithSimplification { goal, .. } => {
                let v = self.resolve_from(idx, goal.goal.clone());
                to_string_goal!(v, self)
            }
        }
    }

    fn convert_obligation(
        &self,
        idx: ft::ProofNodeIdx,
        value: &pt::ObligationNode<Interner>,
    ) -> GoalInfo {
        let v = self.resolve_from(idx, value.obligation.goal.clone());
        to_string_goal!(v, self)
    }

    fn convert_leaf(&self, idx: ft::ProofNodeIdx, value: &pt::Leaf<Interner>) -> NodeLeaf {
        use std::borrow::Cow;

        let leaf_str = |s: Cow<'_, str>| NodeLeaf::WithString { value: s.to_string() };

        leaf_str(sexp_it!(value, self).into())
        // leaf_str(format!("{:?}", value).into())
    }
}

mod convert {
    use super::*;

    pub type ChalkInferenceTable = chalk_solve::infer::InferenceTable<Interner>;

    pub struct Resolver<'a> {
        pub(super) table: &'a mut ChalkInferenceTable,
    }

    impl<'i> FallibleTypeFolder<Interner> for Resolver<'i> {
        type Error = std::convert::Infallible;

        fn as_dyn(&mut self) -> &mut dyn FallibleTypeFolder<Interner, Error = Self::Error> {
            self
        }

        fn interner(&self) -> Interner {
            Interner
        }
    }

    impl<'i> TypeFolder<Interner> for Resolver<'i> {
        fn as_dyn(&mut self) -> &mut dyn TypeFolder<Interner> {
            self
        }

        fn interner(&self) -> Interner {
            Interner
        }

        #[tracing::instrument(level = "debug", skip(self))]
        fn fold_inference_ty(
            &mut self,
            var: InferenceVar,
            kind: TyVariableKind,
            outer_binder: DebruijnIndex,
        ) -> Ty<Interner> {
            match self.table.probe_var(var) {
                Some(ty) => {
                    let ty = ty.assert_ty_ref(Interner);
                    tracing::debug!("bound to {:?}", ty);
                    ty.clone()
                        .fold_with(self, DebruijnIndex::INNERMOST)
                        .shifted_in_from(Interner, outer_binder)
                }
                None => {
                    TyKind::InferenceVar(self.table.inference_var_root(var), kind).intern(Interner)
                }
            }
        }
    }
}
