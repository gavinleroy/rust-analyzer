//! Debug impls for types.

use std::fmt::{Debug, Error, Formatter};
use std::marker::PhantomData;

use hir_def::GenericDefId;

use rustc_hash::FxHashMap;

use chalk_ir::{debug::*, interner::HasInterner, TSerialize, *};
use chalk_solve::RustIrDatabase;

use crate::{
    interner::Interner,
    mapping::{from_assoc_type_id, from_chalk_trait_id, ToChalk},
    CallableDefId, HirDatabase,
};

/* === CURRENT TODO(gavinleroy) ===
 *
 * - [ ] resolve all inference vars within nodes.
 * - [ ] many of the items are filled with a `todo!`
 * - [ ] track generic params from where they were generated.
 *       E.g., `IntoSystemConfig<M>` instead of `IntoSystemConfig<Marker>`.
 * - [X] track reentrant obligations (fixpoints at the inference level) so
 *       we can filter them.
 * - [ ] remove the "advanced goals" from the output. For now. Later we
 *       can introduce a mechanism to toggle them.
 *
 */

macro_rules! deep {
    ($fmt:expr, $ctxt:expr, $($expr:expr),*) => {{
        $(
            $expr.fmt_deep($fmt, $ctxt)?;
        )*
        Ok(())
    }}
}

pub trait DeepDebug: std::fmt::Debug {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error>;
}

#[derive(Clone)]
pub struct DebugContext<'a, 'b>
where
    'a: 'b,
{
    pub db: &'a dyn HirDatabase,
    pub ir: &'a dyn RustIrDatabase<Interner>,
    pub mapping: FxHashMap<BoundVar, &'b str>,
}

#[allow(dead_code)]
fn compare_formatting<T>(name: &str, value: T, ctxt: &DebugContext<'_, '_>)
where
    T: std::fmt::Debug + argus::utils::SexpExt<Interner> + DeepDebug,
{
    println!(
        "{:?}",
        debug::Fmt(|f| {
            let mut local = ctxt.clone();

            writeln!(f, "{}", name)?;
            writeln!(f, "DEBUG: {:?}", value)?;

            write!(f, "SEXP: ")?;
            value.nfmt(f, ctxt.ir)?;
            writeln!(f, "")?;

            write!(f, "WRITE: ")?;
            value.fmt_deep(f, &mut local)?;
            writeln!(f, "")
        })
    );
}

impl<'a, 'b> DebugContext<'a, 'b> {
    fn shift_context<'c, T>(
        &self,
        map: FxHashMap<BoundVar, &'c str>,
        scope: impl FnOnce(&mut Self) -> T + 'c,
    ) -> T
    where
        'c: 'b,
    {
        use std::collections::hash_map::Entry;

        let mut this = DebugContext { db: &*self.db, ir: &*self.ir, mapping: map };

        for (&k, &v) in self.mapping.iter() {
            match this.mapping.entry(k) {
                Entry::Vacant(o) => {
                    o.insert(v);
                }
                Entry::Occupied(_) => (),
            }
        }

        scope(&mut this)
    }
}

#[derive(Debug)]
struct WrapAngle;

#[derive(Debug)]
struct WrapRound;

#[derive(Debug)]
struct WrapCurly;

#[derive(Debug)]
struct WrapSquare;

trait ToWrapped<'a, T: DeepDebug> {
    fn using_angle(&'a self) -> Wrapped<'a, T, WrapAngle>;
    fn using_round(&'a self) -> Wrapped<'a, T, WrapRound>;
    fn using_curly(&'a self) -> Wrapped<'a, T, WrapCurly>;
    fn using_square(&'a self) -> Wrapped<'a, T, WrapSquare>;
}

#[derive(Debug)]
struct Wrapped<'a, T: DeepDebug, K> {
    data: &'a [T],
    phantom: PhantomData<K>,
}

impl DeepDebug for &str {
    fn fmt_deep(&self, fmt: &mut Formatter<'_>, _: &mut DebugContext<'_, '_>) -> Result<(), Error> {
        if self.is_empty() {
            panic!("Printing empty string!");
        }

        write!(fmt, "{}", self)
    }
}

impl DeepDebug for String {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_str().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for &usize {
    fn fmt_deep(&self, fmt: &mut Formatter<'_>, _: &mut DebugContext<'_, '_>) -> Result<(), Error> {
        write!(fmt, "{}", self)
    }
}

impl<T: DeepDebug, K> Wrapped<'_, T, K> {
    fn internal_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
        (b, e): (&str, &str),
        allow_empty: bool,
    ) -> Result<(), Error> {
        if self.data.len() == 0 && allow_empty {
            return Ok(());
        }

        b.fmt_deep(fmt, ctxt)?;

        for (i, v) in self.data.iter().enumerate() {
            if i > 0 {
                write!(fmt, ", ")?;
            }
            v.fmt_deep(fmt, ctxt)?;
        }

        e.fmt_deep(fmt, ctxt)?;

        Ok(())
    }
}

impl<T: DeepDebug> DeepDebug for Wrapped<'_, T, WrapAngle> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.internal_deep(fmt, ctxt, ("<", ">"), true)
    }
}

impl<T: DeepDebug> DeepDebug for Wrapped<'_, T, WrapRound> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.internal_deep(fmt, ctxt, ("(", ")"), false)
    }
}

impl<T: DeepDebug> DeepDebug for Wrapped<'_, T, WrapCurly> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.internal_deep(fmt, ctxt, ("{", "}"), true)
    }
}

impl<T: DeepDebug> DeepDebug for Wrapped<'_, T, WrapSquare> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.internal_deep(fmt, ctxt, ("[", "]"), true)
    }
}

impl<'a, T: DeepDebug> ToWrapped<'a, T> for [T] {
    fn using_angle(&'a self) -> Wrapped<'a, T, WrapAngle> {
        Wrapped { data: self, phantom: PhantomData }
    }

    fn using_round(&'a self) -> Wrapped<'a, T, WrapRound> {
        Wrapped { data: self, phantom: PhantomData }
    }

    fn using_curly(&'a self) -> Wrapped<'a, T, WrapCurly> {
        Wrapped { data: self, phantom: PhantomData }
    }

    fn using_square(&'a self) -> Wrapped<'a, T, WrapSquare> {
        Wrapped { data: self, phantom: PhantomData }
    }
}

impl<'a> ToWrapped<'a, GenericArg<Interner>> for Substitution<Interner> {
    fn using_angle(&'a self) -> Wrapped<'a, GenericArg<Interner>, WrapAngle> {
        Wrapped { data: self.as_slice(Interner), phantom: PhantomData }
    }

    fn using_round(&'a self) -> Wrapped<'a, GenericArg<Interner>, WrapRound> {
        Wrapped { data: self.as_slice(Interner), phantom: PhantomData }
    }

    fn using_curly(&'a self) -> Wrapped<'a, GenericArg<Interner>, WrapCurly> {
        Wrapped { data: self.as_slice(Interner), phantom: PhantomData }
    }

    fn using_square(&'a self) -> Wrapped<'a, GenericArg<Interner>, WrapSquare> {
        Wrapped { data: self.as_slice(Interner), phantom: PhantomData }
    }
}

#[derive(Debug)]
struct GenericFallback<'a> {
    id: GenericDefId,
    subst: &'a [GenericArg<Interner>],
}

impl<'a> GenericFallback<'a> {
    fn new(id: impl Into<GenericDefId>, subst: &'a [GenericArg<Interner>]) -> Self {
        Self { id: id.into(), subst }
    }
}

impl DeepDebug for GenericFallback<'_> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let gen_params = ctxt.db.generic_params(self.id).clone();
        let gen_params = &gen_params.type_or_consts;

        let associations = self
            .subst
            .iter()
            // HACK: both lists should be skipped in the same place!
            .zip(gen_params.iter().skip(1))
            .filter_map(|(barg, (_, sarg))| {
                // eprintln!(
                //     "{}",
                //     debug::Fmt(|f| {
                //         let lctxt = &mut ctxt.clone();
                //         deep!(f, lctxt, "BoundVar: ", barg, "\n")?;
                //         writeln!(f, "{sarg:?}")
                //     })
                // );

                match (barg.ty(Interner), sarg.name()) {
                    (Some(ty), Some(source_name))
                        if ty.bound_var(Interner).is_some() && source_name.as_str().is_some() =>
                    {
                        Some((ty.bound_var(Interner).unwrap(), source_name.as_str().unwrap()))
                    }
                    _ => None,
                }
            })
            .collect::<FxHashMap<_, _>>();

        ctxt.shift_context(associations, |ctxt| self.subst.using_angle().fmt_deep(fmt, ctxt))
    }
}

// ----------------------
// END: boilerplate stuff
// ----------------------

impl<T: HasInterner<Interner = Interner> + DeepDebug> DeepDebug for UCanonical<T> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.canonical.fmt_deep(fmt, ctxt)
    }
}

impl<T: HasInterner<Interner = Interner> + DeepDebug> DeepDebug for Canonical<T> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.value.fmt_deep(fmt, ctxt)
    }
}

impl<T: HasInterner<Interner = Interner> + DeepDebug + TSerialize> DeepDebug for InEnvironment<T> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.goal.fmt_deep(fmt, ctxt)
    }
}

// ------------

impl DeepDebug for hir_expand::name::Name {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> std::fmt::Result {
        self.unescaped().to_smol_str().as_str().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for TraitId<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        ctxt.ir.trait_name(*self).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for AdtId<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // TODO: use HirDatabase
        ctxt.ir.adt_name(*self).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for AssocTypeId<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // FIXME: is this the right transformation?
        let id = from_assoc_type_id(*self);
        let name = ctxt.db.type_alias_data(id).name.clone();
        name.fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for FnDefId<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> std::fmt::Result {
        let call_id = CallableDefId::from_chalk(ctxt.db, *self);
        let name = match call_id {
            CallableDefId::FunctionId(id) => ctxt.db.function_data(id).name.clone(),
            CallableDefId::StructId(id) => ctxt.db.struct_data(id).name.clone(),
            // FIXME: using parent here is (probably) wrong.
            CallableDefId::EnumVariantId(id) => ctxt.db.enum_data(id.parent).name.clone(),
        };

        name.fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ClosureId<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> std::fmt::Result {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for GeneratorId<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> std::fmt::Result {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for ForeignDefId<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> std::fmt::Result {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for Ty<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for Lifetime<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for Const<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ConcreteConst<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for GenericArg<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for Goal<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for Goals<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_slice(Interner).using_square().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ProgramClauseImplication<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.debug(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ProgramClause<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.data(Interner).fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ProgramClauses<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_slice(Interner).using_square().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for Constraints<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_slice(Interner).using_square().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for SeparatorTraitRef<'_, Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let parameters = self.trait_ref.substitution.as_slice(Interner);
        let sep = self.separator;
        let id = from_chalk_trait_id(self.trait_ref.trait_id);
        let ga = GenericFallback::new(id, &parameters[1..]);

        deep!(fmt, ctxt, parameters[0], sep, self.trait_ref.trait_id, ga)
    }
}

impl DeepDebug for AliasTy<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // TODO wrapper??
        match self {
            AliasTy::Projection(pty) => pty.fmt_deep(fmt, ctxt),
            AliasTy::Opaque(oty) => oty.fmt_deep(fmt, ctxt),
        }
    }
}

impl DeepDebug for QuantifiedWhereClauses<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_slice(Interner).using_square().fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for ProjectionTy<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let ga = GenericFallback::new(
            from_assoc_type_id(self.associated_ty_id),
            self.substitution.as_slice(Interner),
        );
        deep!(fmt, ctxt, "(", self.associated_ty_id, ")", ga)
    }
}

impl DeepDebug for OpaqueTy<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // TODO:
        // GenericFallback::new(self.opaque_ty_id, self.substitution.as_slice(Interner));
        let ga = self.substitution.using_angle();
        deep!(fmt, ctxt, "(", self.opaque_ty_id, ")", ga)
    }
}

impl DeepDebug for OpaqueTyId<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for UniverseIndex {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for TyData<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.kind.fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for TyKind<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // TODO!
        match self {
            TyKind::BoundVar(db) => db.fmt_deep(fmt, ctxt),
            TyKind::Dyn(clauses) => clauses.fmt_deep(fmt, ctxt),
            TyKind::InferenceVar(var, TyVariableKind::General) => deep!(fmt, ctxt, var, "var"),
            TyKind::InferenceVar(var, TyVariableKind::Integer) => deep!(fmt, ctxt, var, "i"),
            TyKind::InferenceVar(var, TyVariableKind::Float) => deep!(fmt, ctxt, var, "f"),
            TyKind::Alias(alias) => alias.fmt_deep(fmt, ctxt),
            TyKind::Placeholder(index) => index.fmt_deep(fmt, ctxt),
            TyKind::Function(function) => function.fmt_deep(fmt, ctxt),

            // ------------------------
            // --- TYPES WITH SUBST ---
            // ------------------------
            TyKind::Adt(id, substitution) => {
                id.fmt_deep(fmt, ctxt)?;
                let chalk_ir::AdtId(adt_id) = id;
                let ga = GenericFallback::new(*adt_id, substitution.as_slice(Interner));

                // FIXME: why does this version print out the adt name twice?
                // In the GenericFallback the first parameter is skipped, which should skip the
                // name and thus still only print once (namely, here). But that doesn't seem to
                // be true??? TODO: investigate.
                // deep!(fmt, ctxt, id, ga)
                deep!(fmt, ctxt, ga)
            }
            TyKind::AssociatedType(_assoc_ty, _substitution) => {
                write!(fmt, "{:?}", self)
            }
            TyKind::Tuple(_arity, substitution) => {
                deep!(fmt, ctxt, substitution.using_round())
            }
            TyKind::OpaqueType(_opaque_ty, _substitution) => {
                write!(fmt, "{:?}", self)
            }
            TyKind::Slice(_substitution) => {
                write!(fmt, "{:?}", self)
            }
            TyKind::FnDef(fn_def, substitution) => {
                let call_id = CallableDefId::from_chalk(ctxt.db, *fn_def);
                let ga = GenericFallback::new(call_id, substitution.as_slice(Interner));
                deep!(fmt, ctxt, fn_def, ga)
            }
            TyKind::Closure(_id, _substitution) => {
                write!(fmt, "{:?}", self)
            }
            TyKind::Generator(_generator, _substitution) => {
                write!(fmt, "{:?}", self)
            }
            TyKind::GeneratorWitness(_witness, _substitution) => {
                write!(fmt, "{:?}", self)
            }

            TyKind::Scalar(scalar) => scalar.fmt_deep(fmt, ctxt),
            TyKind::Str => deep!(fmt, ctxt, "Str"),
            TyKind::Ref(mutability, lifetime, ty) => match mutability {
                Mutability::Mut => deep!(fmt, ctxt, "(&", lifetime, " mut ", ty, ")"),
                Mutability::Not => deep!(fmt, ctxt, "(&", lifetime, " ", ty, ")"),
            },
            TyKind::Raw(mutability, ty) => match mutability {
                Mutability::Mut => deep!(fmt, ctxt, "(*mut ", ty, ")"),
                Mutability::Not => deep!(fmt, ctxt, "(*const ", ty, ")"),
            },
            TyKind::Never => deep!(fmt, ctxt, "Never"),
            TyKind::Array(ty, const_) => deep!(fmt, ctxt, "[", ty, ";", const_, "]"),
            TyKind::Foreign(foreign_ty) => foreign_ty.fmt_deep(fmt, ctxt),
            TyKind::Error => deep!(fmt, ctxt, "{{error}}"),
        }
    }
}

impl DeepDebug for Scalar {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for BoundVar {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        if let Some(s) = ctxt.mapping.get(self).copied() {
            s.fmt_deep(fmt, ctxt)
        } else {
            write!(fmt, "{:?}", self)
        }
    }
}

impl DeepDebug for DebruijnIndex {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for DynTy<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for InferenceVar {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        // todo!("{self:?} inference var found!")
        write!(_fmt, "{:?}", self)
    }
}

// NOTE: the last element represents the return type.
impl DeepDebug for FnSubst<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let all_elems = self.0.as_slice(Interner);
        let Some((ret, args)) = all_elems.split_last() else {
            unreachable!();
        };
        deep!(fmt, ctxt, args.using_round(), " -> ", ret)
    }
}

impl DeepDebug for Safety {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            Safety::Unsafe => "unsafe ".fmt_deep(fmt, ctxt),
            Safety::Safe => Ok(()),
        }
    }
}

impl DeepDebug for FnPointer<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let FnPointer { num_binders: _, substitution, sig } = self;

        deep!(fmt, ctxt, sig.safety, "fn", substitution)
    }
}

impl DeepDebug for LifetimeData<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            LifetimeData::BoundVar(db) => db.fmt_deep(fmt, ctxt),
            LifetimeData::InferenceVar(var) => var.fmt_deep(fmt, ctxt),
            LifetimeData::Placeholder(index) => index.fmt_deep(fmt, ctxt),
            LifetimeData::Static => "'static".fmt_deep(fmt, ctxt),
            LifetimeData::Erased => "'<erased>".fmt_deep(fmt, ctxt),
            LifetimeData::Phantom(..) => unreachable!(),
        }
    }
}

impl<'a> DeepDebug for VariableKindsInnerDebug<'a, Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for ConstData<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for QuantifierKind {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            QuantifierKind::ForAll => deep!(fmt, ctxt, "forall"),
            QuantifierKind::Exists => deep!(fmt, ctxt, "exists"),
        }
    }
}

impl DeepDebug for GoalData<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            GoalData::Quantified(qkind, ref subgoal) => {
                // TODO(gavinleroy) how do we do this!!!!
                deep!(fmt, ctxt, qkind, "{{", subgoal.skip_binders(), "}}")
            }

            GoalData::Implies(ref wc, ref g) => {
                deep!(fmt, ctxt, "if (", wc, ") {{", g, "}}")
            }

            GoalData::All(ref goals) => {
                deep!(fmt, ctxt, "all(", goals, ")")
            }
            GoalData::Not(ref g) => {
                deep!(fmt, ctxt, "not(", g, ")")
            }
            GoalData::EqGoal(ref wc) => wc.fmt_deep(fmt, ctxt),
            GoalData::SubtypeGoal(ref wc) => wc.fmt_deep(fmt, ctxt),
            GoalData::DomainGoal(ref wc) => wc.fmt_deep(fmt, ctxt),
            GoalData::CannotProve => deep!(fmt, ctxt, r"¯\_(ツ)_/¯"),
        }
    }
}

impl<'a> DeepDebug for ProgramClauseImplicationDebug<'a, Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl<'a> DeepDebug for TyKindDebug<'a, Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl<'a> DeepDebug for SubstitutionDebug<'a, Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for PlaceholderIndex {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for TraitRef<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let dbg = SeparatorTraitRef { trait_ref: self, separator: " as " };

        dbg.fmt_deep(fmt, ctxt)
    }
}

impl DeepDebug for LifetimeOutlives<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for TypeOutlives<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for Normalize<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        deep!(fmt, ctxt, "(", self.alias, " -> ", self.ty, ")")
    }
}

impl DeepDebug for AliasEq<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        deep!(fmt, ctxt, self.alias, " = ", self.ty)
    }
}

impl DeepDebug for WhereClause<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            WhereClause::Implemented(tr) => {
                let dbg = SeparatorTraitRef { trait_ref: tr, separator: ": " };

                deep!(fmt, ctxt, dbg)
            }
            WhereClause::AliasEq(a) => a.fmt_deep(fmt, ctxt),
            WhereClause::LifetimeOutlives(l_o) => l_o.fmt_deep(fmt, ctxt),
            WhereClause::TypeOutlives(t_o) => t_o.fmt_deep(fmt, ctxt),
        }
    }
}

impl DeepDebug for FromEnv<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            FromEnv::Trait(t) => {
                let dbg = SeparatorTraitRef { trait_ref: t, separator: ": " };

                deep!(fmt, ctxt, "FromEnv(", dbg, ")")
            }
            FromEnv::Ty(t) => t.fmt_deep(fmt, ctxt),
        }
    }
}

impl DeepDebug for WellFormed<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            WellFormed::Trait(t) => {
                let dbg = SeparatorTraitRef { trait_ref: t, separator: ": " };

                deep!(fmt, ctxt, "FromEnv(", dbg, ")")
            }
            WellFormed::Ty(t) => t.fmt_deep(fmt, ctxt),
        }
    }
}

impl DeepDebug for DomainGoal<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            DomainGoal::Holds(n) => n.fmt_deep(fmt, ctxt),
            DomainGoal::WellFormed(n) => n.fmt_deep(fmt, ctxt),
            DomainGoal::FromEnv(n) => n.fmt_deep(fmt, ctxt),
            DomainGoal::Normalize(n) => n.fmt_deep(fmt, ctxt),

            // TODO
            DomainGoal::IsLocal(..)
            | DomainGoal::IsUpstream(..)
            | DomainGoal::IsFullyVisible(..)
            | DomainGoal::LocalImplAllowed(..)
            | DomainGoal::Compatible
            // | DomainGoal::LocalImplAllowed(..)
            | DomainGoal::DownstreamType(..)
            | DomainGoal::Reveal
            | DomainGoal::ObjectSafe(..) => write!(fmt, "{:?}", self),
        }
    }
}

impl DeepDebug for EqGoal<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        deep!(fmt, ctxt, "(", self.a, " = ", self.b, ")")
    }
}

impl DeepDebug for SubtypeGoal<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        deep!(fmt, ctxt, "(", self.a, " <: ", self.b, ")")
    }
}

impl<T: HasInterner + Debug> DeepDebug for Binders<T> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for ProgramClauseData<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for Environment<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        write!(_fmt, "{:?}", self)
    }
}

impl DeepDebug for CanonicalVarKinds<Interner> {
    fn fmt_deep(
        &self,
        _fmt: &mut Formatter<'_>,
        _ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        todo!("CanonicalVarKinds {:?}", self)
    }
}

impl DeepDebug for GenericArgData<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            GenericArgData::Ty(t) => t.fmt_deep(fmt, ctxt),
            GenericArgData::Lifetime(l) => l.fmt_deep(fmt, ctxt),
            GenericArgData::Const(c) => c.fmt_deep(fmt, ctxt),
        }
    }
}

impl DeepDebug for VariableKind<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            VariableKind::Ty(TyVariableKind::General) => deep!(fmt, ctxt, "type"),
            VariableKind::Ty(TyVariableKind::Integer) => deep!(fmt, ctxt, "integer type"),
            VariableKind::Ty(TyVariableKind::Float) => deep!(fmt, ctxt, "float type"),
            VariableKind::Lifetime => deep!(fmt, ctxt, "lifetime"),
            VariableKind::Const(ty) => ty.fmt_deep(fmt, ctxt),
        }
    }
}

impl<T: DeepDebug> DeepDebug for WithKind<Interner, T> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        let value = self.skip_kind();
        match &self.kind {
            VariableKind::Ty(TyVariableKind::General) => deep!(fmt, ctxt, value, " with kind type"),
            VariableKind::Ty(TyVariableKind::Integer) => {
                deep!(fmt, ctxt, value, " with kind integer type")
            }
            VariableKind::Ty(TyVariableKind::Float) => {
                deep!(fmt, ctxt, value, " with kind float type")
            }
            VariableKind::Lifetime => deep!(fmt, ctxt, value, "{:?} with kind lifetime"),
            VariableKind::Const(ty) => deep!(fmt, ctxt, value, " with kind ", ty),
        }
    }
}

impl DeepDebug for Constraint<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            Constraint::LifetimeOutlives(a, b) => {
                deep!(fmt, ctxt, a, ": ", b)
            }
            Constraint::TypeOutlives(ty, lifetime) => {
                deep!(fmt, ctxt, ty, ": ", lifetime)
            }
        }
    }
}

impl DeepDebug for Variance {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        match self {
            Variance::Covariant => deep!(fmt, ctxt, "Covariant"),
            Variance::Invariant => deep!(fmt, ctxt, "Invariant"),
            Variance::Contravariant => deep!(fmt, ctxt, "Contravariant"),
        }
    }
}

impl DeepDebug for Variances<Interner> {
    fn fmt_deep(
        &self,
        fmt: &mut Formatter<'_>,
        ctxt: &mut DebugContext<'_, '_>,
    ) -> Result<(), Error> {
        self.as_slice(Interner).using_square().fmt_deep(fmt, ctxt)
    }
}
