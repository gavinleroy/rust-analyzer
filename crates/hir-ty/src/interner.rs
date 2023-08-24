//! Implementation of the Chalk `Interner` trait, which allows customizing the
//! representation of the various objects Chalk deals with (types, goals etc.).

use std::{
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
};

use crate::{chalk_db, tls, ConstScalar, GenericArg};
use base_db::salsa::InternId;
use chalk_ir::{Goal, GoalData, TSerialize};
use hir_def::TypeAliasId;
use intern::{impl_internable, Internable, Interned};
use smallvec::SmallVec;
use std::fmt;
use triomphe::Arc;

use serde::{Serialize, Serializer};
use ts_rs::TS;

#[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
#[cfg_attr(feature = "tserialize", derive(TS, Serialize))]
pub struct Interner;

pub struct InternedTS<T: Internable + ?Sized + Serialize>(pub Interned<T>);

// --- ---

impl<T: Internable + ?Sized + TSerialize> TS for InternedTS<T> {
    fn name() -> String {
        T::name()
    }
    fn name_with_type_args(mut args: Vec<String>) -> String {
        assert_eq!(args.len(), 1);
        args.remove(0)
    }
    fn inline() -> String {
        T::inline()
    }
    fn inline_flattened() -> String {
        T::inline_flattened()
    }
    fn dependencies() -> Vec<ts_rs::Dependency> {
        T::dependencies()
    }
    fn transparent() -> bool {
        T::transparent()
    }
}

impl<T: Internable + ?Sized + TSerialize> Serialize for InternedTS<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<T: Internable + TSerialize> PartialEq for InternedTS<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: Internable + TSerialize> Eq for InternedTS<T> {}

impl PartialEq for InternedTS<str> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for InternedTS<str> {}

impl<T: Internable + ?Sized + TSerialize> Hash for InternedTS<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T: Internable + ?Sized + TSerialize> AsRef<T> for InternedTS<T> {
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T: Internable + ?Sized + TSerialize> Deref for InternedTS<T> {
    type Target = Interned<T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Internable + ?Sized + TSerialize> From<Interned<T>> for InternedTS<T> {
    fn from(data: Interned<T>) -> Self {
        InternedTS(data)
    }
}

impl<T: Internable + ?Sized + TSerialize> Clone for InternedTS<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Debug + Internable + ?Sized + TSerialize> Debug for InternedTS<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.0).fmt(f)
    }
}

impl<T: Display + Internable + ?Sized + TSerialize> Display for InternedTS<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.0).fmt(f)
    }
}

// --- ---

#[derive(PartialEq, Eq, Hash)]
#[cfg_attr(feature = "tserialize", derive(TS, Serialize))]
pub struct InternedWrapper<T: TSerialize>(T);

impl<T: fmt::Debug + TSerialize> fmt::Debug for InternedWrapper<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<T: TSerialize> std::ops::Deref for InternedWrapper<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(TS, Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InternIdTS(#[ts(type = "number")] pub InternId);

impl Serialize for InternIdTS {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let s = format!("{}", self.0.as_usize());
        serializer.serialize_str(&s)
    }
}

impl std::ops::Deref for InternIdTS {
    type Target = InternId;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Display for InternIdTS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl From<InternId> for InternIdTS {
    fn from(data: InternId) -> Self {
        InternIdTS(data)
    }
}

impl_internable!(
    InternedWrapper<Vec<chalk_ir::VariableKind<Interner>>>,
    InternedWrapper<SmallVec<[GenericArg; 2]>>,
    InternedWrapper<chalk_ir::TyData<Interner>>,
    InternedWrapper<chalk_ir::LifetimeData<Interner>>,
    InternedWrapper<chalk_ir::ConstData<Interner>>,
    InternedWrapper<ConstScalar>,
    InternedWrapper<Vec<chalk_ir::CanonicalVarKind<Interner>>>,
    InternedWrapper<Vec<chalk_ir::ProgramClause<Interner>>>,
    InternedWrapper<Vec<chalk_ir::QuantifiedWhereClause<Interner>>>,
    InternedWrapper<Vec<chalk_ir::Variance>>,
);

impl chalk_ir::interner::Interner for Interner {
    type InternedType = InternedTS<InternedWrapper<chalk_ir::TyData<Self>>>;
    type InternedLifetime = InternedTS<InternedWrapper<chalk_ir::LifetimeData<Self>>>;
    type InternedConst = InternedTS<InternedWrapper<chalk_ir::ConstData<Self>>>;
    type InternedConcreteConst = ConstScalar;
    type InternedGenericArg = chalk_ir::GenericArgData<Self>;
    type InternedGoal = Arc<GoalData<Self>>;
    type InternedGoals = Vec<Goal<Self>>;
    type InternedSubstitution = InternedTS<InternedWrapper<SmallVec<[GenericArg; 2]>>>;
    type InternedProgramClauses = InternedTS<InternedWrapper<Vec<chalk_ir::ProgramClause<Self>>>>;
    type InternedProgramClause = chalk_ir::ProgramClauseData<Self>;
    type InternedQuantifiedWhereClauses =
        InternedTS<InternedWrapper<Vec<chalk_ir::QuantifiedWhereClause<Self>>>>;
    type InternedVariableKinds = InternedTS<InternedWrapper<Vec<chalk_ir::VariableKind<Interner>>>>;
    type InternedCanonicalVarKinds =
        InternedTS<InternedWrapper<Vec<chalk_ir::CanonicalVarKind<Self>>>>;
    type InternedConstraints = Vec<chalk_ir::InEnvironment<chalk_ir::Constraint<Self>>>;
    type InternedVariances = InternedTS<InternedWrapper<Vec<chalk_ir::Variance>>>;
    type DefId = InternIdTS;
    type InternedAdtId = hir_def::AdtId;
    type Identifier = TypeAliasId;
    type FnAbi = ();

    fn debug_adt_id(
        type_kind_id: chalk_db::AdtId,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        tls::with_current_program(|prog| Some(prog?.debug_struct_id(type_kind_id, fmt)))
    }

    fn debug_trait_id(
        type_kind_id: chalk_db::TraitId,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        tls::with_current_program(|prog| Some(prog?.debug_trait_id(type_kind_id, fmt)))
    }

    fn debug_assoc_type_id(
        id: chalk_db::AssocTypeId,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        tls::with_current_program(|prog| Some(prog?.debug_assoc_type_id(id, fmt)))
    }

    fn debug_opaque_ty_id(
        opaque_ty_id: chalk_ir::OpaqueTyId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "OpaqueTy#{}", opaque_ty_id.0))
    }

    fn debug_fn_def_id(
        fn_def_id: chalk_ir::FnDefId<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        tls::with_current_program(|prog| Some(prog?.debug_fn_def_id(fn_def_id, fmt)))
    }

    fn debug_closure_id(
        _fn_def_id: chalk_ir::ClosureId<Self>,
        _fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    fn debug_alias(
        alias: &chalk_ir::AliasTy<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        match alias {
            chalk_ir::AliasTy::Projection(projection_ty) => {
                Interner::debug_projection_ty(projection_ty, fmt)
            }
            chalk_ir::AliasTy::Opaque(opaque_ty) => Some(opaque_ty.fmt(fmt)),
        }
    }

    fn debug_projection_ty(
        proj: &chalk_ir::ProjectionTy<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        tls::with_current_program(|prog| Some(prog?.debug_projection_ty(proj, fmt)))
    }

    fn debug_opaque_ty(
        opaque_ty: &chalk_ir::OpaqueTy<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", opaque_ty.opaque_ty_id))
    }

    fn debug_ty(ty: &chalk_ir::Ty<Interner>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", ty.data(Interner)))
    }

    fn debug_lifetime(
        lifetime: &chalk_ir::Lifetime<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", lifetime.data(Interner)))
    }

    fn debug_const(
        constant: &chalk_ir::Const<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", constant.data(Interner)))
    }

    fn debug_generic_arg(
        parameter: &GenericArg,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", parameter.data(Interner).inner_debug()))
    }

    fn debug_variable_kinds(
        variable_kinds: &chalk_ir::VariableKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", variable_kinds.as_slice(Interner)))
    }

    fn debug_variable_kinds_with_angles(
        variable_kinds: &chalk_ir::VariableKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", variable_kinds.inner_debug(Interner)))
    }

    fn debug_canonical_var_kinds(
        canonical_var_kinds: &chalk_ir::CanonicalVarKinds<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", canonical_var_kinds.as_slice(Interner)))
    }
    fn debug_goal(goal: &Goal<Interner>, fmt: &mut fmt::Formatter<'_>) -> Option<fmt::Result> {
        let goal_data = goal.data(Interner);
        Some(write!(fmt, "{goal_data:?}"))
    }
    fn debug_goals(
        goals: &chalk_ir::Goals<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", goals.debug(Interner)))
    }
    fn debug_program_clause_implication(
        pci: &chalk_ir::ProgramClauseImplication<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", pci.debug(Interner)))
    }
    fn debug_program_clause(
        clause: &chalk_ir::ProgramClause<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", clause.data(Interner)))
    }
    fn debug_program_clauses(
        clauses: &chalk_ir::ProgramClauses<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", clauses.as_slice(Interner)))
    }
    fn debug_substitution(
        substitution: &chalk_ir::Substitution<Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", substitution.debug(Interner)))
    }
    fn debug_separator_trait_ref(
        separator_trait_ref: &chalk_ir::SeparatorTraitRef<'_, Interner>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", separator_trait_ref.debug(Interner)))
    }

    fn debug_quantified_where_clauses(
        clauses: &chalk_ir::QuantifiedWhereClauses<Self>,
        fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        Some(write!(fmt, "{:?}", clauses.as_slice(Interner)))
    }

    fn debug_constraints(
        _clauses: &chalk_ir::Constraints<Self>,
        _fmt: &mut fmt::Formatter<'_>,
    ) -> Option<fmt::Result> {
        None
    }

    fn intern_ty(self, kind: chalk_ir::TyKind<Self>) -> Self::InternedType {
        let flags = kind.compute_flags(self);
        Interned::new(InternedWrapper(chalk_ir::TyData { kind, flags })).into()
    }

    fn ty_data(self, ty: &Self::InternedType) -> &chalk_ir::TyData<Self> {
        &ty.0
    }

    fn intern_lifetime(self, lifetime: chalk_ir::LifetimeData<Self>) -> Self::InternedLifetime {
        Interned::new(InternedWrapper(lifetime)).into()
    }

    fn lifetime_data(self, lifetime: &Self::InternedLifetime) -> &chalk_ir::LifetimeData<Self> {
        &lifetime.0
    }

    fn intern_const(self, constant: chalk_ir::ConstData<Self>) -> Self::InternedConst {
        Interned::new(InternedWrapper(constant)).into()
    }

    fn const_data(self, constant: &Self::InternedConst) -> &chalk_ir::ConstData<Self> {
        &constant.0
    }

    fn const_eq(
        self,
        _ty: &Self::InternedType,
        c1: &Self::InternedConcreteConst,
        c2: &Self::InternedConcreteConst,
    ) -> bool {
        (c1 == &ConstScalar::Unknown) || (c2 == &ConstScalar::Unknown) || (c1 == c2)
    }

    fn intern_generic_arg(
        self,
        parameter: chalk_ir::GenericArgData<Self>,
    ) -> Self::InternedGenericArg {
        parameter
    }

    fn generic_arg_data(
        self,
        parameter: &Self::InternedGenericArg,
    ) -> &chalk_ir::GenericArgData<Self> {
        parameter
    }

    fn intern_goal(self, goal: GoalData<Self>) -> Self::InternedGoal {
        Arc::new(goal).into()
    }

    fn goal_data(self, goal: &Self::InternedGoal) -> &GoalData<Self> {
        goal
    }

    fn intern_goals<E>(
        self,
        data: impl IntoIterator<Item = Result<Goal<Self>, E>>,
    ) -> Result<Self::InternedGoals, E> {
        data.into_iter().collect()
    }

    fn goals_data(self, goals: &Self::InternedGoals) -> &[Goal<Interner>] {
        goals
    }

    fn intern_substitution<E>(
        self,
        data: impl IntoIterator<Item = Result<GenericArg, E>>,
    ) -> Result<Self::InternedSubstitution, E> {
        let v: InternedWrapper<SmallVec<[GenericArg; 2]>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn substitution_data(self, substitution: &Self::InternedSubstitution) -> &[GenericArg] {
        &substitution.as_ref().0
    }

    fn intern_program_clause(
        self,
        data: chalk_ir::ProgramClauseData<Self>,
    ) -> Self::InternedProgramClause {
        data
    }

    fn program_clause_data(
        self,
        clause: &Self::InternedProgramClause,
    ) -> &chalk_ir::ProgramClauseData<Self> {
        clause
    }

    fn intern_program_clauses<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::ProgramClause<Self>, E>>,
    ) -> Result<Self::InternedProgramClauses, E> {
        let v: InternedWrapper<Vec<chalk_ir::ProgramClause<Self>>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn program_clauses_data(
        self,
        clauses: &Self::InternedProgramClauses,
    ) -> &[chalk_ir::ProgramClause<Self>] {
        clauses
    }

    fn intern_quantified_where_clauses<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::QuantifiedWhereClause<Self>, E>>,
    ) -> Result<Self::InternedQuantifiedWhereClauses, E> {
        let v: InternedWrapper<Vec<chalk_ir::QuantifiedWhereClause<Self>>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn quantified_where_clauses_data(
        self,
        clauses: &Self::InternedQuantifiedWhereClauses,
    ) -> &[chalk_ir::QuantifiedWhereClause<Self>] {
        clauses
    }

    fn intern_generic_arg_kinds<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::VariableKind<Self>, E>>,
    ) -> Result<Self::InternedVariableKinds, E> {
        let v: InternedWrapper<Vec<chalk_ir::VariableKind<Interner>>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn variable_kinds_data(
        self,
        parameter_kinds: &Self::InternedVariableKinds,
    ) -> &[chalk_ir::VariableKind<Self>] {
        &parameter_kinds.as_ref().0
    }

    fn intern_canonical_var_kinds<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::CanonicalVarKind<Self>, E>>,
    ) -> Result<Self::InternedCanonicalVarKinds, E> {
        let v: InternedWrapper<Vec<chalk_ir::CanonicalVarKind<Self>>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn canonical_var_kinds_data(
        self,
        canonical_var_kinds: &Self::InternedCanonicalVarKinds,
    ) -> &[chalk_ir::CanonicalVarKind<Self>] {
        canonical_var_kinds
    }
    fn intern_constraints<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::InEnvironment<chalk_ir::Constraint<Self>>, E>>,
    ) -> Result<Self::InternedConstraints, E> {
        data.into_iter().collect()
    }
    fn constraints_data(
        self,
        constraints: &Self::InternedConstraints,
    ) -> &[chalk_ir::InEnvironment<chalk_ir::Constraint<Self>>] {
        constraints
    }

    fn intern_variances<E>(
        self,
        data: impl IntoIterator<Item = Result<chalk_ir::Variance, E>>,
    ) -> Result<Self::InternedVariances, E> {
        let v: InternedWrapper<Vec<chalk_ir::Variance>> =
            InternedWrapper(data.into_iter().collect::<Result<_, _>>()?);
        Ok(Interned::new(v).into())
    }

    fn variances_data(self, variances: &Self::InternedVariances) -> &[chalk_ir::Variance] {
        variances
    }
}

impl chalk_ir::interner::HasInterner for Interner {
    type Interner = Self;
}

#[macro_export]
macro_rules! has_interner {
    ($t:ty) => {
        impl HasInterner for $t {
            type Interner = crate::Interner;
        }
    };
}
