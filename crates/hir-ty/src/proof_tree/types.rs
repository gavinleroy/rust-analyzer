//! Module for working with TyPeS.

use std::ops::ControlFlow;

use chalk_ir::{
    visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
    DebruijnIndex, WhereClause,
};
use tracing::debug;

use hir_def::{generics::GenericParams, GenericDefId, Lookup};
use intern::Interned;

use crate::{
    infer::unify::InferenceTable, interner::Interner, mapping::from_chalk_trait_id, HirDatabase,
};

pub(super) struct TypeInstantiator<'a> {
    pub context: &'a InferenceTable<'a>,
    pub source_bindings: Vec<Interned<GenericParams>>,
    // pub param_lists: FxHashMap<DebruijnIndex, >
}

impl<'a> TypeInstantiator<'a> {
    pub(crate) fn new(context: &'a InferenceTable<'a>) -> TypeInstantiator<'a> {
        Self {
            context,
            source_bindings: Vec::default(),
        }
    }
}

impl TypeInstantiator<'_> {
    fn db(&self) -> &dyn HirDatabase {
        self.context.db
    }
}

impl TypeVisitor<Interner> for TypeInstantiator<'_> {
    type BreakTy = ();

    fn as_dyn(&mut self) -> &mut dyn TypeVisitor<Interner, BreakTy = Self::BreakTy> {
        self
    }

    fn interner(&self) -> Interner {
        Interner
    }

    // At this points, we don't expect inference vars to exist.
    fn forbid_inference_vars(&self) -> bool {
        true
    }

    fn visit_where_clause(
        &mut self,
        where_clause: &WhereClause<Interner>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<Self::BreakTy> {
        debug!(?where_clause, "Visiting WhereClause");

        if let WhereClause::Implemented(trait_ref) = where_clause {
            let trait_id = trait_ref.trait_id;
            let subst = &trait_ref.substitution.as_slice(self.interner());
            let db = self.db();
            let id = from_chalk_trait_id(trait_id);
            let params = db.generic_params(id.into());

            debug!(?subst, ?params, "TraitRef params+subst");
        }

        where_clause.super_visit_with(self.as_dyn(), outer_binder)
    }
}
