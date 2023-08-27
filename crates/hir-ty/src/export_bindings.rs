#![cfg(test)]

use argus::proof_tree as apt;

use chalk_ir::{self as ir, interner::HasInterner as HasInternerTrait};
use chalk_solve as solve;

// NOTE, Because we are exporting everything into the same directory,
//       any name clashes must be resolved by first renaming.
use hir_def::{
    self as def, builtin_type as defbt, AdtId as ConcreteAdtId, ImplId as ConcreteImplId,
    TraitId as ConcreteTraitId,
};

use crate::{
    self as krate,
    interner::{self as int, Interner},
};

use serde::Serialize;
use ts_rs::TS;

#[derive(TS, Serialize)]
pub struct HasInterner;

impl HasInternerTrait for HasInterner {
    type Interner = Interner;
}

impl IntoIterator for HasInterner {
    type Item = <std::iter::Empty<()> as Iterator>::Item;
    type IntoIter = std::iter::Empty<()>;
    fn into_iter(self) -> Self::IntoIter {
        std::iter::empty()
    }
}

macro_rules! ts {
      ($name:literal, $($ty:ty,)*) => {
            $(
                  {
                        // TODO: this can be simplified, we can also get rid of the extra 'bindings'
                        //       directories which isn't really a problem, just weird.
                        use ts_rs::ExportError::*;
                        use std::path::{Path, PathBuf};
                        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").map_err(|_| ManifestDirNotSet).expect("Failed to get CARGO_MANIFEST_DIR");
                        let manifest_dir = Path::new(&manifest_dir);
                        let s = format!("bindings/{}", $name);
                        let additional = Path::new(&s);
                        let path = PathBuf::from(<$ty as TS>::EXPORT_TO.ok_or(CannotBeExported).expect("Failed to build export path"));
                        let resolved = manifest_dir.join(additional).join(path);
                        <$ty as TS>::export_to(resolved)
                              .expect(format!("Failed to export TS binding for type '{}'", stringify!($ty)).as_ref());
                  }
            )*
      };
      ($($ty:ty,)*) => {
            $(
                  <$ty as TS>::export()
                        .expect(format!("Failed to export TS binding for type '{}'", stringify!($ty)).as_ref());
            )*
      };
}

/* XXX Important note,
 *
 * The tests marked as IGNORE shouldn't ever be run. The types
 * aren't expected to change and the exported Typescript bindings
 * often need to be manually adjusted. If they *need* to be run,
 * feel free to talk to Gavin if you run into any issues.
 * */

#[test]
#[ignore]
fn export_chalk_ir() {
    ts! { "chalk-ir",

      ir::Void,
      ir::NoSolution,
      ir::Variance,
      ir::Environment::<Interner>,
      ir::InEnvironment::<HasInterner>,
      ir::IntTy,
      ir::UintTy,
      ir::FloatTy,
      ir::Scalar,
      ir::Safety,
      ir::Mutability,
      ir::UniverseIndex,
      ir::UniverseMap,
      ir::AdtId::<Interner>,
      ir::TraitId::<Interner>,
      ir::ImplId::<Interner>,
      ir::ClauseId::<Interner>,
      ir::AssocTypeId::<Interner>,
      ir::OpaqueTyId::<Interner>,
      ir::FnDefId::<Interner>,
      ir::ClosureId::<Interner>,
      ir::GeneratorId::<Interner>,
      ir::ForeignDefId::<Interner>,
      ir::Ty::<Interner>,
      ir::TyData::<Interner>,
      ir::TypeFlags,
      ir::TyKind::<Interner>,
      ir::BoundVar,
      ir::DebruijnIndex,
      ir::DynTy::<Interner>,
      ir::InferenceVar,
      ir::FnSig::<Interner>,
      ir::FnSubst::<Interner>,
      ir::FnPointer::<Interner>,
      ir::Const::<Interner>,
      ir::ConstData::<Interner>,
      ir::ConstValue::<Interner>,
      ir::ConcreteConst::<Interner>,
      ir::Lifetime::<Interner>,
      ir::LifetimeData::<Interner>,
      ir::PlaceholderIndex,
      ir::TyVariableKind,
      ir::VariableKind::<Interner>,
      ir::GenericArg::<Interner>,
      ir::GenericArgData::<Interner>,
      ir::WithKind::<Interner, ()>,
      ir::AliasTy::<Interner>,
      ir::ProjectionTy::<Interner>,
      ir::OpaqueTy::<Interner>,
      ir::TraitRef::<Interner>,
      ir::LifetimeOutlives::<Interner>,
      ir::TypeOutlives::<Interner>,
      ir::WhereClause::<Interner>,
      ir::WellFormed::<Interner>,
      ir::FromEnv::<Interner>,
      ir::DomainGoal::<Interner>,
      ir::EqGoal::<Interner>,
      ir::SubtypeGoal::<Interner>,
      ir::Normalize::<Interner>,
      ir::AliasEq::<Interner>,
      ir::Binders::<HasInterner>,
      ir::ProgramClauseImplication::<Interner>,
      ir::ClausePriority,
      ir::ProgramClauseData::<Interner>,
      ir::ProgramClause::<Interner>,
      ir::Canonical::<HasInterner>,
      ir::UCanonical::<HasInterner>,
      ir::Goal::<Interner>,
      ir::GoalData::<Interner>,
      ir::QuantifierKind,
      ir::Constraint::<Interner>,
      ir::ConstrainedSubst::<Interner>,
      ir::AnswerSubst::<Interner>,

      // Interned Items
      ir::QuantifiedWhereClauses::<Interner>,
      ir::ProgramClauses::<Interner>,
      ir::VariableKinds::<Interner>,
      ir::CanonicalVarKinds::<Interner>,
      ir::Goals::<Interner>,
      ir::Constraints::<Interner>,
      ir::Substitution::<Interner>,
      ir::Variances::<Interner>,

    }
}

#[test]
#[ignore]
fn export_chalk_solve() {
    ts! { "chalk-solve",

      solve::Solution::<Interner>,
      solve::Guidance::<Interner>,

    }
}

#[test]
#[ignore]
fn export_ra_hir_def() {
    ts! { "ra-hir-def",

      def::ModuleId,
      def::FunctionId,
      def::StructId,
      def::UnionId,
      def::EnumId,
      def::EnumVariantId,
      def::FieldId,
      def::ConstId,
      def::StaticId,
      ConcreteTraitId,
      def::TraitAliasId,
      def::TypeAliasId,
      ConcreteImplId,
      def::ExternBlockId,
      def::Macro2Id,
      def::MacroRulesId,
      def::ProcMacroId,
      def::BlockId,
      def::TypeOrConstParamId,
      def::TypeParamId,
      def::ConstParamId,
      def::LifetimeParamId,
      def::ItemContainerId,
      ConcreteAdtId,
      def::MacroId,
      def::GenericParamId,
      def::ModuleDefId,
      def::GeneralConstId,
      def::DefWithBodyId,
      def::AssocItemId,
      def::GenericDefId,
      def::AttrDefId,
      def::VariantId,

      // builtins
      defbt::BuiltinInt,
      defbt::BuiltinUint,
      defbt::BuiltinFloat,
      defbt::BuiltinType,

    }
}

#[test]
#[ignore]
fn export_ra_hir_ty() {
    ts! { "ra-hir-ty",

      krate::MemoryMap,
      krate::ConstScalar,
      krate::CallableSig,
      krate::CallableSig,
      Interner,
      int::InternedWrapper<()>,
      int::InternIdTS,

    }
}

// -------------------
// Non-ignored exports

#[test]
fn export_proof_tree() {
    // XXX: as of now, the proof tree isn't intended
    //      for frontend consumption, it is merely how
    //      we do tracing within Chalk, but then it's
    //      converted into a SerializeTree which has
    //      a better format. I(gavinleroy) don't yet know
    //      the best way to capture the Chalk traces, there's
    //      some funky corners that are rather difficult.
    //
    //      This is why almost everything is commented out.
    ts! { "proof-tree",

      // apt::ProofTree<Interner>,
      // apt::UnifyKind<Interner>,
      // apt::Opaque::<()>,
      // apt::EdgeInfo::<Interner>,
      // apt::PCINode::<Interner>,
      // apt::NestedNode::<Interner>,
      // apt::ClauseNode::<Interner>,
      // apt::LeafNode::<Interner>,
      // apt::UnifyNode,
      apt::ChildRelKind,

    }
}

#[test]
fn export_serialize_tree() {
    // Base types for serialize tree
    use crate::proof_tree as stpt;

    ts! { "serialize-tree",

      // XXX: A manual patch exists for indices,
      //      in `script/ts-bind.py`, because the output type
      //      isn't correct but adding a manual ts attribute doesn't
      //      seem to work.
      // st::NodeIdx,

      stpt::SerializeTree,
      stpt::NodeGoal,
      stpt::GoalInfo,
      stpt::NodeLeaf,
    }
}
