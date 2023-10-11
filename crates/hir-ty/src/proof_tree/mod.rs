// pub mod serialize_tree;
mod types;
mod writer;
pub(crate) mod utils;
pub(crate) mod resolve;

use serde::Serialize;
use ts_rs::TS;

use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};

use argus::{proof_tree::ChildRelKind, utils::SexpExt};

/*
 * The serializable proof tree needs to incorporate:
 * - [ ] Chalk proofs / other constructs
 * - [ ] Rust types
 * - [ ] Rust constructs (impls mostly).
 */

// Core data structures used in the (serializable) proof tree
//
// === TODO ===
// - [ ] Nodes use opaque strings to store data, this is done
//       _temporarily_ to ease serialization and front-end experimentation.
//       It's not intended for long-term use, we just need to figure out
//       inference and instantiation first.

index_vec::define_index_type! {
    #[derive(TS)]
    pub struct NodeIdx = usize;
}

/// Currently an un-opinionated tree structure.
/// This will certainly change alongside the fronend.
#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct SerializeTree {
    pub root: NodeIdx,
    pub nodes: IndexVec<NodeIdx, NodeGoal>,
    pub children: FxHashMap<NodeIdx, FxHashSet<NodeIdx>>,
    pub parent: FxHashMap<NodeIdx, NodeIdx>,
    pub relationship: FxHashMap<NodeIdx, FxHashMap<NodeIdx, ChildRelKind>>,
}

// ----------------------------
// Sum combinations when needed

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "type")]
pub enum NodeGoal {
    Fixpoint,
    Goal { data: GoalInfo },
    Leaf { leaf: NodeLeaf },
}

// ------------------------------
// Nodes consisting of root Goals

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct GoalInfo {
    goal: String,
}

impl GoalInfo {
    /// TODO: remove, only used for debugging.
    fn tag(self, s: &str) -> Self {
        let goal = format!("[{s}] {}", self.goal);
        GoalInfo { goal }
    }
}

impl NodeLeaf {
    /// TODO: remove, only used for debugging.
    fn tag(self, s: &str) -> Self {
        match self {
            NodeLeaf::Halted => self,
            NodeLeaf::WithString { value } => {
                let value = format!("[{s}] {}", value);
                NodeLeaf::WithString { value }
            }
        }
    }
}

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "type")]
pub enum NodeLeaf {
    Halted,
    // TODO: this is a placeholder to view leaf types
    // without commiting too much to representation.
    WithString { value: String },
}

// -------------------------------------
// Nodes consiting of nested Obligations

index_vec::define_index_type! {
    #[derive(TS)]
    pub struct ObligationIdx = usize;
}

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Obligation {}

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct ObligationLeaf {}

// -------------------------------
// Nodes consiting of unifications

index_vec::define_index_type! {
    #[derive(TS)]
    pub struct UnificationIdx = usize;
}

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Unification {}

#[derive(TS, Serialize, Clone, Debug, PartialEq, Eq)]
pub struct UnificationLeaf {}

// ----------------------------------------------
// Tree modifications (for original ProofTreeNav)

use crate::Interner;

use argus::{
    proof_tree::{
        indices::ProofNodeIdx,
        navigation::{BuildControlFlow, Navigation, TreeView, ViewBuilder},
    },
    topology::TreeTopology,
};
use hir_def::lang_item::LangItem;

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
