pub mod serialize_tree;
mod types;
mod writer;

use serde::Serialize;
use ts_rs::TS;

use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};

use argus::{proof_tree::ChildRelKind, utils::SexpExt};

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
