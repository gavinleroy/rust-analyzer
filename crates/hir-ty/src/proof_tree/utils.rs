//! Extra struct utilities for debugging in Rust Analyzer.
//! I keep these here to reduce visual noise when comparing with the original code.

use std::{
    fmt::{self, Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
};

use base_db::salsa::InternId;
use chalk_ir::TSerialize;
use intern::{Internable, Interned};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

use serde::{Serialize, Serializer};
use ts_rs::TS;

use crate::{
    Canonical, InEnvironment, Goal, Solution, ProofTree,
    infer::unify,
};

// ----------------
// Inference junk

index_vec::define_index_type! {
    pub struct ObligationKey = usize;
}


#[derive(Clone, Debug)]
pub struct QueryAttempt<'a> {
    pub(crate) context: unify::InferenceTable<'a>,
    pub canonicalized: Canonical<InEnvironment<Goal>>,
    pub solution: Option<Solution>,
    pub trace: ProofTree,
}

#[derive(Clone, Debug)]
pub enum AttemptKind<'a> {
    Required(Vec<QueryAttempt<'a>>),
    Try(QueryAttempt<'a>),
}

#[derive(Clone, Debug)]
pub struct TracedTraitQuery<'a> {
    pub krate: base_db::CrateId,
    pub block: Option<hir_def::BlockId>,
    pub kind: AttemptKind<'a>,
}


#[derive(Debug, Clone, Default)]
pub struct ObligationTracker<'a> {
    /// The obligation attempts during the process of type-checking. For a given
    /// tracked obligation, there may be several attempts at making it succeed.
    /// These are *required* to succeed for type-checking to succeed.
    pub tracked: IndexVec<ObligationKey, Vec<QueryAttempt<'a>>>,

    pub info: FxHashMap<ObligationKey, (base_db::CrateId, Option<hir_def::BlockId>)>,

    /// During type-inference sometimes RA wants to know if something holds,
    /// but that isn't necessarily required for type-checking to succeed. The
    /// responses here *can* dictate what is tried in the future.
    pub other: Vec<TracedTraitQuery<'a>>,
}

// ----------------
// Interner junk

pub struct InternedTS<T: Internable + ?Sized + Serialize>(pub Interned<T>);

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

#[derive(PartialEq, Eq, Hash)]
#[cfg_attr(feature = "tserialize", derive(TS, Serialize))]
pub struct InternedWrapper<T: TSerialize>(pub T);

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