//! Resolving all contextual type information (de Bruijn indices, etc...).

use std::borrow::BorrowMut;

use argus::{
    proof_tree::{flat::ProofTreeNav, fulfill::FulfillmentKind, navigation::NavRooted, ProofTree},
    utils::InferenceTableExt,
};

use tracing::{debug, instrument};

use chalk_ir::cast::Cast;
use chalk_ir::fold::TypeFoldable;
use chalk_ir::Fallible;
use chalk_ir::{interner::HasInterner, zip::Zip, UniverseIndex};
use either::Either;
use index_vec::IndexVec;
use itertools::Itertools;

use super::{utils::*, *};
use crate::{
    infer::unify::{ChalkInferenceTable, InferenceTable},
    CanonicalVarKind, DebruijnIndex, GenericArg, InferenceVar, ProgramClauseImplication, Solution,
    Substitution, VariableKind,
};
use crate::{Goal, InEnvironment};

pub struct ResolvedTrace<'a> {
    pub info: ObligationSource,
    pub(crate) tables: FxHashMap<ProofNodeIdx, InferenceTable<'a>>,
    pub resolved_goals: FxHashMap<ProofNodeIdx, Either<Goal, Fallible<Solution>>>,
    pub query: QueryAttempt,
}

#[tracing::instrument(level = "info", skip(table))]
fn expect_unify<T: ?Sized + Zip<Interner>>(table: &mut InferenceTable<'_>, t1: &T, t2: &T) {
    if table.try_unify(t1, t2).is_err() {
        tracing::warn!(
            r#"
Couldn't unify:
    {t1:?}
    {t2:?}
"#
        );
    }
}

#[tracing::instrument(level = "info", skip(table, query))]
pub(crate) fn resolve_bindings<'a>(
    table: &mut InferenceTable<'a>,
    query: &TracedTraitQuery,
) -> ResolvedTrace<'a> {
    let AttemptKind::Required(qas) = &query.kind else {
        todo!();
    };

    let biggest = qas.into_iter().max_set_by(|a, b| {
        let len_a = a.trace.nodes.len();
        let len_b = b.trace.nodes.len();
        len_a.cmp(&len_b)
    });

    let qa = *biggest.first().unwrap();

    struct Env<'b, 'c> {
        prev: InEnvironment<Goal>,
        prev_clause_subst: Option<Substitution>,
        table: InferenceTable<'b>,
        tables: FxHashMap<ProofNodeIdx, InferenceTable<'b>>,
        nodes: FxHashMap<ProofNodeIdx, Either<Goal, Fallible<Solution>>>,
        trace: &'c ProofTreeNav<Interner>,
    }

    let mut env = Env {
        prev: query.info.goal.clone().cast(Interner),
        prev_clause_subst: None,
        table: table.clone(),
        tables: FxHashMap::default(),
        nodes: FxHashMap::default(),
        trace: &qa.trace,
    };

    tracing::debug!("Visiting at least {:?} nodes", env.trace.nodes.len());

    fn resolve_node(env: &mut Env<'_, '_>, node: ProofNodeIdx) {
        let resolved;

        if env.nodes.contains_key(&node) {
            return;
        }

        let node_data = &env.trace.nodes[node];

        tracing::debug!("Visiting node {:?} {:?}", node, node_data);

        match node_data {
            // Assumption, the previous goal is the same shape as this one.
            //
            // `FromClauses` is the node that attempts a different clause when proving
            // the rule. This means that the previous goal, is the same as this one, we are
            // just gathering the possible program clauses that will prove by implication.
            //
            // Steps:
            // Instantiate the canonicalized goal in this context.
            // Unify new inference variables with those already in the context
            //   (i.e., those from the previous goal).
            ProofTree::FromClauses(value) => {
                debug!("before canonical");
                let canonical = value.goal().canonical.clone();
                debug!("before instantiate");
                let goal = env.table.instantiate_canonical(canonical).cast(Interner);
                debug!("before unify");
                expect_unify(&mut env.table, &env.prev, &goal);
                resolved = Either::Left(goal.goal.clone());
                env.prev = goal;
            }

            // Assumption, the previous goal is the same shape as this one.
            //
            // TODO
            ProofTree::Fulfill(value) => match value.goal() {
                FulfillmentKind::WithClause { goal, clause } => {
                    debug!("before instantiate");
                    let pci = env.table.instantiate_binders_existentially(Interner, clause.clone());
                    debug!("before into value");
                    let (pc, binders) = clause.clone().into_value_and_skipped_binders();
                    let value = goal.canonical.value.clone();

                    debug!("before args building");

                    let clause_args = binders
                        .iter(Interner)
                        .cloned()
                        .map(|pk| CanonicalVarKind::new(pk, UniverseIndex::root()))
                        .collect::<Vec<_>>();
                    let canonical_args =
                        goal.canonical.binders.iter(Interner).cloned().collect::<Vec<_>>();

                    let the_args = if clause_args.len() < canonical_args.len() {
                        canonical_args
                    } else {
                        clause_args
                    };

                    let clause_subst = env.table.fresh_subst(&the_args);
                    let goal = clause_subst.apply(value.clone(), Interner).cast(Interner);

                    debug!("before unify");
                    // Unify the goal with the previous
                    expect_unify(&mut env.table, &env.prev, &goal);

                    debug!("before unify");
                    // Unify the prev with the consequence of the goal pci @ (consequence :- [conditions ⩘ ...])
                    expect_unify(
                        &mut env.table,
                        &env.prev.goal,
                        &pci.consequence.clone().cast(Interner),
                    );

                    resolved = Either::Left(goal.goal.clone());
                    env.prev = goal.clone();
                    env.prev_clause_subst = Some(clause_subst);
                }

                FulfillmentKind::WithSimplification { goal, .. } => {
                    eprintln!("[Using Simpl] {:?}", {
                        // TODO
                        todo!()
                    });
                }
            },

            // Assumptions:
            // - The parent node is a `Fulfill` node.
            // - The goal here is on of the conditions of the program clause.
            // - The clause substitution was stored.
            //
            // TODO
            ProofTree::Obligation(value) => {
                let clause_subst = env.prev_clause_subst.clone().unwrap();
                let goal = clause_subst
                    .apply(value.goal().canonical.value.clone(), Interner)
                    .cast(Interner);
                resolved = Either::Left(goal.goal.clone());
                env.prev = goal;
            }

            ProofTree::Leaf(leaf) => {
                let leaf = leaf.outcome.clone();
                // TODO we need to instantiate the solution, but Argus
                // isn't currently capturing Canonical solutions, just solutions...
                // UGH
                // let leaf = env.table.instantiate_canonical(leaf);
                resolved = Either::Right(leaf);
            }
        }

        let _p = env.nodes.insert(node, resolved);
        if _p.is_some() {
            panic!("Inserting twice {node:?} {_p:?}");
        }
        let _p = env.tables.insert(node, env.table.clone());
        if _p.is_some() {
            panic!("Inserting twice {node:?} {_p:?}");
        }

        let this_table = env.table.clone();
        let this_prev = env.prev.clone();
        let this_subst = env.prev_clause_subst.clone();

        for child in env.trace.topology.children(node) {
            env.table = this_table.clone();
            env.prev = this_prev.clone();
            env.prev_clause_subst = this_subst.clone();

            resolve_node(env, child);
        }
    }

    let root = env.trace.descr.root;
    resolve_node(&mut env, root);

    // TODO assert that we actually resolved all nodes.

    ResolvedTrace {
        info: query.info.clone(),
        tables: env.tables,
        resolved_goals: env.nodes,
        query: qa.clone(),
    }
}
