//! Resolving all contextual type information (de Bruijn indices, etc...).

use std::borrow::BorrowMut;

use argus::{
    proof_tree::{fulfill::FulfillmentKind, navigation::NavRooted, ProofTree},
    utils::InferenceTableExt,
};
use chalk_ir::{zip::Zip, UniverseIndex};

use super::{utils::*, *};
use crate::{
    infer::unify::{ChalkInferenceTable, InferenceTable},
    CanonicalVarKind, ProgramClauseImplication, Substitution,
};

fn expect_unify<T: ?Sized + Zip<Interner>>(table: &mut InferenceTable<'_>, t1: &T, t2: &T) {
    table.try_unify(t1, t2).unwrap_or_else(|e| {
        panic!("Couldn't unify:\n\t{t1:?}\n\t{t2:?}\n\n{e:?}");
    });
}

pub(crate) fn resolve_bindings(table: &mut InferenceTable<'_>, query: &TracedTraitQuery) {
    let AttemptKind::Required(qas) = &query.kind else {
        todo!();
    };

    // Find query attempt with the deepest failure (HACK: actually analyze these).
    let Some((qa, path)) = qas.into_iter().fold(None, |acc, qa| {
        let Some(new_path) = qa.trace.find_lowest_failure() else {
            return acc;
        };

        let Some((_, old_path)) = &acc else {
            return Some((qa, new_path));
        };

        if old_path.len() < new_path.len() {
            Some((qa, new_path))
        } else {
            acc
        }
    }) else {
        panic!();
    };

    eprintln!("\n------------ TRACING -------------");
    eprintln!("RA GOAL: {:?}\n", table.resolve_completely(query.ra_goal.clone()));
    eprintln!("         {:?}\n", query.ra_goal.clone());
    eprintln!("▶");

    let trace = &qa.trace;

    use crate::{Goal, InEnvironment};
    use chalk_ir::cast::Cast;

    let mut prev: InEnvironment<Goal> = query.ra_goal.clone().cast(Interner);
    let mut prev_clause_subst: Option<Substitution> = None;
    let mut last_infer: Option<ChalkInferenceTable> = None;

    for node in path.path.iter() {
        eprintln!("> {prev:?}");
        eprintln!("> {prev_clause_subst:?}\n");

        match &trace.nodes[*node] {
            ProofTree::FromClauses(value) => {
                eprintln!("[FromClauses] {:?}", value.goal().clone());
                eprintln!("              {:?}", {
                    let canonical = value.goal().canonical.clone();
                    let goal = table.instantiate_canonical(canonical).cast(Interner);

                    eprintln!(
                        "              Unifying\n                {prev:?}\n                {goal:?}"
                    );
                    // expect_unify(&mut table, &prev, &goal);
                    prev = goal;
                    &prev
                });
            }

            ProofTree::Fulfill(value) => match value.goal() {
                FulfillmentKind::WithClause { goal, clause } => {
                    let mut tbl = value.infer.0.clone();

                    let pci = table.instantiate_binders_existentially(Interner, clause.clone());
                    let (pc, binders) = clause.clone().into_value_and_skipped_binders();
                    let clause_subst = table.fresh_subst(
                        &binders
                            .iter(Interner)
                            .cloned()
                            .map(|pk| CanonicalVarKind::new(pk, UniverseIndex::root()))
                            .collect::<Vec<_>>(),
                    );

                    let canonicalized = tbl.canonicalize(Interner, goal.clone());

                    eprintln!("[UsingClause] {:?}", goal.clone());
                    eprintln!("              {:?}", clause);
                    eprintln!("              {:?}", pci);
                    eprintln!("              {:?}", {
                        let instantiated =
                            clause_subst.apply(canonicalized.quantified.value, Interner);

                        expect_unify(table, &prev, &instantiated.clone().cast(Interner));
                        expect_unify(table, &prev.goal, &pci.consequence.clone().cast(Interner));

                        prev = instantiated.cast(Interner);
                        prev_clause_subst = Some(clause_subst);
                        &prev
                    });

                    last_infer = Some(tbl);
                }

                FulfillmentKind::WithSimplification { goal, .. } => {
                    eprintln!("[Using Simpl] {:?}", {
                        // TODO
                        todo!()
                    });
                }
            },

            ProofTree::Obligation(value) => {
                eprintln!(
                    "[Obligation {:?}] {:?}",
                    value.obligation.kind,
                    value.obligation.goal.clone()
                );
                eprintln!("                   {:?}", {
                    let mut infer = last_infer.clone().unwrap();
                    let canonicalized = infer.canonicalize(Interner, value.obligation.goal.clone());
                    let clause_subst = prev_clause_subst.clone().unwrap();
                    let instantiated =
                        clause_subst.apply(canonicalized.quantified.value, Interner).cast(Interner);
                    prev = instantiated;
                    &prev
                });
            }

            ProofTree::Leaf(leaf) => {
                eprintln!("🏁 {:?}", leaf);
            }
        }

        print!("\n");
    }

    eprintln!("-----------------------------------");
}
