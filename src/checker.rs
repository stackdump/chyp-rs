// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/checker.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026):
//   - translated to Rust, as a `Checker` that checks one part per `step()`
//     so callers can check a proof step by step; `check()` runs it to the end;
//   - where upstream raises (a proof with no theorem, an `apply` or `qed`
//     with no proof state, a top-level rewrite step whose sides have
//     different types), the part gets an error and is marked invalid and
//     checking continues;
//   - `next_rhs` (RHS synthesis for the editor) is not ported.

//! Checking proofs, one part at a time.

use crate::parts::{PartKind, Side, Status};
use crate::proofstate::{run_tactic, Goal, ProofState};
use crate::rule::Rule;
use crate::state::{ErrorEntry, State};

/// Walks a `State`'s parts in order, checking each.
#[derive(Debug, Clone, Default)]
pub struct Checker {
    pos: usize,
    current_proof_state: Option<ProofState>,
    current_theorem: Option<usize>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker::default()
    }

    /// Index of the next part `step` will check.
    pub fn position(&self) -> usize {
        self.pos
    }

    pub fn done(&self, state: &State) -> bool {
        self.pos >= state.parts.len()
    }

    /// Check the next part. Returns its index, or None when all are checked.
    pub fn step(&mut self, state: &mut State) -> Option<usize> {
        let i = self.pos;
        if i >= state.parts.len() {
            return None;
        }
        self.pos += 1;
        let kind = state.parts[i].kind;
        let line = state.parts[i].line;

        match kind {
            PartKind::Theorem => {
                state.parts[i].status = Status::Checking;
                self.current_theorem = Some(i);
            }

            PartKind::ProofStart => match self.current_theorem {
                Some(t) => {
                    let thm = &state.parts[t];
                    let formula = thm.rule.clone().expect("theorem has a formula");
                    let ps = ProofState::new(thm.sequence, vec![Goal { formula }]);
                    state.parts[i].status = Status::Valid;
                    state.parts[i].proof_state = Some(ps.clone());
                    self.current_proof_state = Some(ps);
                }
                None => {
                    // Upstream: RuntimeError('Got proof without theorem').
                    push_error(state, line, "Got proof without theorem");
                    state.parts[i].status = Status::Invalid;
                    self.current_proof_state = None;
                }
            },

            PartKind::ProofQed => match (self.current_theorem, &self.current_proof_state) {
                (Some(t), Some(cur)) => {
                    let ps = cur.snapshot(line as i64);
                    let st = if ps.goals.is_empty() { Status::Valid } else { Status::Invalid };
                    state.parts[i].proof_state = Some(ps);
                    state.parts[i].status = st;
                    state.parts[t].status = st;
                    self.current_theorem = None;
                    self.current_proof_state = None;
                }
                _ => {
                    // Upstream: RuntimeError('Get qed without theorem or proofstate').
                    push_error(state, line, "Got qed without theorem or proof state");
                    state.parts[i].status = Status::Invalid;
                    self.current_theorem = None;
                    self.current_proof_state = None;
                }
            },

            PartKind::ApplyTactic => match &self.current_proof_state {
                Some(cur) => {
                    let mut ps = cur.snapshot(line as i64);
                    let tactic = state.parts[i].tactic.clone();
                    let args = state.parts[i].tactic_args.clone();
                    let ok = run_tactic(&mut ps, &tactic, &args, &state.table);
                    flush(state, &mut ps);
                    state.parts[i].status = if ok { Status::Valid } else { Status::Invalid };
                    state.parts[i].proof_state = Some(ps.clone());
                    self.current_proof_state = Some(ps);
                }
                None => {
                    // Upstream: RuntimeError('Could not get ProofState for "apply"').
                    push_error(state, line, "Could not get proof state for \"apply\"");
                    state.parts[i].status = Status::Invalid;
                }
            },

            PartKind::Rewrite => self.rewrite(state, i),

            PartKind::Gen | PartKind::Let | PartKind::Rule => {}
        }
        Some(i)
    }

    fn rewrite(&mut self, state: &mut State, i: usize) {
        let line = state.parts[i].line;
        let in_proof = self.current_proof_state.is_some();
        let mut proof_state: Option<ProofState> = None;

        if let Some(cur) = &self.current_proof_state {
            let mut ps = cur.snapshot(line as i64);
            if ps.num_goals() > 0 {
                let p = &mut state.parts[i];
                match p.rhs_side {
                    Some(Side::Lhs) => p.rhs = ps.lhs(),
                    Some(Side::Rhs) => p.rhs = ps.rhs(),
                    None => {}
                }
                match p.lhs_side {
                    Some(Side::Lhs) => {
                        p.lhs = ps.lhs();
                        if let Some(rhs) = p.rhs.clone() {
                            ps.replace_lhs(&rhs);
                        }
                    }
                    Some(Side::Rhs) => {
                        p.lhs = ps.rhs();
                        if let Some(rhs) = p.rhs.clone() {
                            ps.replace_rhs(&rhs);
                        }
                    }
                    None => {}
                }
            }
            proof_state = Some(ps);
        } else if let Some(lhs) = state.parts[i].lhs.clone() {
            let rhs = match state.parts[i].rhs.clone() {
                Some(r) => r,
                None => {
                    state.parts[i].rhs = Some(lhs.clone());
                    lhs.clone()
                }
            };
            match Rule::new(lhs, rhs, "") {
                Ok(formula) => {
                    let mut ps = ProofState::new(state.parts[i].sequence, vec![Goal { formula }]);
                    ps.line = line as i64;
                    proof_state = Some(ps);
                }
                Err(e) => {
                    // Upstream raises RuleError out of check() here.
                    push_error(state, line, &e.0);
                }
            }
        }

        let Some(mut ps) = proof_state else {
            state.parts[i].status = Status::Invalid;
            return;
        };

        let tactic = state.parts[i].tactic.clone();
        let args = state.parts[i].tactic_args.clone();
        state.parts[i].status = Status::Checking;
        let num_goals = ps.num_goals();
        let status = if run_tactic(&mut ps, &tactic, &args, &state.table) {
            if ps.num_goals() < num_goals {
                ps.try_close_goal(0);
                Status::Valid
            } else {
                Status::Invalid
            }
        } else {
            Status::Invalid
        };
        flush(state, &mut ps);
        state.parts[i].status = status;
        state.parts[i].proof_state = Some(ps.clone());
        if in_proof {
            self.current_proof_state = Some(ps);
        }
    }
}

fn push_error(state: &mut State, line: usize, msg: &str) {
    state.errors.push(ErrorEntry { line: line as i64, msg: msg.to_string() });
}

/// Move a proof state's errors into the theory's error list.
fn flush(state: &mut State, ps: &mut ProofState) {
    for (line, msg) in ps.errors.drain(..) {
        state.errors.push(ErrorEntry { line, msg });
    }
}

/// Check every part of `state`.
pub fn check(state: &mut State) {
    let mut c = Checker::new();
    while c.step(state).is_some() {}
}
