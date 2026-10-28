// chyp-rs: a Rust port of part of Chyp.
//
// Derived from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// files chyp/state.py and chyp/parser.py (its `parse()`), by Aleks Kissinger
// and the Chyp contributors.
//
// chyp/state.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// chyp/parser.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// Modified by the chyp-rs contributors, 2026. Changes from the original:
//   - translated to Rust as a walk over the parser's AST instead of a Lark
//     Transformer, in the same order (each statement bottom-up, left to
//     right), so errors and parts come out in upstream's order;
//   - a `;` chain's type errors are found by replaying upstream's
//     right-to-left compositions on the arities alone, and its graph is then
//     built left to right in linear time (the same vertices and edges in the
//     same order); `*` chains likewise;
//   - `State::parse` also does what chyp/parser.py's `parse()` does: line
//     endings are normalised as Python's universal newlines do when upstream
//     reads a file, and a syntax error gives one error entry and no parts.
//     `parsed` is false after a syntax error (upstream sets it to True in
//     every case); errors are (line, message) without the file name;
//   - not ported: imports and namespaces, colours, typed and sized wires and
//     redistributers, one-way rules, converse rewrites, `?` holes, the
//     `proofs` map, `current_part`, `copy_state_until`, and the editor's
//     revision tracking and `part_at` lookups.

//! A parsed theory: its terms, rules, parts and errors.

use std::collections::BTreeMap;

use crate::graph::{gen, identity, perm, type_repr, Graph};
use crate::parser::{self, Hole, ProofStep, RewriteStep, SideTok, Stmt, Term};
use crate::parts::{Part, PartKind, Side, Status};
use crate::proofstate::RuleTable;
use crate::rule::Rule;

/// An error reported against a source line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorEntry {
    pub line: i64,
    pub msg: String,
}

/// Everything known about a theory file after parsing (and, once
/// `checker::check` has run, checking).
#[derive(Debug, Clone, Default)]
pub struct State {
    pub sequence: usize,
    pub graphs: BTreeMap<String, Graph>,
    pub table: RuleTable,
    pub parts: Vec<Part>,
    pub errors: Vec<ErrorEntry>,
    /// False if the source had a syntax error (then there are no parts).
    pub parsed: bool,
}

fn side(s: SideTok) -> Side {
    match s {
        SideTok::Lhs => Side::Lhs,
        SideTok::Rhs => Side::Rhs,
    }
}

/// The right-hand side of a step once built: a graph, a side, or nothing
/// (the term failed to build).
enum Built {
    Graph(Graph),
    Side(Side),
    Missing,
}

/// `a * b * c` means `a * (b * c)`; the product is associative on the nose
/// (the same vertices and edges in the same order either way), so it is built
/// left to right, in linear time. Upstream raises no errors here.
fn par_chain(gs: Vec<Option<Graph>>) -> Option<Graph> {
    if gs.iter().any(Option::is_none) {
        return None;
    }
    let mut gs = gs.into_iter().flatten();
    let mut acc = gs.next()?;
    for g in gs {
        acc.tensor(&g);
    }
    Some(acc)
}

impl State {
    fn error(&mut self, line: usize, msg: String) {
        self.errors.push(ErrorEntry { line: line as i64, msg });
    }

    fn add_part(&mut self, mut p: Part) {
        p.index = self.parts.len();
        self.parts.push(p);
    }

    /// Build a term's graph, reporting errors as upstream's transformer does:
    /// bottom-up, left to right. The walk uses an explicit stack, so deep
    /// nesting costs heap, not call stack.
    fn term(&mut self, root: &Term) -> Option<Graph> {
        enum Task<'a> {
            Visit(&'a Term),
            Combine(&'a Term),
        }
        let mut tasks = vec![Task::Visit(root)];
        let mut values: Vec<Option<Graph>> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(t) => match t {
                    Term::Seq(items) | Term::Par(items) => {
                        tasks.push(Task::Combine(t));
                        tasks.extend(items.iter().rev().map(Task::Visit));
                    }
                    Term::Nested(inner, _) => tasks.push(Task::Visit(inner)),
                    leaf => {
                        let g = self.leaf(leaf);
                        values.push(g);
                    }
                },
                Task::Combine(t) => {
                    let (Term::Seq(items) | Term::Par(items)) = t else {
                        unreachable!()
                    };
                    let gs = values.split_off(values.len() - items.len());
                    let g = match t {
                        Term::Seq(_) => self.seq_chain(items, gs),
                        _ => par_chain(gs),
                    };
                    values.push(g);
                }
            }
        }
        values.pop().flatten()
    }

    /// A term with no sub-terms.
    fn leaf(&mut self, t: &Term) -> Option<Graph> {
        match t {
            Term::Id(_) => Some(identity()),
            Term::Id0(_) => Some(Graph::new()),
            Term::Perm(idx, pos) => {
                let p = idx.clone().unwrap_or_else(|| vec![1, 0]);
                match perm(&p) {
                    Ok(g) => Some(g),
                    Err(e) => {
                        self.error(pos.line, e.0);
                        None
                    }
                }
            }
            Term::Ref(name, pos) => match self.graphs.get(name) {
                Some(g) => Some(g.clone()),
                None => {
                    self.error(pos.line, format!("Undefined term: {}", name));
                    None
                }
            },
            Term::Seq(_) | Term::Par(_) | Term::Nested(..) => unreachable!("not a leaf"),
        }
    }

    /// `a ; b ; c` means `a ; (b ; c)`: upstream composes from the right,
    /// each composition reporting a type error on the line where its left
    /// operand starts. That is replayed on the arities alone, so errors are
    /// upstream's; the graph is then built left to right, which gives the
    /// same vertices and edges in the same order (each composite keeps its
    /// left side's vertices and adds the right side's non-input vertices
    /// after them), in linear time.
    fn seq_chain(&mut self, items: &[Term], gs: Vec<Option<Graph>>) -> Option<Graph> {
        let mut acc_dom = gs.last().unwrap().as_ref().map(|g| g.domain());
        for (g, t) in gs[..gs.len() - 1].iter().zip(items).rev() {
            acc_dom = match (g, acc_dom) {
                (Some(g), Some(dom)) if g.codomain() == dom => Some(g.domain()),
                (Some(g), Some(dom)) => {
                    self.error(
                        t.pos().line,
                        format!(
                            "Codomain {} does not match domain {}",
                            type_repr(g.codomain()),
                            type_repr(dom)
                        ),
                    );
                    None
                }
                _ => None,
            };
        }
        acc_dom?;
        let mut gs = gs.into_iter().flatten();
        let mut acc = gs.next()?;
        for g in gs {
            acc.compose(&g).expect("arities checked above");
        }
        Some(acc)
    }

    fn step_rhs(&mut self, step: &RewriteStep) -> Built {
        match &step.hole {
            Hole::Term(t) => match self.term(t) {
                Some(g) => Built::Graph(g),
                None => Built::Missing,
            },
            Hole::Side(s) => Built::Side(side(*s)),
        }
    }

    fn tactic_of(step: &RewriteStep) -> (String, Vec<String>) {
        match &step.tactic {
            Some(t) => (t.name.clone(), t.args.clone()),
            None => ("refl".into(), Vec::new()),
        }
    }

    fn statement(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Gen { name, n_in, n_out, pos } => {
                let g = match self.graphs.get(name) {
                    None => {
                        let g = gen(name, *n_in, *n_out);
                        self.graphs.insert(name.clone(), g.clone());
                        g
                    }
                    Some(g) => {
                        let g = g.clone();
                        if g.domain() != *n_in || g.codomain() != *n_out {
                            self.error(
                                pos.line,
                                format!(
                                    "Term '{}' already defined with incompatible type {} -> {}.",
                                    name,
                                    type_repr(g.domain()),
                                    type_repr(g.codomain())
                                ),
                            );
                            self.error(
                                pos.line,
                                format!("(Trying to add) {} -> {}.", type_repr(*n_in), type_repr(*n_out)),
                            );
                        }
                        g
                    }
                };
                let mut p = Part::new(PartKind::Gen, pos.start, pos.end, pos.line, name);
                p.graph = Some(g);
                self.add_part(p);
            }

            Stmt::Let { name, term, pos } => {
                let graph = self.term(term);
                if !self.graphs.contains_key(name) {
                    if let Some(g) = &graph {
                        self.graphs.insert(name.clone(), g.clone());
                    }
                } else {
                    self.error(pos.line, format!("Term '{}' already defined.", name));
                }
                let mut p = Part::new(PartKind::Let, pos.start, pos.end, pos.line, name);
                p.graph = graph;
                self.add_part(p);
            }

            Stmt::Rule { name, lhs, rhs, pos } => {
                let lhs = self.term(lhs);
                let rhs = self.term(rhs);
                self.sequence += 1;
                if !self.table.rules.contains_key(name) {
                    if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
                        match Rule::new(lhs, rhs, name) {
                            Ok(rule) => {
                                self.table.rules.insert(name.clone(), rule.clone());
                                self.table.rule_sequence.insert(name.clone(), self.sequence);
                                self.add_rule_part(pos, rule);
                            }
                            Err(e) => self.error(pos.line, e.0),
                        }
                    }
                } else {
                    self.error(pos.line, format!("Rule '{}' already defined.", name));
                }
            }

            Stmt::Def { name, term, pos } => {
                let graph = self.term(term);
                self.sequence += 1;
                let rule_name = format!("{}_def", name);
                if self.table.rules.contains_key(&rule_name) {
                    self.error(pos.line, format!("Rule \"{}\" already defined.", rule_name));
                    return;
                }
                let Some(graph) = graph else { return };
                let (dom, cod) = (graph.domain(), graph.codomain());
                match self.graphs.get(name).cloned() {
                    None => {
                        let lhs = gen(name, dom, cod);
                        self.graphs.insert(name.clone(), lhs.clone());
                        let rule = Rule::new(lhs, graph, &rule_name).expect("same boundary");
                        self.table.rules.insert(rule_name.clone(), rule.clone());
                        self.table.rule_sequence.insert(rule_name, self.sequence);
                        self.add_rule_part(pos, rule);
                    }
                    Some(lhs) => {
                        if lhs.domain() == dom && lhs.codomain() == cod {
                            let rule = Rule::new(lhs, graph, &rule_name).expect("same boundary");
                            self.table.rules.insert(rule_name.clone(), rule.clone());
                            self.sequence += 1;
                            self.table.rule_sequence.insert(rule_name, self.sequence);
                            self.add_rule_part(pos, rule);
                        } else {
                            self.error(
                                pos.line,
                                format!(
                                    "Term \"{}\" already defined with incompatible type {} -> {}.",
                                    name,
                                    type_repr(dom),
                                    type_repr(cod)
                                ),
                            );
                        }
                    }
                }
            }

            Stmt::Show { name, name_pos, pos } => match self.table.rules.get(name).cloned() {
                Some(rule) => self.add_rule_part(pos, rule),
                None => self.error(name_pos.line, format!("Undefined rule: {}", name)),
            },

            Stmt::Rewrite { name, term, steps, pos } => self.rewrite(name, term, steps, pos),

            Stmt::Theorem {
                name,
                lhs,
                rhs,
                pos,
                proof,
            } => {
                let lhs = self.term(lhs);
                let rhs = self.term(rhs);
                self.sequence += 1;
                // Upstream builds Rule(None, ...) with an empty graph.
                match Rule::new(lhs.unwrap_or_default(), rhs.unwrap_or_default(), name) {
                    Ok(rule) => {
                        // Upstream records the sequence number but never adds
                        // the theorem to `rules` (see proofstate::lookup_rule).
                        self.table.rule_sequence.insert(name.clone(), self.sequence);
                        let mut p = Part::new(PartKind::Theorem, pos.start, pos.end, pos.line, name);
                        p.lhs = Some(rule.lhs.clone());
                        p.rhs = Some(rule.rhs.clone());
                        p.rule = Some(rule);
                        p.sequence = self.sequence;
                        self.add_part(p);
                    }
                    Err(e) => self.error(pos.line, e.0),
                }
                if let Some(proof) = proof {
                    self.proof(proof);
                }
            }
        }
    }

    fn add_rule_part(&mut self, pos: &parser::Pos, rule: Rule) {
        let mut p = Part::new(PartKind::Rule, pos.start, pos.end, pos.line, &rule.name);
        p.lhs = Some(rule.lhs.clone());
        p.rhs = Some(rule.rhs.clone());
        p.rule = Some(rule);
        self.add_part(p);
    }

    fn rewrite(&mut self, name: &str, term: &Term, steps: &[RewriteStep], pos: &parser::Pos) {
        let term = self.term(term);
        let built: Vec<Built> = steps.iter().map(|s| self.step_rhs(s)).collect();
        self.sequence += 1;

        if steps.is_empty() {
            // A stub: upstream gives it tactic '' (an unknown tactic).
            let mut p = Part::new(PartKind::Rewrite, pos.start, pos.end, pos.line, name);
            p.sequence = self.sequence;
            p.lhs = term;
            self.add_part(p);
            return;
        }

        let mut start = pos.start;
        let mut lhs = term.clone();
        let mut last: Option<&Built> = None;
        for (step, rhs) in steps.iter().zip(&built) {
            let end = step.pos.end.max(step.hole_pos.end);
            match rhs {
                Built::Side(_) => {
                    self.error(pos.line, "Cannot use LHS/RHS outside of proof.".into());
                }
                Built::Graph(_) | Built::Missing => {
                    let (tactic, args) = Self::tactic_of(step);
                    let rhs_g = match rhs {
                        Built::Graph(g) => Some(g.clone()),
                        _ => None,
                    };
                    let mut p = Part::new(PartKind::Rewrite, start, end, step.pos.line, name);
                    p.sequence = self.sequence;
                    p.term_pos = (step.hole_pos.start, step.hole_pos.end);
                    p.tactic = tactic;
                    p.tactic_args = args;
                    p.lhs = lhs.clone();
                    p.rhs = rhs_g.clone();
                    self.add_part(p);
                    lhs = rhs_g;
                }
            }
            start = end;
            last = Some(rhs);
        }

        if let (Some(term), Some(Built::Graph(rhs))) = (term, last) {
            if !self.table.rules.contains_key(name) {
                match Rule::new(term, rhs.clone(), name) {
                    Ok(rule) => {
                        self.table.rules.insert(name.to_string(), rule);
                        self.table.rule_sequence.insert(name.to_string(), self.sequence);
                    }
                    Err(e) => self.error(pos.line, e.0),
                }
            } else {
                self.error(pos.line, format!("Rule '{}' already defined.", name));
            }
        }
    }

    fn proof(&mut self, proof: &parser::Proof) {
        let mut p = Part::new(
            PartKind::ProofStart,
            proof.start.start,
            proof.start.end,
            proof.start.line,
            "",
        );
        p.sequence = self.sequence;
        self.add_part(p);

        for step in &proof.steps {
            match step {
                ProofStep::Apply { tactic, pos } => {
                    let mut p = Part::new(PartKind::ApplyTactic, pos.start, pos.end, pos.line, "");
                    p.sequence = self.sequence;
                    p.tactic = tactic.name.clone();
                    p.tactic_args = tactic.args.clone();
                    self.add_part(p);
                }
                ProofStep::Rewrite {
                    side: lhs_side,
                    steps,
                    pos,
                } => {
                    let built: Vec<Built> = steps.iter().map(|s| self.step_rhs(s)).collect();
                    let mut start = pos.start;
                    for (step, rhs) in steps.iter().zip(built) {
                        let end = step.pos.end.max(step.hole_pos.end);
                        let (tactic, args) = Self::tactic_of(step);
                        let mut p = Part::new(PartKind::Rewrite, start, end, step.pos.line, "");
                        p.sequence = self.sequence;
                        p.term_pos = (step.hole_pos.start, step.hole_pos.end);
                        p.lhs_side = Some(side(*lhs_side));
                        match rhs {
                            Built::Graph(g) => p.rhs = Some(g),
                            Built::Side(s) => p.rhs_side = Some(s),
                            Built::Missing => {}
                        }
                        p.tactic = tactic;
                        p.tactic_args = args;
                        self.add_part(p);
                        start = end;
                    }
                }
            }
        }

        let mut p = Part::new(PartKind::ProofQed, proof.end.start, proof.end.end, proof.end.line, "");
        p.sequence = self.sequence;
        self.add_part(p);
    }

    /// Parse a theory and build its graphs, rules and parts (not yet checked).
    /// Line endings are normalised first, as Python's universal newlines do
    /// when upstream reads a file: "\r\n" and a lone "\r" become "\n"
    /// (character offsets refer to the normalised text).
    pub fn parse(src: &str) -> State {
        let src = if src.contains('\r') {
            src.replace("\r\n", "\n").replace('\r', "\n")
        } else {
            src.to_string()
        };
        let mut st = State::default();
        match parser::parse(&src) {
            Ok(stmts) => {
                for s in &stmts {
                    st.statement(s);
                }
                st.parsed = true;
            }
            Err(e) => {
                st.errors.push(ErrorEntry {
                    line: e.line as i64,
                    msg: e.message,
                });
            }
        }
        st
    }

    /// Number of parts whose status is `s`.
    pub fn count(&self, s: Status) -> usize {
        self.parts.iter().filter(|p| p.status == s).count()
    }
}
