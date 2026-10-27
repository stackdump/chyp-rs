// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/rewrite.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026): translated to
// Rust; `dpo` returns the rewritten graph rather than a Match of the RHS into
// it (the embedding was only used for GUI highlighting), and its
// NotImplementedError cases are returned as errors.

//! Double-pushout (DPO) rewriting.

use std::collections::BTreeMap;

use crate::graph::Graph;
use crate::matcher::Match;
use crate::rule::Rule;

const FROBENIUS: &str = "Rewriting modulo Frobenius not yet supported.";

/// Rewrite `m.codomain` with rule `r` at match `m` (a match of `r.lhs`):
/// compute the pushout complement, then glue in `r.rhs`.
pub fn dpo(r: &Rule, m: &Match<'_>) -> Result<Graph, String> {
    // Vertices split apart for identity wires on the LHS.
    let mut in_map: BTreeMap<usize, usize> = BTreeMap::new();
    let mut out_map: BTreeMap<usize, usize> = BTreeMap::new();

    // Pushout complement.
    let mut ctx = m.codomain.clone();
    for e in r.lhs.edges() {
        ctx.remove_edge(m.edge(e).expect("dpo: match is not total"));
    }
    for v in r.lhs.vertices() {
        let v1 = m.vertex(v).expect("dpo: match is not total");
        if r.lhs.is_boundary(v) {
            let in_c = r.lhs.vertex_data(v).in_indices.len();
            let out_c = r.lhs.vertex_data(v).out_indices.len();
            if in_c == 1 && out_c == 1 {
                let (v1i, v1o) = ctx.explode_vertex(v1).map_err(|e| e.0)?;
                if v1i.len() == 1 && v1o.len() == 1 {
                    in_map.insert(v, v1i[0]);
                    out_map.insert(v, v1o[0]);
                } else {
                    return Err(FROBENIUS.into());
                }
            } else if in_c > 1 || out_c > 1 {
                return Err(FROBENIUS.into());
            }
        } else {
            ctx.remove_vertex(v1, false).map_err(|e| e.0)?;
        }
    }

    // The rewritten graph, and where r.rhs's vertices land in it.
    let mut h = ctx;
    let mut vmap: BTreeMap<usize, usize> = BTreeMap::new();

    // Inputs go where the LHS inputs went.
    for (&vl, &vr) in r.lhs.inputs().iter().zip(r.rhs.inputs()) {
        let img = in_map.get(&vl).copied().unwrap_or_else(|| m.vertex(vl).unwrap());
        vmap.insert(vr, img);
    }

    // Outputs likewise; a vertex that is both an input and an output of
    // r.rhs merges the two places in h.
    for (&vl, &vr) in r.lhs.outputs().iter().zip(r.rhs.outputs()) {
        let vr1 = out_map.get(&vl).copied().unwrap_or_else(|| m.vertex(vl).unwrap());
        match vmap.get(&vr) {
            Some(&existing) => h.merge_vertices(existing, vr1),
            None => {
                vmap.insert(vr, vr1);
            }
        }
    }

    // Fresh vertices for the interior of r.rhs.
    for v in r.rhs.vertices() {
        if !r.rhs.is_boundary(v) {
            let v1 = h.add_vertex();
            vmap.insert(v, v1);
        }
    }

    // Edges of r.rhs.
    for e in r.rhs.edges() {
        let ed = r.rhs.edge_data(e);
        let s = ed.s.iter().map(|v| vmap[v]).collect();
        let t = ed.t.iter().map(|v| vmap[v]).collect();
        h.add_edge(s, t, &ed.value);
    }

    Ok(h)
}
