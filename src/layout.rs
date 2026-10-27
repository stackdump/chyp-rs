// Ported in part from Chyp (https://github.com/akissinger/chyp), commit
// 3d28483: `layer_decomp` from chyp/term.py and the initial coordinates of
// `convex_layout` from chyp/layout.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026):
//   - translated to Rust; sets are iterated in increasing id order, so the
//     result is deterministic (upstream iterates Python sets);
//   - the cvxpy refinement of y-coordinates is replaced by a deterministic
//     heuristic with no solver: alternating barycentric sweeps between
//     neighbouring columns, each followed by an isotonic projection that
//     enforces upstream's ordering and spacing constraints;
//   - term printing (`graph_to_term` and friends) is not ported.

//! A simple deterministic layered layout for string diagrams.
//!
//! Columns, left to right: the inputs, one column per edge layer, the
//! outputs. Within a column, items keep their order; consecutive boundary
//! vertices are at least 1 apart, consecutive boxes at least
//! (size1 + size2) / 2 apart (a box's size is 1 if it has at most one input
//! and one output, otherwise 2). A box's ports sit at y + offset, offsets
//! spread evenly over [-0.5, 0.5].

use std::collections::{BTreeMap, BTreeSet};

use crate::graph::Graph;

/// Upstream's `EData.box_size`.
pub fn box_size(g: &Graph, e: usize) -> usize {
    let ed = g.edge_data(e);
    if ed.s.len() <= 1 && ed.t.len() <= 1 {
        1
    } else {
        2
    }
}

/// Port offset of the j-th of n ports: 0 for a single port, else evenly
/// spread over [-0.5, 0.5].
pub fn port_offset(j: usize, n: usize) -> f64 {
    if n <= 1 {
        0.0
    } else {
        j as f64 / (n - 1) as f64 - 0.5
    }
}

/// Sort the edges of `g` into layers so every edge's sources are produced by
/// an earlier layer (or are inputs). Identity edges (labelled "id") are
/// inserted into `g` so that every wire crosses exactly one column boundary;
/// their ids are returned in the second component.
pub fn layer_decomp(g: &mut Graph) -> Result<(Vec<Vec<usize>>, BTreeSet<usize>), String> {
    let mut e_layers: Vec<Vec<usize>> = Vec::new();
    let mut v_layer: Vec<usize> = Vec::new();
    let mut v_placed: BTreeSet<usize> = BTreeSet::new();
    let mut inserted: BTreeSet<usize> = BTreeSet::new();

    // Inputs are placed; an input that is also an output gets an id edge.
    let outputs: BTreeSet<usize> = g.outputs().iter().copied().collect();
    for v in g.inputs().to_vec() {
        if outputs.contains(&v) {
            inserted.insert(g.insert_id_after(v, false));
        }
        v_layer.push(v);
        v_placed.insert(v);
    }

    let mut new_ids: BTreeSet<usize> = BTreeSet::new();
    let mut edges: BTreeSet<usize> = g.edges().collect();

    while !edges.is_empty() {
        let mut ready: BTreeSet<usize> =
            edges.iter().copied().filter(|&e| g.source(e).iter().all(|v| v_placed.contains(v))).collect();
        let outputs: BTreeSet<usize> = g.outputs().iter().copied().collect();
        for &v in &v_layer {
            if outputs.contains(&v) || g.out_edges(v).iter().any(|e| !ready.contains(e)) {
                let id = g.insert_id_after(v, false);
                new_ids.insert(id);
                inserted.insert(id);
                ready.insert(id);
            }
        }
        let e_layer: Vec<usize> = ready.iter().copied().collect();
        for e in &e_layer {
            edges.remove(e);
        }
        if e_layer.iter().all(|e| new_ids.contains(e)) {
            return Err("Could not make progress. Is graph acyclic?".into());
        }
        if !edges.is_empty() {
            v_layer = Vec::new();
            for &e in &e_layer {
                for &v in g.target(e) {
                    v_placed.insert(v);
                    v_layer.push(v);
                }
            }
        }
        e_layers.push(e_layer);
    }

    // Reduce crossings: sort each layer by the mean position of its sources
    // (forward pass), then also of its targets, weighted double (backward).
    for it in 0..2 {
        let order: Vec<usize> = if it == 0 { (0..e_layers.len()).collect() } else { (0..e_layers.len()).rev().collect() };
        for j in order {
            let inp: Vec<usize> = if j > 0 {
                e_layers[j - 1].iter().flat_map(|&e| g.target(e).to_vec()).collect()
            } else {
                g.inputs().to_vec()
            };
            let inp_pos: BTreeMap<usize, f64> =
                inp.iter().enumerate().map(|(i, &v)| (v, i as f64 / inp.len() as f64)).collect();
            let outp_pos: Option<BTreeMap<usize, f64>> = if it != 0 {
                let outp: Vec<usize> = if j + 1 < e_layers.len() {
                    e_layers[j + 1].iter().flat_map(|&e| g.source(e).to_vec()).collect()
                } else {
                    g.outputs().to_vec()
                };
                Some(outp.iter().enumerate().map(|(i, &v)| (v, i as f64 / outp.len() as f64)).collect())
            } else {
                None
            };
            let mut e_pos: BTreeMap<usize, f64> = BTreeMap::new();
            for &e in &e_layers[j] {
                let src = g.source(e);
                let mut p = if src.is_empty() {
                    0.0
                } else {
                    src.iter().map(|v| inp_pos.get(v).copied().unwrap_or(0.0)).sum::<f64>() / src.len() as f64
                };
                if let Some(op) = &outp_pos {
                    let tgt = g.target(e);
                    if !tgt.is_empty() {
                        p += 2.0 * tgt.iter().map(|v| op.get(v).copied().unwrap_or(0.0)).sum::<f64>() / tgt.len() as f64;
                    }
                }
                e_pos.insert(e, p);
            }
            // Stable sort, as Python's list.sort.
            e_layers[j].sort_by(|a, b| e_pos[a].partial_cmp(&e_pos[b]).unwrap_or(std::cmp::Ordering::Equal));
        }
    }

    Ok((e_layers, inserted))
}

/// A laid-out diagram: the graph (with any identity edges the layout
/// inserted), its layers, and coordinates for every vertex and edge.
#[derive(Debug, Clone)]
pub struct Layout {
    pub graph: Graph,
    pub layers: Vec<Vec<usize>>,
    /// Identity edges inserted by the layout: draw them as plain wire.
    pub inserted: BTreeSet<usize>,
    pub vpos: BTreeMap<usize, (f64, f64)>,
    pub epos: BTreeMap<usize, (f64, f64)>,
}

impl Layout {
    /// y-coordinates of an edge's input ports, top to bottom.
    pub fn in_ports(&self, e: usize) -> Vec<f64> {
        let (_, y) = self.epos[&e];
        let n = self.graph.source(e).len();
        (0..n).map(|j| y + port_offset(j, n)).collect()
    }

    /// y-coordinates of an edge's output ports, top to bottom.
    pub fn out_ports(&self, e: usize) -> Vec<f64> {
        let (_, y) = self.epos[&e];
        let n = self.graph.target(e).len();
        (0..n).map(|j| y + port_offset(j, n)).collect()
    }

    /// (x_min, x_max, y_min, y_max) over vertices and edges.
    pub fn bounds(&self) -> (f64, f64, f64, f64) {
        let mut b = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
        let mut first = true;
        for &(x, y) in self.vpos.values().chain(self.epos.values()) {
            if first {
                b = (x, x, y, y);
                first = false;
            } else {
                b = (b.0.min(x), b.1.max(x), b.2.min(y), b.3.max(y));
            }
        }
        b
    }
}

/// One item of a column: a boundary vertex or a box.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Item {
    V(usize),
    E(usize),
}

/// Number of barycentric sweeps (each one left-to-right then right-to-left).
const SWEEPS: usize = 8;

/// Lay out `g` (which is not modified).
pub fn layout(g: &Graph) -> Layout {
    let mut g = g.clone();
    let (layers, inserted) = match layer_decomp(&mut g) {
        Ok(r) => r,
        // Graphs built from terms are acyclic; fall back to one box per layer.
        Err(_) => (g.edges().map(|e| vec![e]).collect(), BTreeSet::new()),
    };

    // Columns of items, and upstream's initial coordinates.
    let n_layers = layers.len();
    let mut cols: Vec<Vec<Item>> = Vec::with_capacity(n_layers + 2);
    cols.push(g.inputs().iter().map(|&v| Item::V(v)).collect());
    for l in &layers {
        cols.push(l.iter().map(|&e| Item::E(e)).collect());
    }
    cols.push(g.outputs().iter().map(|&v| Item::V(v)).collect());
    let x0 = -((n_layers + 1) as f64) * 1.5;
    let col_x = |c: usize| -> f64 {
        if c == 0 {
            x0 + 1.5
        } else if c == n_layers + 1 {
            x0 + 3.0 * (n_layers + 1) as f64 - 1.5
        } else {
            x0 + 3.0 * c as f64
        }
    };

    let mut y: Vec<Vec<f64>> = cols
        .iter()
        .enumerate()
        .map(|(c, items)| {
            let n = items.len() as f64;
            let step = if c == 0 || c == n_layers + 1 { 1.0 } else { 2.0 };
            (0..items.len()).map(|i| step * (i as f64 - (n - 1.0) / 2.0)).collect()
        })
        .collect();

    // Minimum gaps between consecutive items of each column.
    let gaps: Vec<Vec<f64>> = cols
        .iter()
        .map(|items| {
            items
                .windows(2)
                .map(|w| match (w[0], w[1]) {
                    (Item::E(a), Item::E(b)) => (box_size(&g, a) + box_size(&g, b)) as f64 * 0.5,
                    _ => 1.0,
                })
                .collect()
        })
        .collect();

    // Wires between adjacent columns: (left col, left item, left port offset,
    // right item, right port offset). Every vertex is one wire.
    let mut index: BTreeMap<(usize, bool, usize), (usize, usize)> = BTreeMap::new(); // (col, is_edge, id) -> (col, pos)
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            let key = match *it {
                Item::V(v) => (c, false, v),
                Item::E(e) => (c, true, e),
            };
            index.insert(key, (c, i));
        }
    }
    let edge_col: BTreeMap<usize, usize> =
        layers.iter().enumerate().flat_map(|(l, es)| es.iter().map(move |&e| (e, l + 1))).collect();
    let mut wires: Vec<(usize, usize, f64, usize, f64)> = Vec::new();
    for v in g.vertices() {
        // Left end: an input, or the edge that has v as a target.
        let left = if g.is_input(v) && g.in_edges(v).is_empty() {
            Some((0usize, index[&(0, false, v)].1, 0.0))
        } else {
            g.in_edges(v).iter().next().and_then(|&e| {
                let c = *edge_col.get(&e)?;
                let t = g.target(e);
                let j = t.iter().position(|&x| x == v)?;
                Some((c, index[&(c, true, e)].1, port_offset(j, t.len())))
            })
        };
        // Right end: the edge that has v as a source, or an output.
        let right = if let Some(&e) = g.out_edges(v).iter().next() {
            edge_col.get(&e).and_then(|&c| {
                let s = g.source(e);
                let j = s.iter().position(|&x| x == v)?;
                Some((c, index[&(c, true, e)].1, port_offset(j, s.len())))
            })
        } else if g.is_output(v) {
            let c = n_layers + 1;
            index.get(&(c, false, v)).map(|&(_, i)| (c, i, 0.0))
        } else {
            None
        };
        if let (Some((lc, li, lo)), Some((rc, ri, ro))) = (left, right) {
            if rc == lc + 1 {
                wires.push((lc, li, lo, ri, ro));
            }
        }
    }

    // Alternating sweeps: move each item towards the mean straight-wire
    // position given its neighbours in the previous (or next) column, then
    // restore order and spacing with the least squares change.
    for _ in 0..SWEEPS {
        for c in 1..cols.len() {
            relax(&mut y, &gaps, &wires, c, true);
        }
        for c in (0..cols.len().saturating_sub(1)).rev() {
            relax(&mut y, &gaps, &wires, c, false);
        }
    }

    // Centre vertically.
    let all: Vec<f64> = y.iter().flatten().copied().collect();
    if let (Some(lo), Some(hi)) =
        (all.iter().copied().reduce(f64::min), all.iter().copied().reduce(f64::max))
    {
        let shift = (lo + hi) * 0.5;
        for col in y.iter_mut() {
            for v in col.iter_mut() {
                *v -= shift;
            }
        }
    }

    let mut vpos: BTreeMap<usize, (f64, f64)> = BTreeMap::new();
    let mut epos: BTreeMap<usize, (f64, f64)> = BTreeMap::new();
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            match *it {
                Item::V(v) => {
                    vpos.insert(v, (col_x(c), y[c][i]));
                }
                Item::E(e) => {
                    epos.insert(e, (col_x(c), y[c][i]));
                }
            }
        }
    }
    // Interior vertices sit just right of the box they leave, at its port.
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            if let Item::E(e) = *it {
                let t = g.target(e).to_vec();
                for (j, &v) in t.iter().enumerate() {
                    if !g.is_boundary(v) {
                        vpos.insert(v, (col_x(c) + 0.7, y[c][i] + port_offset(j, t.len())));
                    }
                }
            }
        }
    }
    // Anything left (cannot happen for graphs built from terms).
    for v in g.vertices() {
        vpos.entry(v).or_insert((0.0, 0.0));
    }

    Layout { graph: g, layers, inserted, vpos, epos }
}

/// One relaxation of column `c` against its left (`forward`) or right
/// neighbour column.
fn relax(y: &mut [Vec<f64>], gaps: &[Vec<f64>], wires: &[(usize, usize, f64, usize, f64)], c: usize, forward: bool) {
    let n = y[c].len();
    if n == 0 {
        return;
    }
    let mut sum = vec![0.0f64; n];
    let mut cnt = vec![0usize; n];
    for &(lc, li, lo, ri, ro) in wires {
        if forward && lc + 1 == c {
            sum[ri] += y[lc][li] + lo - ro;
            cnt[ri] += 1;
        } else if !forward && lc == c {
            sum[li] += y[c + 1][ri] + ro - lo;
            cnt[li] += 1;
        }
    }
    let target: Vec<f64> = (0..n).map(|i| if cnt[i] > 0 { sum[i] / cnt[i] as f64 } else { y[c][i] }).collect();
    y[c] = project(&target, &gaps[c]);
}

/// The closest (least squares) y to `target` with y[i+1] - y[i] >= gap[i]:
/// pool-adjacent-violators on y[i] - (gap[0] + ... + gap[i-1]).
fn project(target: &[f64], gap: &[f64]) -> Vec<f64> {
    let n = target.len();
    let mut offset = vec![0.0f64; n];
    for i in 1..n {
        offset[i] = offset[i - 1] + gap[i - 1];
    }
    // Blocks of (sum, count).
    let mut blocks: Vec<(f64, usize)> = Vec::with_capacity(n);
    for i in 0..n {
        blocks.push((target[i] - offset[i], 1));
        while blocks.len() >= 2 {
            let (s2, c2) = blocks[blocks.len() - 1];
            let (s1, c1) = blocks[blocks.len() - 2];
            if s1 / c1 as f64 > s2 / c2 as f64 {
                blocks.pop();
                blocks.pop();
                blocks.push((s1 + s2, c1 + c2));
            } else {
                break;
            }
        }
    }
    let mut out = Vec::with_capacity(n);
    for (s, c) in blocks {
        let m = s / c as f64;
        for _ in 0..c {
            let i = out.len();
            out.push(m + offset[i]);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{gen, identity, perm};

    #[test]
    fn layers_and_inserted_wires() {
        let f = gen("f", 1, 1);
        let m = gen("m", 2, 1);
        // f * id ; m : the second input needs an id edge in the first layer.
        let g = f.par(&identity()).seq(&m).unwrap();
        let l = layout(&g);
        assert_eq!(l.layers.len(), 2);
        assert_eq!(l.inserted.len(), 1);
        let (fx, _) = l.epos[&0];
        let (mx, _) = l.epos[&1];
        assert!(fx < mx);
    }

    #[test]
    fn straight_chain_is_straight() {
        let f = gen("f", 1, 1);
        let g = f.seq(&f).unwrap().seq(&f).unwrap();
        let l = layout(&g);
        for (_, &(_, y)) in &l.epos {
            assert!(y.abs() < 1e-9);
        }
    }

    #[test]
    fn spacing_and_determinism() {
        let sw = perm(&[1, 0]).unwrap();
        let n = gen("n", 1, 2);
        let m = gen("m", 2, 1);
        let g = n.par(&n).seq(&identity().par(&sw).par(&identity())).unwrap().seq(&m.par(&m)).unwrap();
        let a = layout(&g);
        let b = layout(&g);
        assert_eq!(a.epos, b.epos);
        assert_eq!(a.vpos, b.vpos);
        for layer in &a.layers {
            for w in layer.windows(2) {
                let need = (box_size(&a.graph, w[0]) + box_size(&a.graph, w[1])) as f64 * 0.5;
                assert!(a.epos[&w[1]].1 - a.epos[&w[0]].1 >= need - 1e-9);
            }
        }
    }

    #[test]
    fn projection() {
        let y = project(&[0.0, 0.0, 0.0], &[1.0, 1.0]);
        assert_eq!(y, vec![-1.0, 0.0, 1.0]);
        let y = project(&[0.0, 5.0], &[1.0]);
        assert_eq!(y, vec![0.0, 5.0]);
    }
}
