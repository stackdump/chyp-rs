// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/matcher.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026):
//   - translated to Rust; `Matches` is a Rust `Iterator`;
//   - no vertex type/size checks (single-sorted graphs only);
//   - debug logging removed.
// The search order is kept: the match stack is a LIFO, `more()` extends a
// partial match in the same order, and the vertex/edge maps remember
// insertion order like Python dicts.

//! Matching a graph into another (convex matches for rewriting, and
//! isomorphism checking).

use std::collections::BTreeSet;

use crate::graph::Graph;
use crate::rule::Rule;

/// A partial or total map of `domain` into `codomain`.
#[derive(Debug, Clone)]
pub struct Match<'a> {
    pub domain: &'a Graph,
    pub codomain: &'a Graph,
    /// (domain vertex, codomain vertex) pairs in insertion order.
    pub vertex_map: Vec<(usize, usize)>,
    pub vertex_image: BTreeSet<usize>,
    /// (domain edge, codomain edge) pairs in insertion order.
    pub edge_map: Vec<(usize, usize)>,
    pub edge_image: BTreeSet<usize>,
}

fn lookup(map: &[(usize, usize)], k: usize) -> Option<usize> {
    map.iter().find(|(a, _)| *a == k).map(|(_, b)| *b)
}

impl<'a> Match<'a> {
    pub fn new(domain: &'a Graph, codomain: &'a Graph) -> Match<'a> {
        Match {
            domain,
            codomain,
            vertex_map: Vec::new(),
            vertex_image: BTreeSet::new(),
            edge_map: Vec::new(),
            edge_image: BTreeSet::new(),
        }
    }

    /// Image of a domain vertex, if mapped.
    pub fn vertex(&self, v: usize) -> Option<usize> {
        lookup(&self.vertex_map, v)
    }

    /// Image of a domain edge, if mapped.
    pub fn edge(&self, e: usize) -> Option<usize> {
        lookup(&self.edge_map, e)
    }

    /// Try to map `domain_vertex` to `codomain_vertex`. Matches may only be
    /// non-injective on boundary vertices, and interior vertices must keep
    /// their degree (the gluing conditions).
    pub fn try_add_vertex(&mut self, domain_vertex: usize, codomain_vertex: usize) -> bool {
        if let Some(img) = self.vertex(domain_vertex) {
            return img == codomain_vertex;
        }

        // Non-boundary domain vertices may not map to boundary codomain vertices.
        if self.codomain.is_boundary(codomain_vertex) && !self.domain.is_boundary(domain_vertex) {
            return false;
        }

        // Non-injectivity is only allowed between boundary vertices.
        if self.vertex_image.contains(&codomain_vertex) {
            if !self.domain.is_boundary(domain_vertex) {
                return false;
            }
            for &(mapped, image) in &self.vertex_map {
                if image == codomain_vertex && !self.domain.is_boundary(mapped) {
                    return false;
                }
            }
        }

        self.vertex_map.push((domain_vertex, codomain_vertex));
        self.vertex_image.insert(codomain_vertex);

        // Edges are mapped injectively, so equal degree on interior vertices
        // guarantees the gluing conditions.
        if !self.domain.is_boundary(domain_vertex) {
            if self.domain.in_edges(domain_vertex).len() != self.codomain.in_edges(codomain_vertex).len() {
                return false;
            }
            if self.domain.out_edges(domain_vertex).len() != self.codomain.out_edges(codomain_vertex).len() {
                return false;
            }
        }
        true
    }

    /// Try to map `domain_edge` to `codomain_edge`, extending the vertex map
    /// along its sources and targets.
    pub fn try_add_edge(&mut self, domain_edge: usize, codomain_edge: usize) -> bool {
        if self.domain.edge_data(domain_edge).value != self.codomain.edge_data(codomain_edge).value {
            return false;
        }
        if self.edge_image.contains(&codomain_edge) {
            return false;
        }
        self.edge_map.push((domain_edge, codomain_edge));
        self.edge_image.insert(codomain_edge);

        // As upstream, sources+targets are zipped pairwise (so a length
        // mismatch is truncated rather than rejected).
        let dom: Vec<usize> = self
            .domain
            .source(domain_edge)
            .iter()
            .chain(self.domain.target(domain_edge))
            .copied()
            .collect();
        let cod: Vec<usize> = self
            .codomain
            .source(codomain_edge)
            .iter()
            .chain(self.codomain.target(codomain_edge))
            .copied()
            .collect();
        for (dv, cv) in dom.into_iter().zip(cod) {
            match self.vertex(dv) {
                Some(img) if img != cv => return false,
                _ => {
                    if !self.try_add_vertex(dv, cv) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether every edge adjacent to a domain vertex is mapped.
    pub fn domain_neighbourhood_mapped(&self, vertex: usize) -> bool {
        self.domain.in_edges(vertex).iter().all(|&e| self.edge(e).is_some())
            && self.domain.out_edges(vertex).iter().all(|&e| self.edge(e).is_some())
    }

    /// Map every scalar (0 -> 0 edge) of the domain to a distinct scalar of
    /// the codomain with the same label, greedily. Any choice gives
    /// isomorphic rewrites, so only one is tried.
    pub fn map_scalars(&mut self) -> bool {
        let mut codomain_scalars: Vec<(usize, String)> = Vec::new();
        for e in self.codomain.edges() {
            let ed = self.codomain.edge_data(e);
            if ed.s.is_empty() && ed.t.is_empty() {
                codomain_scalars.push((e, ed.value.clone()));
            }
        }
        let domain_edges: Vec<usize> = self.domain.edges().collect();
        for e in domain_edges {
            let ed = self.domain.edge_data(e);
            if !ed.s.is_empty() || !ed.t.is_empty() {
                continue;
            }
            match codomain_scalars.iter().position(|(_, val)| *val == ed.value) {
                Some(i) => {
                    let (ce, _) = codomain_scalars.remove(i);
                    self.edge_map.push((e, ce));
                    self.edge_image.insert(ce);
                }
                None => return false,
            }
        }
        true
    }

    /// All matches extending this one by a single edge or vertex.
    pub fn more(&self) -> Vec<Match<'a>> {
        let mut extended = Vec::new();

        // First, try to map an edge adjacent to an already-mapped vertex.
        for &(domain_vertex, codomain_vertex) in &self.vertex_map {
            if self.domain_neighbourhood_mapped(domain_vertex) {
                continue;
            }
            for &edge in self.domain.in_edges(domain_vertex) {
                if self.edge(edge).is_some() {
                    continue;
                }
                for &codomain_edge in self.codomain.in_edges(codomain_vertex) {
                    let mut m = self.clone();
                    if m.try_add_edge(edge, codomain_edge) {
                        extended.push(m);
                    }
                }
                return extended;
            }
            for &edge in self.domain.out_edges(domain_vertex) {
                if self.edge(edge).is_some() {
                    continue;
                }
                for &codomain_edge in self.codomain.out_edges(codomain_vertex) {
                    let mut m = self.clone();
                    if m.try_add_edge(edge, codomain_edge) {
                        extended.push(m);
                    }
                }
                return extended;
            }
        }

        // Otherwise map the first unmapped domain vertex anywhere it fits.
        for domain_vertex in self.domain.vertices() {
            if self.vertex(domain_vertex).is_some() {
                continue;
            }
            for codomain_vertex in self.codomain.vertices() {
                let mut m = self.clone();
                if m.try_add_vertex(domain_vertex, codomain_vertex) {
                    extended.push(m);
                }
            }
            return extended;
        }

        Vec::new()
    }

    pub fn is_total(&self) -> bool {
        self.vertex_map.len() == self.domain.num_vertices() && self.edge_map.len() == self.domain.num_edges()
    }

    pub fn is_surjective(&self) -> bool {
        self.vertex_image.len() == self.codomain.num_vertices() && self.edge_image.len() == self.codomain.num_edges()
    }

    /// Edges are always mapped injectively, so this checks vertices.
    pub fn is_injective(&self) -> bool {
        self.vertex_map.len() == self.vertex_image.len()
    }

    /// Injective, and no directed path leads from the image of an output of
    /// the domain back to the image of one of its inputs.
    pub fn is_convex(&self) -> bool {
        if !self.is_injective() {
            return false;
        }
        let out_imgs: Vec<usize> = self.domain.outputs().iter().filter_map(|&v| self.vertex(v)).collect();
        let succ = self.codomain.successors(out_imgs);
        for &v in self.domain.inputs() {
            if let Some(img) = self.vertex(v) {
                if succ.contains(&img) {
                    return false;
                }
            }
        }
        true
    }
}

/// Iterator over the total (and, if `convex`, convex) matches of one graph
/// into another, by depth-first search over a stack of partial matches.
pub struct Matches<'a> {
    stack: Vec<Match<'a>>,
    convex: bool,
}

impl<'a> Matches<'a> {
    pub fn new(domain: &'a Graph, codomain: &'a Graph, initial: Option<Match<'a>>, convex: bool) -> Matches<'a> {
        let mut initial = initial.unwrap_or_else(|| Match::new(domain, codomain));
        let stack = if initial.map_scalars() { vec![initial] } else { Vec::new() };
        Matches { stack, convex }
    }
}

impl<'a> Iterator for Matches<'a> {
    type Item = Match<'a>;

    fn next(&mut self) -> Option<Match<'a>> {
        while let Some(m) = self.stack.pop() {
            if m.is_total() {
                if !self.convex || m.is_convex() {
                    return Some(m);
                }
            } else {
                self.stack.extend(m.more());
            }
        }
        None
    }
}

/// Matches of `domain` into `codomain`.
pub fn match_graph<'a>(domain: &'a Graph, codomain: &'a Graph, convex: bool) -> Matches<'a> {
    Matches::new(domain, codomain, None, convex)
}

/// Convex matches of a rule's left-hand side into `graph`.
pub fn match_rule<'a>(rule: &'a Rule, graph: &'a Graph) -> Matches<'a> {
    Matches::new(&rule.lhs, graph, None, true)
}

/// An isomorphism `domain` -> `codomain` that respects the boundary order, if
/// there is one.
pub fn find_iso<'a>(domain: &'a Graph, codomain: &'a Graph) -> Option<Match<'a>> {
    if domain.domain() != codomain.domain() || domain.codomain() != codomain.codomain() {
        return None;
    }
    let mut initial = Match::new(domain, codomain);
    for (&d, &c) in domain.inputs().iter().zip(codomain.inputs()) {
        if !initial.try_add_vertex(d, c) {
            return None;
        }
    }
    for (&d, &c) in domain.outputs().iter().zip(codomain.outputs()) {
        if !initial.try_add_vertex(d, c) {
            return None;
        }
    }
    Matches::new(domain, codomain, Some(initial), false).find(|m| m.is_surjective())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{gen, identity, perm};

    #[test]
    fn iso_respects_boundary_order() {
        let f = gen("f", 1, 1);
        let g = gen("g", 1, 1);
        let a = f.par(&identity()).seq(&identity().par(&g)).unwrap();
        let b = identity().par(&g).seq(&f.par(&identity())).unwrap();
        assert!(find_iso(&a, &b).is_some());
        let c = identity().par(&f);
        assert!(find_iso(&f.par(&identity()), &c).is_none());
        let sw = perm(&[1, 0]).unwrap();
        assert!(find_iso(&sw.seq(&sw).unwrap(), &identity().par(&identity())).is_some());
    }

    #[test]
    fn counts_matches() {
        let f = gen("f", 1, 1);
        let ff = f.seq(&f).unwrap();
        let fff = ff.seq(&f).unwrap();
        assert_eq!(match_graph(&ff, &fff, true).count(), 2);
        assert_eq!(match_graph(&f, &fff, true).count(), 3);
    }
}
