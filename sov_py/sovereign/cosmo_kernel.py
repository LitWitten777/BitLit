"""
sovereign_cosmo_kernel.py
=========================
Combinatorial Cosmohedron, Matryoshka Poset, Devadoss Bracket Associahedra,
Submodular Energy Poles, and Flat-Space Wavefunction Single-Pole Extraction.

Mathematical Foundations:
- Arkani-Hamed, Figueiredo, Vazão (JHEP 11 (2025) 029): "Cosmohedra"
- Ardila-Mantilla, Figueiredo, Arkani-Hamed, Vazão (arXiv:2603.03425): "Combinatorics of the cosmohedron"
- Devadoss (2009): "A realization of graph associahedra"
- Postnikov (2009): "Permutohedra, associahedra, and beyond"

Architecture:
1. PolygonGeometry: Representation of convex (n+2)-gons, chords, subdivisions, and dual trees.
2. MatryoshkaPoset: Generation of all Matryoshkas and bracketed trees with exact face counts.
3. DevadossBracketAssociahedron: Poset tree(B) and exact vertex coordinates b_B.
4. SubmodularEnergyPoles: delta_P = delta * (N - #P)^2, submodularity verification, facet inequalities.
5. CosmoCanonicalForm: Facet singularity pairs 1/X_C, permuto-cosmohedron blowup, and double-pole cancellation.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple
from collections import defaultdict
import numpy as np


# ===========================================================================
# 1. Polygon Geometry & Subdivisions
# ===========================================================================

Chord = Tuple[int, int]
Polygon = Tuple[int, ...]


class PolygonGeometry:
    """Methods for convex polygon chords, non-crossing sets, and subdivisions."""

    @staticmethod
    def get_all_chords(n_vertices: int) -> List[Chord]:
        """Returns all internal chords (i, j) of an N-gon, with i < j."""
        chords = []
        for i in range(n_vertices):
            for j in range(i + 2, n_vertices):
                if not (i == 0 and j == n_vertices - 1):
                    chords.append((i, j))
        return chords

    @staticmethod
    def chords_cross(c1: Chord, c2: Chord) -> bool:
        """Returns True if chords c1 and c2 cross in the interior of the polygon."""
        i, j = min(c1), max(c1)
        k, l = min(c2), max(c2)
        return (i < k < j < l) or (k < i < l < j)

    @classmethod
    def get_all_subdivisions(cls, n_vertices: int) -> List[Tuple[Chord, ...]]:
        """
        Returns all non-crossing sets of chords (subdivisions) of an N-gon,
        including the empty set (trivial subdivision).
        """
        chords = cls.get_all_chords(n_vertices)
        subdivisions = [()]
        max_chords = n_vertices - 3  # A full triangulation has N - 3 chords
        for k in range(1, max_chords + 1):
            for combo in itertools.combinations(chords, k):
                crossing = False
                for a in range(len(combo)):
                    for b in range(a + 1, len(combo)):
                        if cls.chords_cross(combo[a], combo[b]):
                            crossing = True
                            break
                    if crossing:
                        break
                if not crossing:
                    subdivisions.append(combo)
        return subdivisions

    @staticmethod
    def split_polygon(poly: Polygon, chord: Chord) -> List[Polygon]:
        """Splits a convex polygon along an internal chord (u, v)."""
        u, v = chord
        if u not in poly or v not in poly:
            return [poly]
        p = poly.index(u)
        q = poly.index(v)
        if p > q:
            p, q = q, p
        # Check non-consecutive in cycle
        if (q - p == 1) or (p == 0 and q == len(poly) - 1):
            return [poly]
        p1 = poly[p : q + 1]
        p2 = poly[q:] + poly[: p + 1]
        return [p1, p2]

    @classmethod
    def get_subpolygons(cls, n_vertices: int, chords: Tuple[Chord, ...]) -> List[Polygon]:
        """Returns the canonical subpolygons created by cutting along chords."""
        polys = [tuple(range(n_vertices))]
        for c in chords:
            new_polys = []
            for poly in polys:
                splits = cls.split_polygon(poly, c)
                new_polys.extend(splits)
            polys = new_polys

        # Canonical rotation: start at min vertex
        canon_polys = []
        for poly in polys:
            min_i = min(range(len(poly)), key=lambda k: poly[k])
            c_poly = poly[min_i:] + poly[:min_i]
            canon_polys.append(c_poly)
        return canon_polys

    @classmethod
    def build_dual_tree(
        cls, n_vertices: int, chords: Tuple[Chord, ...]
    ) -> Tuple[List[Polygon], List[Tuple[int, int, Chord]]]:
        """
        Constructs the dual tree T(S) for a subdivision.
        Returns:
            polys: list of subpolygons (vertices of T(S))
            edges: list of (poly_idx_a, poly_idx_b, shared_chord)
        """
        polys = cls.get_subpolygons(n_vertices, chords)
        k = len(polys)
        if k == 1:
            return polys, []

        edges = []
        for a in range(k):
            for b in range(a + 1, k):
                pa = polys[a]
                pb = polys[b]
                edges_a = {
                    tuple(sorted((pa[i], pa[(i + 1) % len(pa)])))
                    for i in range(len(pa))
                }
                edges_b = {
                    tuple(sorted((pb[i], pb[(i + 1) % len(pb)])))
                    for i in range(len(pb))
                }
                shared = edges_a & edges_b
                if shared:
                    chord = list(shared)[0]
                    edges.append((a, b, chord))
        return polys, edges


# ===========================================================================
# 2. Matryoshka Poset & Combinatorial Cosmohedron
# ===========================================================================

@dataclass(frozen=True)
class Matryoshka:
    """
    A Matryoshka (Russian doll) on an (n+2)-gon.
    Represented by:
        chords: the non-crossing chords defining the underlying subdivision S = M_min
        polygons: the full set of subpolygons in M (both minimal and non-minimal)
    """
    n_vertices: int
    chords: Tuple[Chord, ...]
    polygons: FrozenSet[Polygon]

    @property
    def minimal_polygons(self) -> List[Polygon]:
        return PolygonGeometry.get_subpolygons(self.n_vertices, self.chords)

    @property
    def non_minimal_polygons(self) -> List[Polygon]:
        min_set = set(self.minimal_polygons)
        return [p for p in self.polygons if p not in min_set]

    @property
    def codim(self) -> int:
        """Codimension in the cosmohedron = number of non-minimal polygons."""
        return len(self.non_minimal_polygons)

    def is_valid_matryoshka(self) -> bool:
        """
        Verifies the strict Matryoshka condition:
        For any non-minimal polygon X in M, the maximal subpolygons (M_{<X})_max
        of X that are in M must subdivide X.
        """
        for X in self.polygons:
            strictly_contained = [Y for Y in self.polygons if set(Y) < set(X)]
            if not strictly_contained:
                continue  # X is minimal in M
            # Find maximal elements among strictly_contained
            max_sub = []
            for Y in strictly_contained:
                is_max = True
                for Z in strictly_contained:
                    if set(Y) < set(Z):
                        is_max = False
                        break
                if is_max:
                    max_sub.append(Y)

            # Check that max_sub subdivides X:
            # 1. Total triangle count must sum to len(X) - 2
            total_triangles = sum(len(Y) - 2 for Y in max_sub)
            if total_triangles != len(X) - 2:
                return False
            # 2. Pairwise disjoint interiors (cannot share >= 3 vertices)
            for i in range(len(max_sub)):
                for j in range(i + 1, len(max_sub)):
                    if len(set(max_sub[i]) & set(max_sub[j])) > 2:
                        return False
        return True


class MatryoshkaEngine:
    """Generates all Matryoshkas and verifies the cosmohedron face lattice."""

    @classmethod
    def generate_bracketings(
        cls, k_polys: int, edges: List[Tuple[int, int, Chord]]
    ) -> List[FrozenSet[int]]:
        """
        Generates all valid bracketings B of a tree T.
        Each bracketing is a set of connected edge-subsets containing the full tree,
        such that any two brackets are either nested or vertex-disjoint.
        """
        E = len(edges)
        if E == 0:
            return [frozenset()]

        adj: Dict[int, List[Tuple[int, int]]] = {i: [] for i in range(k_polys)}
        for e_idx, (u, v, _) in enumerate(edges):
            adj[u].append((v, e_idx))
            adj[v].append((u, e_idx))

        def is_connected(edge_set: Tuple[int, ...]) -> bool:
            if not edge_set:
                return False
            verts = set()
            sub_adj: Dict[int, List[int]] = {v: [] for v in range(k_polys)}
            for e_idx in edge_set:
                u, v, _ = edges[e_idx]
                verts.add(u)
                verts.add(v)
                sub_adj[u].append(v)
                sub_adj[v].append(u)
            start = next(iter(verts))
            visited = set()
            stack = [start]
            while stack:
                curr = stack.pop()
                if curr not in visited:
                    visited.add(curr)
                    for nxt in sub_adj[curr]:
                        if nxt not in visited:
                            stack.append(nxt)
            return visited == verts

        # All connected edge-brackets
        all_brackets = []
        bracket_verts = {}
        for sz in range(1, E + 1):
            for combo in itertools.combinations(range(E), sz):
                if is_connected(combo):
                    fs = frozenset(combo)
                    all_brackets.append(fs)
                    b_verts = set()
                    for e_idx in combo:
                        b_verts.add(edges[e_idx][0])
                        b_verts.add(edges[e_idx][1])
                    bracket_verts[fs] = b_verts

        full_bracket = frozenset(range(E))

        def compatible(b1: FrozenSet[int], b2: FrozenSet[int]) -> bool:
            if b1 <= b2 or b2 <= b1:
                return True
            return len(bracket_verts[b1] & bracket_verts[b2]) == 0

        other_brackets = [b for b in all_brackets if b != full_bracket]
        valid_bracketings: List[FrozenSet[FrozenSet[int]]] = []

        def search(idx: int, current: Set[FrozenSet[int]]) -> None:
            valid_bracketings.append(frozenset(current | {full_bracket}))
            for i in range(idx, len(other_brackets)):
                b = other_brackets[i]
                if all(compatible(b, c) for c in current):
                    search(i + 1, current | {b})

        search(0, set())
        return valid_bracketings

    @classmethod
    def generate_all_matryoshkas(cls, n_vertices: int) -> List[Matryoshka]:
        """
        Generates all Matryoshkas on an (n+2)-gon.
        Uses the bijection with bracketed trees (T_M, B_M).
        """
        subdivisions = PolygonGeometry.get_all_subdivisions(n_vertices)
        full_polygon = tuple(range(n_vertices))
        all_m: List[Matryoshka] = []

        for chords in subdivisions:
            polys, edges = PolygonGeometry.build_dual_tree(n_vertices, chords)
            if not edges:
                # Trivial subdivision: only the full polygon
                all_m.append(
                    Matryoshka(
                        n_vertices=n_vertices,
                        chords=chords,
                        polygons=frozenset([full_polygon]),
                    )
                )
                continue

            bracketings = cls.generate_bracketings(len(polys), edges)
            for B in bracketings:
                # Each bracket in B defines a merged subpolygon
                poly_set = set(polys)
                for bracket in B:
                    # Find vertices in this bracket
                    bracket_polys = set()
                    for e_idx in bracket:
                        bracket_polys.add(edges[e_idx][0])
                        bracket_polys.add(edges[e_idx][1])
                    # Union of polygon vertices
                    union_verts = set()
                    for p_idx in bracket_polys:
                        union_verts.update(polys[p_idx])
                    # Order cyclically
                    sorted_verts = tuple(sorted(union_verts))
                    poly_set.add(sorted_verts)

                m = Matryoshka(
                    n_vertices=n_vertices,
                    chords=chords,
                    polygons=frozenset(poly_set),
                )
                all_m.append(m)

        return all_m

    @classmethod
    def get_face_vector(cls, n_vertices: int) -> Dict[int, int]:
        """
        Returns the f-vector of the (n-1)-cosmohedron for an (n+2)-gon.
        f[d] = number of d-codimensional faces.
        """
        matryoshkas = cls.generate_all_matryoshkas(n_vertices)
        f_vec: Dict[int, int] = defaultdict(int)
        for m in matryoshkas:
            f_vec[m.codim] += 1
        return dict(sorted(f_vec.items()))


# ===========================================================================
# 3. Devadoss Bracket Associahedron Coordinates
# ===========================================================================

class DevadossBracketAssociahedron:
    """
    Computes exact vertex coordinates for the Devadoss bracket associahedron
    BrAssoc(T) for a tree T and maximal bracketing B.
    """

    @staticmethod
    def canonical_concave_b(bracket_size: int) -> float:
        """
        A strictly concave function on bracket sizes:
        b(k) = sqrt(k), so 2*b(2) = 2.828 > b(1) + b(3) = 2.732.
        """
        return math.sqrt(bracket_size)

    @classmethod
    def compute_tree_poset(
        cls, edges: List[Tuple[int, int, Chord]], B: FrozenSet[FrozenSet[int]]
    ) -> Dict[int, FrozenSet[int]]:
        """
        Computes bracket_B(e) for each edge e:
        The unique smallest bracket in B containing e.
        """
        E = len(edges)
        bracket_e = {}
        for e in range(E):
            containing = [b for b in B if e in b]
            # Smallest by size
            smallest = min(containing, key=len)
            bracket_e[e] = smallest
        return bracket_e

    @classmethod
    def compute_covering_relations(
        cls, edges: List[Tuple[int, int, Chord]], bracket_e: Dict[int, FrozenSet[int]]
    ) -> Dict[int, List[int]]:
        """
        Computes the covering relations f < e in tree(B):
        bracket_B(f) < bracket_B(e) with no intervening bracket.
        """
        E = len(edges)
        covered_by: Dict[int, List[int]] = {e: [] for e in range(E)}
        for f in range(E):
            bf = bracket_e[f]
            # Parents of f in the poset
            parents = [e for e in range(E) if bf < bracket_e[e]]
            if parents:
                # Immediate parent has minimum bracket size
                min_sz = min(len(bracket_e[p]) for p in parents)
                immediate_parents = [p for p in parents if len(bracket_e[p]) == min_sz]
                for p in immediate_parents:
                    covered_by[p].append(f)
        return covered_by

    @classmethod
    def compute_vertex_coordinates(
        cls,
        edges: List[Tuple[int, int, Chord]],
        B: FrozenSet[FrozenSet[int]],
        b_func=None,
    ) -> np.ndarray:
        """
        Computes Devadoss vertex coordinates (b_B)_e via Lemma 4.5:
            (b_B)_e = b(bracket_B(e)) - sum_{f < e} b(bracket_B(f))
        """
        if b_func is None:
            b_func = cls.canonical_concave_b

        E = len(edges)
        bracket_e = cls.compute_tree_poset(edges, B)
        covers = cls.compute_covering_relations(edges, bracket_e)

        coords = np.zeros(E, dtype=np.float64)
        for e in range(E):
            val = b_func(len(bracket_e[e]))
            for f in covers[e]:
                val -= b_func(len(bracket_e[f]))
            coords[e] = val
        return coords


# ===========================================================================
# 4. Facet Inequalities & Submodular Energy Poles
# ===========================================================================

class SubmodularEnergyPoles:
    """
    Submodular energy pole assignments delta_P and cosmohedral facet inequalities.
    """

    @staticmethod
    def delta_P(poly: Polygon, total_vertices: int, delta: float = 1.0) -> float:
        """
        Convex scaling function:
            delta_P = delta * (N - #P)^2 for P != P_full
            delta_full = 0
        """
        if len(poly) >= total_vertices:
            return 0.0
        return delta * (total_vertices - len(poly)) ** 2

    @classmethod
    def verify_strict_submodularity(
        cls, total_vertices: int, delta: float = 1.0
    ) -> Dict[str, Any]:
        """
        Verifies that for any two subpolygons P, P' of the N-gon:
            delta_P + delta_P' <= delta_{P union P'} + delta_{P cap P'}
        with strict inequality when P and P' cross or intersect non-trivially.
        """
        all_chords = PolygonGeometry.get_all_chords(total_vertices)
        # Collect all valid subpolygons
        subpolys = [tuple(range(total_vertices))]
        for c in all_chords:
            splits = PolygonGeometry.split_polygon(tuple(range(total_vertices)), c)
            for s in splits:
                if s not in subpolys:
                    subpolys.append(s)

        tested_pairs = 0
        strictly_submodular = 0

        for i in range(len(subpolys)):
            for j in range(i + 1, len(subpolys)):
                p1 = set(subpolys[i])
                p2 = set(subpolys[j])
                cap = p1 & p2
                cup = p1 | p2

                if len(cap) >= 3 and len(cup) <= total_vertices:
                    tested_pairs += 1
                    d1 = cls.delta_P(subpolys[i], total_vertices, delta)
                    d2 = cls.delta_P(subpolys[j], total_vertices, delta)
                    d_cap = cls.delta_P(tuple(sorted(cap)), total_vertices, delta)
                    d_cup = cls.delta_P(tuple(sorted(cup)), total_vertices, delta)

                    lhs = d1 + d2
                    rhs = d_cap + d_cup
                    assert lhs <= rhs + 1e-9, f"Submodularity failed: {lhs} > {rhs}"
                    if lhs < rhs - 1e-9:
                        strictly_submodular += 1

        return {
            "total_vertices": total_vertices,
            "pairs_tested": tested_pairs,
            "strictly_submodular_pairs": strictly_submodular,
            "all_submodular_valid": True,
        }

    @classmethod
    def get_facet_inequality(
        cls, n_vertices: int, chords: Tuple[Chord, ...], delta: float = 1.0
    ) -> Dict[str, Any]:
        """
        Computes the cosmohedral facet inequality:
            sum_{c in C} X_c >= sum_{P in S(C)} delta_P
        """
        polys = PolygonGeometry.get_subpolygons(n_vertices, chords)
        rhs = sum(cls.delta_P(p, n_vertices, delta) for p in polys)
        return {
            "chords": chords,
            "subpolygons": polys,
            "rhs_bound": rhs,
            "formula": f"sum_{{c in {chords}}} X_c >= {rhs:.4f}",
        }


# ===========================================================================
# 5. Canonical Form & Single-Pole Extraction
# ===========================================================================

@dataclass(frozen=True)
class PoleProduct:
    """Represents a product of poles: prod_{P} (1 / P_P^{power})."""
    poles: Tuple[Tuple[str, int], ...]

    @property
    def is_single_pole(self) -> bool:
        """True iff every pole has degree exactly 1."""
        return all(pwr == 1 for _, pwr in self.poles)

    def multiply(self, other: PoleProduct) -> PoleProduct:
        d = dict(self.poles)
        for p, pwr in other.poles:
            d[p] = d.get(p, 0) + pwr
        return PoleProduct(tuple(sorted(d.items())))


class RationalPoleForm:
    """Linear combination of PoleProducts."""

    def __init__(self, terms: Optional[Dict[PoleProduct, float]] = None):
        self.terms: Dict[PoleProduct, float] = terms.copy() if terms else {}

    def multiply(self, other: RationalPoleForm) -> RationalPoleForm:
        new_terms: Dict[PoleProduct, float] = defaultdict(float)
        for t1, c1 in self.terms.items():
            for t2, c2 in other.terms.items():
                t = t1.multiply(t2)
                new_terms[t] += c1 * c2
        return RationalPoleForm(dict(new_terms))

    def extract_single_poles(self) -> RationalPoleForm:
        """Extracts only the terms where all poles have power == 1."""
        filtered = {t: c for t, c in self.terms.items() if t.is_single_pole}
        return RationalPoleForm(filtered)

    def __repr__(self) -> str:
        parts = []
        for t, c in sorted(self.terms.items(), key=lambda x: str(x[0])):
            factors = " * ".join(f"1/{p}^{pwr}" if pwr > 1 else f"1/{p}" for p, pwr in t.poles)
            parts.append(f"{c:+.4f} * ({factors})")
        return "\n  ".join(parts) if parts else "0"


class CosmoCanonicalForm:
    """
    Computes the canonical form on the permuto-cosmohedron blowup
    and executes single-pole extraction to cancel spurious double poles.
    """

    @staticmethod
    def facet_factor_1_over_X(
        n_vertices: int, chords: Tuple[Chord, ...]
    ) -> RationalPoleForm:
        """
        Implements eq. (8.2):
            1/X_C = (1 / n_C) * sum_{P, P' meeting on chord} (1 / (P_P * P_P'))
        where n_C is the number of non-triangle subpolygons in S(C).
        """
        polys, edges = PolygonGeometry.build_dual_tree(n_vertices, chords)
        non_triangles = [p for p in polys if len(p) > 3]
        n_C = max(1, len(non_triangles))

        terms: Dict[PoleProduct, float] = defaultdict(float)
        for u, v, _ in edges:
            name_u = "P_" + "".join(str(x) for x in polys[u])
            name_v = "P_" + "".join(str(x) for x in polys[v])
            pole_pair = PoleProduct(tuple(sorted([(name_u, 1), (name_v, 1)])))
            terms[pole_pair] += 1.0 / n_C
        return RationalPoleForm(dict(terms))

    @classmethod
    def verify_5point_single_pole_cancellation(cls) -> Dict[str, Any]:
        """
        Verifies single-pole extraction for 5-point (pentagon -> decagon).
        Two facets meeting at a vertex:
            C_triang = {(0,2), (0,3)}
            C_single = {(0,2)}
        Shows double poles cancel/vanish, leaving pure single-pole Russian doll.
        """
        N = 5
        inv_X_triang = cls.facet_factor_1_over_X(N, ((0, 2), (0, 3)))
        inv_X_single = cls.facet_factor_1_over_X(N, ((0, 2),))

        vertex_product = inv_X_triang.multiply(inv_X_single)
        single_pole_part = vertex_product.extract_single_poles()

        # The single pole part must have exactly 1 term with coefficient 1.0
        assert len(single_pole_part.terms) == 1
        term, coeff = list(single_pole_part.terms.items())[0]
        assert abs(coeff - 1.0) < 1e-9
        assert term.is_single_pole

        # Expected poles: P_012, P_023, P_034, P_0234
        expected_poles = {"P_012", "P_023", "P_034", "P_0234"}
        actual_poles = {p for p, _ in term.poles}
        assert actual_poles == expected_poles

        return {
            "vertex": "{(0,2), (0,3)} x {(0,2)}",
            "full_terms": len(vertex_product.terms),
            "single_pole_terms": len(single_pole_part.terms),
            "coefficient": coeff,
            "poles": sorted(actual_poles),
            "double_poles_eliminated": len(vertex_product.terms) - len(single_pole_part.terms),
            "success": True,
        }

    @classmethod
    def verify_6point_blown_up_vertex_cancellation(cls) -> Dict[str, Any]:
        """
        Verifies the blown-up non-simple vertex at 6-points (hexagon, Section 8.2):
            Facet C1: {(1, 4)}   (splits into two quads, n_C = 2)
            Facet C2: {(1, 3), (1, 4)}
            Facet C3: {(1, 4), (1, 5)}
            Facet C4: {(1, 3), (1, 4), (1, 5)}
        Vertex A: C1, C2, C4
        Vertex B: C1, C3, C4
        Each gives coefficient 0.5; sum = 1.0 exactly.
        All spurious double poles vanish!
        """
        N = 6
        # Shift to 1-indexed (1..6) mapping for exact correspondence with paper
        # Hexagon vertices 0..5 map to 1..6
        inv_C1 = cls.facet_factor_1_over_X(N, ((0, 3),))            # (1, 4)
        inv_C2 = cls.facet_factor_1_over_X(N, ((0, 2), (0, 3)))      # (1, 3), (1, 4)
        inv_C3 = cls.facet_factor_1_over_X(N, ((0, 3), (0, 4)))      # (1, 4), (1, 5)
        inv_C4 = cls.facet_factor_1_over_X(N, ((0, 2), (0, 3), (0, 4)))  # (1,3),(1,4),(1,5)

        # Vertex A
        vert_A = inv_C1.multiply(inv_C2).multiply(inv_C4)
        single_A = vert_A.extract_single_poles()

        # Vertex B
        vert_B = inv_C1.multiply(inv_C3).multiply(inv_C4)
        single_B = vert_B.extract_single_poles()

        # Sum vertices
        combined = RationalPoleForm()
        for t, c in single_A.terms.items():
            combined.terms[t] = combined.terms.get(t, 0.0) + c
        for t, c in single_B.terms.items():
            combined.terms[t] = combined.terms.get(t, 0.0) + c

        assert len(single_A.terms) == 1
        assert len(single_B.terms) == 1
        coeff_A = list(single_A.terms.values())[0]
        coeff_B = list(single_B.terms.values())[0]
        assert abs(coeff_A - 0.5) < 1e-9
        assert abs(coeff_B - 0.5) < 1e-9

        term_tot, coeff_tot = list(combined.terms.items())[0]
        assert abs(coeff_tot - 1.0) < 1e-9
        assert term_tot.is_single_pole

        return {
            "vertex_A_coeff": coeff_A,
            "vertex_B_coeff": coeff_B,
            "combined_coeff": coeff_tot,
            "poles": sorted([p for p, _ in term_tot.poles]),
            "double_poles_eliminated_A": len(vert_A.terms) - len(single_A.terms),
            "double_poles_eliminated_B": len(vert_B.terms) - len(single_B.terms),
            "success": True,
        }


# ===========================================================================
# 6. Self-Contained Verification Function
# ===========================================================================

def verify_all() -> Dict[str, Any]:
    """
    Executes all verification suites:
    1. Chords, non-crossing sets, and subdivision counts.
    2. Matryoshka counts and face vectors matching Table 1 for n=2, 3, 4.
    3. Matryoshka nesting condition on all generated Matryoshkas.
    4. Devadoss bracket associahedron coordinates and facet bounds.
    5. Strict submodularity of delta_P for N=4, 5, 6.
    6. Single-pole extraction and double-pole cancellation for n=3 and n=4.
    """
    results: Dict[str, Any] = {}

    # 1. Subdivisions
    subdiv_counts = {N: len(PolygonGeometry.get_all_subdivisions(N)) for N in [4, 5, 6]}
    assert subdiv_counts == {4: 3, 5: 11, 6: 45}
    results["subdivisions"] = subdiv_counts

    # 2. Face vectors (Table 1)
    f_vec_4 = MatryoshkaEngine.get_face_vector(4)  # n=2: [1, 2]
    f_vec_5 = MatryoshkaEngine.get_face_vector(5)  # n=3: [1, 10, 10]
    f_vec_6 = MatryoshkaEngine.get_face_vector(6)  # n=4: [1, 44, 114, 72]

    assert f_vec_4 == {0: 1, 1: 2}
    assert f_vec_5 == {0: 1, 1: 10, 2: 10}
    assert f_vec_6 == {0: 1, 1: 44, 2: 114, 3: 72}

    results["face_vectors"] = {
        "N=4 (n=2, quadrilateral)": f_vec_4,
        "N=5 (n=3, pentagon)": f_vec_5,
        "N=6 (n=4, hexagon)": f_vec_6,
    }

    # 3. Matryoshka nesting conditions
    for N in [4, 5, 6]:
        matryoshkas = MatryoshkaEngine.generate_all_matryoshkas(N)
        for m in matryoshkas:
            assert m.is_valid_matryoshka(), f"Matryoshka validation failed for {m}"
    results["matryoshka_nesting_valid"] = True

    # 4. Devadoss coordinates
    # Triangulation of pentagon: 2 edges
    _, edges_5 = PolygonGeometry.build_dual_tree(5, ((0, 2), (0, 3)))
    brs_5 = MatryoshkaEngine.generate_bracketings(3, edges_5)
    max_brs_5 = [b for b in brs_5 if len(b) == 2]
    for b in max_brs_5:
        coords = DevadossBracketAssociahedron.compute_vertex_coordinates(edges_5, b)
        # Sum of coords must equal b(H) = sqrt(2)
        assert abs(np.sum(coords) - math.sqrt(2.0)) < 1e-9
    results["devadoss_coordinates_valid"] = True

    # 5. Submodularity
    submod_res = {}
    for N in [4, 5, 6]:
        submod_res[N] = SubmodularEnergyPoles.verify_strict_submodularity(N)
    results["submodularity"] = submod_res

    # 6. Single-pole cancellation
    res_5pt = CosmoCanonicalForm.verify_5point_single_pole_cancellation()
    res_6pt = CosmoCanonicalForm.verify_6point_blown_up_vertex_cancellation()
    results["canonical_form_5point"] = res_5pt
    results["canonical_form_6point"] = res_6pt

    return results


if __name__ == "__main__":
    import json
    print("=" * 80)
    print("SOVEREIGN COSMO KERNEL: VERIFICATION SUITE")
    print("=" * 80)
    res = verify_all()
    print(json.dumps(res, indent=2))
    print("\n[PASS] All Cosmohedron & Matryoshka Invariants Kernel-Verified!")

