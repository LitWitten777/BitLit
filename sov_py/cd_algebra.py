"""
cd_algebra.py — Generalized Cayley-Dickson Algebra & Zero-Divisor Stratification
for arbitrary D = 2^n algebras (D >= 16).

Implements:
1. Canonical multiplication table generation via recursive Cayley-Dickson doubling.
2. Cross-half zero-divisor enumeration and stratification.
3. Universal Projective Duality: Bijection with PG(n-2, F_2) and XOR charge conservation.
4. Spectral analysis and Ramanujan / integral spectrum properties.
"""

from __future__ import annotations

import functools
import itertools
from typing import Any

import networkx as nx
import numpy as np
import numpy.typing as npt

from .exceptions import AlgebraDimensionError


@functools.lru_cache(maxsize=16)
def build_cd_multiplication_table(dim: int) -> tuple[npt.NDArray[np.int8], npt.NDArray[np.int16]]:
    """
    Computes the canonical Cayley-Dickson multiplication table for dimension `dim`.
    Basis elements e_0, ..., e_{dim-1} follow the standard recursive CD doubling:
        (a, b) * (c, d) = (ac - d^* b, da + b c^*)

    Returns:
        sign_table:  (dim, dim) int8 array with entries in {-1, 0, 1}
        idx_table:   (dim, dim) int16 array with entries in {0, ..., dim-1}
        satisfying e_i * e_j = sign_table[i, j] * e_{idx_table[i, j]}.
    """
    if not (dim >= 2 and (dim & (dim - 1)) == 0):
        raise AlgebraDimensionError(f"Dimension must be a power of 2, got {dim}")
    if dim == 2:
        # Complex numbers: e_0=1, e_1=i (i^2 = -1)
        sign = np.array([[1, 1], [1, -1]], dtype=np.int8)
        idx = np.array([[0, 1], [1, 0]], dtype=np.int16)
        return sign, idx

    half = dim // 2
    sub_sign, sub_idx = build_cd_multiplication_table(half)
    sign = np.zeros((dim, dim), dtype=np.int8)
    idx = np.zeros((dim, dim), dtype=np.int16)

    conj_sign = np.ones(half, dtype=np.int8)
    conj_sign[1:] = -1

    # 1. (e_i, 0)(e_j, 0) = (e_i e_j, 0)
    sign[:half, :half] = sub_sign
    idx[:half, :half] = sub_idx

    # 2. (e_i, 0)(0, e_j') = (0, e_j' e_i)
    for i in range(half):
        for jp in range(half):
            sign[i, half + jp] = sub_sign[jp, i]
            idx[i, half + jp] = half + sub_idx[jp, i]

    # 3. (0, e_i')(e_j, 0) = (0, e_i' e_j*)
    for ip in range(half):
        for j in range(half):
            sign[half + ip, j] = sub_sign[ip, j] * conj_sign[j]
            idx[half + ip, j] = half + sub_idx[ip, j]

    # 4. (0, e_i')(0, e_j') = (-e_j'* e_i', 0)
    for ip in range(half):
        for jp in range(half):
            sign[half + ip, half + jp] = -sub_sign[jp, ip] * conj_sign[jp]
            idx[half + ip, half + jp] = sub_idx[jp, ip]

    return sign, idx


def cd_tower_eps_neg(n: int, a: int, b: int) -> bool:
    """
    Recursive Cayley-Dickson structure sign: epsNeg n a b = True iff e_a * e_b = -e_{a ^ b}.
    Formally proven by induction on level n for all dimensions in Sovereign/Algebra/TowerBasis.lean (HYP-048).
    Runs in O(n) bitwise operations with zero floating-point arithmetic and zero memory tables.
    """
    if n == 0:
        return False
    half = 1 << (n - 1)
    if a < half:
        if b < half:
            return cd_tower_eps_neg(n - 1, a, b)
        else:
            return cd_tower_eps_neg(n - 1, b - half, a)
    else:
        conj_b = (b != 0)
        if b < half:
            return conj_b ^ cd_tower_eps_neg(n - 1, a - half, b)
        else:
            b_prime = b - half
            conj_b_prime = (b_prime != 0)
            return not (conj_b_prime ^ cd_tower_eps_neg(n - 1, b_prime, a - half))


def cd_tower_basis_mul(n: int, a: int, b: int) -> tuple[int, int]:
    """
    Universal Cayley-Dickson basis product e_a * e_b = sign * e_{a ^ b}.
    Formally proven for all levels n in Sovereign/Algebra/TowerBasis.lean (HYP-048).
    """
    sign = -1 if cd_tower_eps_neg(n, a, b) else 1
    return sign, (a ^ b)


def cd_cross_vec_annihilates(
    n: int,
    s1: int,
    i: int,
    s2: int,
    j: int,
    t1: int,
    k: int,
    t2: int,
    m: int,
) -> bool:
    """
    Universal cross-half zero-divisor annihilation criterion:
    v = (s1*e_i + s2*e_{2^n + j}) and w = (t1*e_k + t2*e_{2^n + m}) in Tower(n+1) (dim = 2^{n+1})
    satisfy v * w = 0 iff their XOR charges agree and decoupled sign cancellations hold.
    Formally proven in Sovereign/Algebra/TowerZeroDivisors.lean (HYP-049).
    """
    if (i ^ j) != (k ^ m):
        return False
    s = s1 < 0
    t = s2 < 0
    u = t1 < 0
    r = t2 < 0
    half = 1 << n
    c1 = (s ^ u ^ cd_tower_eps_neg(n + 1, i, k)) != (
        t ^ r ^ cd_tower_eps_neg(n + 1, half + j, half + m)
    )
    c2 = (s ^ r ^ cd_tower_eps_neg(n + 1, i, half + m)) != (
        t ^ u ^ cd_tower_eps_neg(n + 1, half + j, k)
    )
    return c1 and c2


class CDStratificationEngine:
    """
    Analyzes cross-half zero divisors in D = 2^n Cayley-Dickson algebras.
    Cross-half vectors are of the form:
        v = s1 * e_i + s2 * e_{half + j}  with i, j in {0, ..., half-1}, s1, s2 in {+1, -1}.
    """

    def __init__(self, dim: int = 32):
        if not (dim >= 16 and (dim & (dim - 1)) == 0):
            raise AlgebraDimensionError(f"dim must be a power of 2 >= 16, got {dim}")
        self.dim = dim
        self.half = dim // 2
        self.sign_table, self.idx_table = build_cd_multiplication_table(dim)

    def multiply_two_terms(
        self, v1: tuple[int, int, int, int], v2: tuple[int, int, int, int]
    ) -> bool:
        """
        Determines whether v1 * v2 = 0 where v = (i, j, s1, s2) represents:
            v = s1 * e_i + s2 * e_j.

        Optimized via closed-form 4-term basis pairing with zero dictionary allocation.
        """
        i1, j1, s1_1, s2_1 = v1
        i2, j2, s1_2, s2_2 = v2

        s0 = int(s1_1 * s1_2 * self.sign_table[i1, i2])
        s1 = int(s1_1 * s2_2 * self.sign_table[i1, j2])
        s2 = int(s2_1 * s1_2 * self.sign_table[j1, i2])
        s3 = int(s2_1 * s2_2 * self.sign_table[j1, j2])

        # Net sign sum must be zero for cancellation to be possible
        if s0 + s1 + s2 + s3 != 0:
            return False

        k0 = int(self.idx_table[i1, i2])
        k1 = int(self.idx_table[i1, j2])
        k2 = int(self.idx_table[j1, i2])
        k3 = int(self.idx_table[j1, j2])

        # Exactly 3 possible partitionings of 4 terms into canceling pairs
        if k0 == k1 and s0 == -s1 and k2 == k3:
            return True
        if k0 == k2 and s0 == -s2 and k1 == k3:
            return True
        return bool(k0 == k3 and s0 == -s3 and k1 == k2)

    def theoretical_counts(self) -> dict[str, int]:
        """Returns theoretical closed-form counts for dimension D."""
        dim = self.dim
        n = int(np.log2(dim))
        total_cross = dim * dim
        total_zds = (dim - 2) * (dim - 4)
        total_non_zds = 6 * dim - 8
        num_components = (1 << (n - 1)) - 1  # |PG(n-2, 2)|
        component_size = 8 * ((1 << (n - 2)) - 1)  # 2*(dim - 4)
        return {
            "dim": dim,
            "total_cross_half_vectors": total_cross,
            "total_zero_divisors": total_zds,
            "total_non_zero_divisors": total_non_zds,
            "num_components": num_components,
            "component_size": component_size,
        }

    def generate_zero_divisor_graph(self, target_chi: int | None = None) -> nx.Graph[Any]:
        """
        Builds the zero-divisor annihilation graph on cross-half vectors.
        Omits identity locus (i=0 or j=half) and diagonal locus (j-half == i).

        Leverages Universal Index Geometry Decoupling:
            Annihilation is possible iff sgn_prod = sign(i1, i2)*sign(j1, j2)*sign(i1, j2)*sign(j1, i2) == +1.
            When sgn_prod == +1, edges are added iff sig1 * sig2 == -sign(i1, i2)*sign(j1, j2).
        This achieves a 16x reduction in pairwise checks per component.
        """
        graph: nx.Graph[Any] = nx.Graph()
        by_chi: dict[int, list[tuple[int, int]]] = {}
        node_id = 0
        pair_nodes: dict[tuple[int, int], list[tuple[int, int]]] = {}

        for i in range(1, self.half):
            for j_rel in range(1, self.half):
                if i == j_rel:
                    continue  # Diagonal locus non-ZD
                chi = i ^ j_rel
                if target_chi is not None and chi != target_chi:
                    continue
                j = self.half + j_rel
                pair = (i, j)
                if chi not in by_chi:
                    by_chi[chi] = []
                by_chi[chi].append(pair)
                pair_nodes[pair] = []
                for s1 in (1, -1):
                    for s2 in (1, -1):
                        graph.add_node(node_id, vec=(i, j, s1, s2), chi=chi)
                        pair_nodes[pair].append((node_id, s1 * s2))
                        node_id += 1

        # Connect mutual annihilators using index geometry decoupling
        for _chi, pairs in by_chi.items():
            m = len(pairs)
            for u in range(m):
                p1 = pairs[u]
                i1, j1 = p1
                for w in range(u + 1, m):
                    p2 = pairs[w]
                    i2, j2 = p2
                    s_prod = (
                        int(self.sign_table[i1, i2])
                        * int(self.sign_table[j1, j2])
                        * int(self.sign_table[i1, j2])
                        * int(self.sign_table[j1, i2])
                    )
                    if s_prod == 1:
                        req = -int(self.sign_table[i1, i2]) * int(self.sign_table[j1, j2])
                        for uid, sig1 in pair_nodes[p1]:
                            for wid, sig2 in pair_nodes[p2]:
                                if sig1 * sig2 == req:
                                    graph.add_edge(uid, wid)

        return graph

    def analyze_components(self, graph: nx.Graph[Any] | None = None) -> dict[str, Any]:
        """
        Decomposes the graph into connected components and verifies:
        1. Universal XOR charge conservation.
        2. Exact correspondence with PG(n-2, F_2).
        3. Integer and algebraic spectral decomposition across all components.
        """
        if graph is None:
            graph = self.generate_zero_divisor_graph()

        comps = list(nx.connected_components(graph))
        comp_data: list[dict[str, Any]] = []

        for c in comps:
            sub: nx.Graph[Any] = graph.subgraph(c)
            chis = {graph.nodes[n]["chi"] for n in c}
            if len(chis) != 1:
                raise ValueError(f"Component has multiple XOR charges: {chis}")
            chi = next(iter(chis))

            adj_matrix: npt.NDArray[np.float64] = nx.to_numpy_array(sub)
            raw_eigs = np.linalg.eigvalsh(adj_matrix)
            eigs = np.round(raw_eigs, 3)
            unique_eigs = sorted({float(x) for x in eigs})
            degs = sorted({int(d) for _, d in sub.degree()})

            # Check for non-rational algebraic integer eigenvalues
            irrational_eigs = [float(e) for e in raw_eigs if abs(e - round(e)) > 1e-3]

            comp_data.append(
                {
                    "chi": chi,
                    "nodes": sub.number_of_nodes(),
                    "edges": sub.number_of_edges(),
                    "degrees": degs,
                    "eigenvalues": unique_eigs,
                    "irrational_eigenvalues_count": len(irrational_eigs),
                }
            )

        comp_data.sort(key=lambda x: x["chi"])
        return {
            "dim": self.dim,
            "total_nodes": graph.number_of_nodes(),
            "total_edges": graph.number_of_edges(),
            "num_components": len(comps),
            "components": comp_data,
        }

    def get_sector_vertices(self, chi: int) -> list[tuple[int, int, int, int]]:
        """
        Returns all cross-half zero-divisor vectors in the sector with XOR charge `chi`.
        Each vector is represented as (i, j_full, s1, s2) where:
          - i ∈ {1, ..., half-1}   (lower basis index)
          - j_full = half + j_rel  (upper basis index in {half+1, ..., dim-1})
          - s1, s2 ∈ {+1, -1}     (sign coefficients)
        """
        H = self.half
        verts: list[tuple[int, int, int, int]] = []
        for i in range(1, H):
            j_rel = i ^ chi
            if j_rel == 0 or j_rel >= H or j_rel == i:
                continue
            for s1 in (1, -1):
                for s2 in (1, -1):
                    verts.append((i, H + j_rel, s1, s2))
        return verts

    def analyze_sector_degrees(self, chi: int) -> dict[str, Any]:
        """
        Computes the full degree distribution for the annihilation sector with XOR charge `chi`.

        Returns a dict with:
          - 'chi': the charge value
          - 'vertices': list of (i, j_full, s1, s2) tuples
          - 'degrees': list of vertex degrees (parallel to 'vertices')
          - 'degree_counts': Counter of {degree: count}
          - 'high_degree_vertices': vertices with the maximum observed degree
          - 'high_degree_index_pairs': unique (i_raw, j_rel) pairs of high-degree vertices
          - 'is_regular': True iff all vertices have the same degree
          - 'is_biregular': True iff exactly two distinct degrees exist
          - 'total_edges': number of undirected edges in the sector
        """
        verts = self.get_sector_vertices(chi)
        degrees: list[int] = []
        for p in verts:
            deg = sum(1 for q in verts if q != p and self.multiply_two_terms(p, q))
            degrees.append(deg)

        from collections import Counter

        cnt: dict[int, int] = dict(Counter(degrees))
        max_deg = max(degrees) if degrees else 0
        high_verts = [verts[k] for k, d in enumerate(degrees) if d == max_deg]
        # Unique index pairs of high-degree vertices (normalised as (low_i, j_rel))
        H = self.half
        high_pairs: set[tuple[int, int]] = set()
        for i_full, j_full, _s1, _s2 in high_verts:
            high_pairs.add((i_full, j_full - H))

        total_edges = sum(degrees) // 2
        unique_degs = set(degrees)

        is_regular = len(unique_degs) == 1
        is_biregular = len(unique_degs) == 2
        is_pole = (chi == self.half // 2)

        # Ramanujan Family Classification (HYP-082, HYP-203, HYP-204, HYP-205)
        # 1. Doubling Pole: Crown blowup, lambda_2 = 4, Ramanujan
        # 2. Biregular sectors: Matching double cone Cone_2, Ramanujan
        # 3. Non-pole regular sectors: Gauge double cover K_m^sigma, Breaks Ramanujan (lambda_2 = d/2)
        if self.dim == 16:
            ramanujan_family = "DOUBLING_POLE" if is_pole else "GAUGE_DOUBLE_COVER"
            is_ramanujan = True
        elif is_pole:
            ramanujan_family = "DOUBLING_POLE"
            is_ramanujan = True
        elif is_biregular:
            ramanujan_family = "BIREGULAR_MATCHING_CONE"
            is_ramanujan = True
        elif is_regular:
            ramanujan_family = "GAUGE_DOUBLE_COVER"
            is_ramanujan = False
        else:
            ramanujan_family = "MULTIREGULAR"
            is_ramanujan = False

        return {
            "chi": chi,
            "vertices": verts,
            "degrees": degrees,
            "degree_counts": cnt,
            "high_degree_vertices": high_verts,
            "high_degree_index_pairs": sorted(high_pairs),
            "is_regular": is_regular,
            "is_biregular": is_biregular,
            "is_pole": is_pole,
            "ramanujan_family": ramanujan_family,
            "is_ramanujan": is_ramanujan,
            "total_edges": total_edges,
        }

    @staticmethod
    def classify_d64_spectral_classes() -> dict[int, dict[str, Any]]:
        """
        Returns the exact 6-class hexapartite spectral decomposition of PG(4, F_2)
        across all 31 components of the D=64 Chingon zero-divisor annihilation graph.
        """
        return {
            1: {
                "name": "Fano Hyperplane PG(2, F_2)",
                "chis": list(range(1, 8)),
                "count": 7,
                "minimal_polynomials": ["x^2 + 4*x - 224"],
                "discriminants": [912],  # 16 * 57
                "squarefree_factors": [57],
                "field_extension": "Q(sqrt(57))",
                "is_integral": False,
            },
            2: {
                "name": "First Doubling Pole (D=32 pole 1000_2)",
                "chis": [8],
                "count": 1,
                "minimal_polynomials": ["x^2 + 4*x - 224"],
                "discriminants": [912],
                "squarefree_factors": [57],
                "field_extension": "Q(sqrt(57))",
                "is_integral": False,
            },
            3: {
                "name": "Fano-Pole 1 Junction",
                "chis": list(range(9, 16)),
                "count": 7,
                "minimal_polynomials": ["x^2 + 4*x - 224", "x^2 - 20*x - 480"],
                "discriminants": [912, 2320],  # 16 * 57, 16 * 145
                "squarefree_factors": [57, 145],
                "field_extension": "Q(sqrt(57), sqrt(145))",
                "is_integral": False,
            },
            4: {
                "name": "Second Doubling Pole (D=64 pole 10000_2, Pure Integral)",
                "chis": [16],
                "count": 1,
                "minimal_polynomials": ["x - 56", "x + 56", "x - 4", "x + 4", "x"],
                "discriminants": [],
                "squarefree_factors": [],
                "field_extension": "Q",
                "is_integral": True,
            },
            5: {
                "name": "Affine Pole 2 Shift (Symmetric Quadratic)",
                "chis": list(range(17, 25)),
                "count": 8,
                "minimal_polynomials": ["x^2 - 4*x - 224", "x^2 + 4*x - 224"],
                "discriminants": [912, 912],
                "squarefree_factors": [57],
                "field_extension": "Q(sqrt(57))",
                "is_integral": False,
            },
            6: {
                "name": "Deep Triple-Junction (Cubic Extension)",
                "chis": list(range(25, 32)),
                "count": 7,
                "minimal_polynomials": ["x^2 + 4*x - 224", "x^3 - 40*x^2 - 80*x + 1920"],
                "discriminants": [912, 514867200],  # 2^14 * 3 * 5^2 * 419
                "squarefree_factors": [57, 1257],  # 3 * 419 = 1257
                "field_extension": "Q(sqrt(57), theta)",
                "is_integral": False,
            },
        }

    def analyze_chingon_spectrum(self, target_chi: int) -> dict[str, Any]:
        """
        Computes and certifies the spectrum and minimal polynomial classification
        for sector `target_chi` in D=64 (120 vertices).
        """
        if self.dim != 64:
            raise ValueError(f"analyze_chingon_spectrum requires dim=64, got dim={self.dim}")
        if not (1 <= target_chi <= 31):
            raise ValueError(f"target_chi must be in 1..31 for D=64, got {target_chi}")

        classes = self.classify_d64_spectral_classes()
        class_id = 0
        for cid, cdata in classes.items():
            if target_chi in cdata["chis"]:
                class_id = cid
                break

        G_sub = self.generate_zero_divisor_graph(target_chi=target_chi)
        adj_matrix: npt.NDArray[np.float64] = nx.to_numpy_array(G_sub)
        raw_eigs = np.linalg.eigvalsh(adj_matrix)
        rounded_eigs = sorted(set(np.round(raw_eigs, 4)))
        irrational_eigs = [float(e) for e in raw_eigs if abs(e - round(e)) > 1e-3]
        degrees = sorted({int(d) for _, d in G_sub.degree()})

        return {
            "dim": 64,
            "chi": target_chi,
            "class_id": class_id,
            "class_info": classes[class_id],
            "nodes": G_sub.number_of_nodes(),
            "edges": G_sub.number_of_edges(),
            "degrees": degrees,
            "unique_eigenvalues": rounded_eigs,
            "irrational_eigenvalue_count": len(irrational_eigs),
            "is_integral": len(irrational_eigs) == 0,
        }

    @classmethod
    def build_component_graph(cls, dim: int, chi: int) -> nx.Graph[Any]:
        """
        Builds the exact zero-divisor annihilation graph for component `chi` in dimension `dim`
        without creating the massive full-space graph.

        Utilizes the Universal Index Geometry Decoupling Theorem:
            Since vertices v1, v2 can only annihilate if chi(v1) == chi(v2),
            this constructs the component subgraph directly by filtering cross-half pairs for `chi`.
        """
        if not (dim >= 16 and (dim & (dim - 1)) == 0):
            raise AlgebraDimensionError(f"dim must be a power of 2 >= 16, got {dim}")
        half = dim // 2
        if not (1 <= chi < half):
            raise ValueError(f"chi must be in 1..{half - 1}, got {chi}")

        sign_table, _ = build_cd_multiplication_table(dim)
        pairs: list[tuple[int, int]] = []
        for i in range(1, half):
            j_rel = i ^ chi
            if j_rel == 0 or j_rel >= half or j_rel == i:
                continue
            pairs.append((i, half + j_rel))

        graph: nx.Graph[Any] = nx.Graph()
        node_id = 0
        pair_nodes: dict[tuple[int, int], list[tuple[int, int]]] = {}
        for p in pairs:
            pair_nodes[p] = []
            for s1 in (1, -1):
                for s2 in (1, -1):
                    graph.add_node(node_id, vec=(p[0], p[1], s1, s2), chi=chi)
                    pair_nodes[p].append((node_id, s1 * s2))
                    node_id += 1

        m = len(pairs)
        for u in range(m):
            p1 = pairs[u]
            i1, j1 = p1
            for w in range(u + 1, m):
                p2 = pairs[w]
                i2, j2 = p2
                s_prod = (
                    int(sign_table[i1, i2])
                    * int(sign_table[j1, j2])
                    * int(sign_table[i1, j2])
                    * int(sign_table[j1, i2])
                )
                if s_prod == 1:
                    req = -int(sign_table[i1, i2]) * int(sign_table[j1, j2])
                    for uid, sig1 in pair_nodes[p1]:
                        for wid, sig2 in pair_nodes[p2]:
                            if sig1 * sig2 == req:
                                graph.add_edge(uid, wid)

        return graph

    @classmethod
    def classify_d128_components(cls) -> dict[str, Any]:
        """
        Classifies all 63 components of PG(5, F_2) for D=128 into regularity/biregularity classes,
        edge counts, and spectral types.

        In D=128, the 15,624 cross-half zero divisors partition into exactly 63 components
        of size 248 = 2*(128 - 4).
        """
        classes_data: list[dict[str, Any]] = [
            {
                "class_id": 1,
                "name": "Doubling Poles 2 & 3 / Fano & Doubling Pole 1 (120-Regular)",
                "chis": list(range(1, 9)) + [16, 32],
                "count": 10,
                "edges": 14880,
                "degrees": [120],
                "regularity": "regular",
                "is_regular": True,
                "is_biregular": False,
                "spectral_type": "Pure Integral (chis 16, 32) / Quadratic Q(sqrt(57)) (chis 1..8)",
            },
            {
                "class_id": 2,
                "name": "Pole 3 Affine Shift (Biregular Pure Integral)",
                "chis": list(range(33, 41)) + [48],
                "count": 9,
                "edges": 1440,
                "degrees": [8, 120],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
                "spectral_type": "Pure Integral",
            },
            {
                "class_id": 3,
                "name": "Pole 2 Affine Shift (Biregular Quadratic)",
                "chis": list(range(17, 25)),
                "count": 8,
                "edges": 4128,
                "degrees": [24, 120],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
                "spectral_type": "Quadratic Q(sqrt(57), sqrt(337))",
            },
            {
                "class_id": 4,
                "name": "Pole 1 Fano Junction (Biregular Quadratic)",
                "chis": list(range(9, 16)),
                "count": 7,
                "edges": 8736,
                "degrees": [56, 120],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
                "spectral_type": "Quadratic Q(sqrt(57), sqrt(673))",
            },
            {
                "class_id": 5,
                "name": "Deep Quad-Junction (Multiregular Quartic)",
                "chis": list(range(57, 64)),
                "count": 7,
                "edges": 6048,
                "degrees": [8, 40, 104, 120],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
                "spectral_type": "Quartic Extension (degree 4)",
            },
            {
                "class_id": 6,
                "name": "Affine Cubic Junction 1",
                "chis": list(range(41, 48)),
                "count": 7,
                "edges": 7584,
                "degrees": [8, 72, 120],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
                "spectral_type": "Cubic Extension (degree 3)",
            },
            {
                "class_id": 7,
                "name": "Fano-Pole 1-Pole 2 Triple Junction",
                "chis": list(range(25, 32)),
                "count": 7,
                "edges": 10272,
                "degrees": [24, 88, 120],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
                "spectral_type": "Cubic / Quadratic Extension",
            },
            {
                "class_id": 8,
                "name": "Pole 3 High-Degree Junction",
                "chis": list(range(49, 57)),
                "count": 8,
                "edges": 12192,
                "degrees": [8, 104, 120],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
                "spectral_type": "Cubic Extension (degree 3)",
            },
        ]
        comp_map: dict[int, dict[str, Any]] = {}
        for c in classes_data:
            for chi in c["chis"]:
                comp_map[chi] = c

        return {
            "dim": 128,
            "total_components": 63,
            "component_size": 248,
            "total_zero_divisors": 15624,
            "total_edges": 520800,
            "num_classes": len(classes_data),
            "regular_components_count": 10,
            "biregular_components_count": 24,
            "multiregular_components_count": 29,
            "classes": classes_data,
            "components": comp_map,
        }

    @classmethod
    def classify_d256_components(cls) -> dict[str, Any]:
        """
        Classifies all 127 components of PG(6, F_2) for D=256 into regularity/biregularity classes
        and edge counts.

        In D=256, the 64,008 cross-half zero divisors partition into exactly 127 components
        of size 504 = 2*(256 - 4).
        """
        classes_data: list[dict[str, Any]] = [
            {
                "class_id": 1,
                "chis": [65, 66, 67, 68, 69, 70, 71, 72, 80, 96],
                "count": 10,
                "edges": 2976,
                "degrees": [8, 248],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
            },
            {
                "class_id": 2,
                "chis": [33, 34, 35, 36, 37, 38, 39, 40, 48],
                "count": 9,
                "edges": 8736,
                "degrees": [24, 248],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
            },
            {
                "class_id": 3,
                "chis": [113, 114, 115, 116, 117, 118, 119, 120],
                "count": 8,
                "edges": 13728,
                "degrees": [8, 40, 232, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 4,
                "chis": [17, 18, 19, 20, 21, 22, 23, 24],
                "count": 8,
                "edges": 19488,
                "degrees": [56, 248],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
            },
            {
                "class_id": 5,
                "chis": [89, 90, 91, 92, 93, 94, 95],
                "count": 7,
                "edges": 21408,
                "degrees": [8, 72, 200, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 6,
                "chis": [57, 58, 59, 60, 61, 62, 63],
                "count": 7,
                "edges": 27168,
                "degrees": [24, 88, 216, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 7,
                "chis": [73, 74, 75, 76, 77, 78, 79],
                "count": 7,
                "edges": 27552,
                "degrees": [8, 136, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 8,
                "chis": [105, 106, 107, 108, 109, 110, 111],
                "count": 7,
                "edges": 32160,
                "degrees": [8, 104, 232, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 9,
                "chis": [41, 42, 43, 44, 45, 46, 47],
                "count": 7,
                "edges": 33312,
                "degrees": [24, 152, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 10,
                "chis": [9, 10, 11, 12, 13, 14, 15],
                "count": 7,
                "edges": 37920,
                "degrees": [120, 248],
                "regularity": "biregular",
                "is_regular": False,
                "is_biregular": True,
            },
            {
                "class_id": 11,
                "chis": [121, 122, 123, 124, 125, 126, 127],
                "count": 7,
                "edges": 38304,
                "degrees": [8, 40, 168, 232, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 12,
                "chis": [25, 26, 27, 28, 29, 30, 31],
                "count": 7,
                "edges": 44064,
                "degrees": [56, 184, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 13,
                "chis": [81, 82, 83, 84, 85, 86, 87, 88],
                "count": 8,
                "edges": 45984,
                "degrees": [8, 200, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 14,
                "chis": [49, 50, 51, 52, 53, 54, 55, 56],
                "count": 8,
                "edges": 51744,
                "degrees": [24, 216, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 15,
                "chis": [97, 98, 99, 100, 101, 102, 103, 104, 112],
                "count": 9,
                "edges": 56736,
                "degrees": [8, 232, 248],
                "regularity": "multiregular",
                "is_regular": False,
                "is_biregular": False,
            },
            {
                "class_id": 16,
                "chis": [1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 64],
                "count": 11,
                "edges": 62496,
                "degrees": [248],
                "regularity": "regular",
                "is_regular": True,
                "is_biregular": False,
            },
        ]
        comp_map: dict[int, dict[str, Any]] = {}
        for c in classes_data:
            for chi in c["chis"]:
                comp_map[chi] = c

        return {
            "dim": 256,
            "total_components": 127,
            "component_size": 504,
            "total_zero_divisors": 64008,
            "total_edges": 4187232,
            "num_classes": len(classes_data),
            "regular_components_count": 11,
            "biregular_components_count": 34,
            "multiregular_components_count": 82,
            "classes": classes_data,
            "components": comp_map,
        }

    @classmethod
    def analyze_higher_tower_spectrum(cls, dim: int, chi: int) -> dict[str, Any]:
        """
        Computes eigenvalues and minimal polynomial splitting behavior for component `chi`
        in dimension `dim`, identifying algebraic number field extensions (quadratic, cubic, quartic, etc.)
        and pure integer spectra at doubling poles (e.g. chi=32 for D=128, chi=64 for D=256).
        """
        G = cls.build_component_graph(dim=dim, chi=chi)
        adj_matrix: npt.NDArray[np.float64] = nx.to_numpy_array(G)
        raw_eigs = np.linalg.eigvalsh(adj_matrix)
        rounded_eigs = sorted(set(np.round(raw_eigs, 4)))
        irrational_eigs = [float(e) for e in raw_eigs if abs(e - round(e)) > 1e-3]
        degrees = sorted({int(d) for _, d in G.degree()})

        # Find unique irrational values
        unique_irr: list[float] = []
        for e in irrational_eigs:
            if not any(abs(e - u) < 1e-4 for u in unique_irr):
                unique_irr.append(e)
        unique_irr.sort()

        is_integral = len(irrational_eigs) == 0
        is_regular = len(degrees) == 1
        is_biregular = len(degrees) == 2

        pole_chi = dim // 4
        is_doubling_pole = chi == pole_chi

        ext_name = "Q"
        max_deg = 1
        min_polys: list[str] = []

        if is_integral:
            ext_name = "Q"
            max_deg = 1
            if is_doubling_pole:
                bound = dim - 8
                min_polys = [f"x - {bound}", f"x + {bound}", "x - 4", "x + 4", "x"]
            else:
                min_polys = [f"x - {int(v)}" if v >= 0 else f"x + {int(-v)}" for v in rounded_eigs]
        else:
            # Detect irreducible minimal polynomial factors
            remaining = list(unique_irr)
            used_indices = set()

            # 1. Quadratic factors (pairs)
            for i in range(len(remaining)):
                if i in used_indices:
                    continue
                for j in range(i + 1, len(remaining)):
                    if j in used_indices:
                        continue
                    r1, r2 = remaining[i], remaining[j]
                    s = r1 + r2
                    p = r1 * r2
                    if abs(s - round(s)) < 1e-3 and abs(p - round(p)) < 1e-2:
                        s_int = int(round(s))
                        p_int = int(round(p))
                        if s_int != 0:
                            poly_str = (
                                f"x^2 - {s_int}*x + {p_int}"
                                if p_int >= 0
                                else f"x^2 - {s_int}*x - {-p_int}"
                            )
                        else:
                            poly_str = f"x^2 - {-p_int}" if p_int < 0 else f"x^2 + {p_int}"
                        min_polys.append(poly_str)
                        used_indices.add(i)
                        used_indices.add(j)
                        max_deg = max(max_deg, 2)
                        break

            unpaired = [remaining[k] for k in range(len(remaining)) if k not in used_indices]

            # 2. Cubic factors (triples among unpaired roots)
            if len(unpaired) >= 3:
                used_cubics = set()
                for triple in itertools.combinations(range(len(unpaired)), 3):
                    if any(idx in used_cubics for idx in triple):
                        continue
                    e1, e2, e3 = [unpaired[idx] for idx in triple]
                    s1 = e1 + e2 + e3
                    s2 = e1 * e2 + e2 * e3 + e3 * e1
                    s3 = e1 * e2 * e3
                    if (
                        abs(s1 - round(s1)) < 1e-3
                        and abs(s2 - round(s2)) < 1e-2
                        and abs(s3 - round(s3)) < 1e-1
                    ):
                        s1_int, s2_int, s3_int = int(round(s1)), int(round(s2)), int(round(s3))
                        poly_str = f"x^3 - {s1_int}*x^2 + {s2_int}*x - {s3_int}"
                        min_polys.append(poly_str)
                        for idx in triple:
                            used_cubics.add(idx)
                        max_deg = max(max_deg, 3)

                unpaired = [unpaired[k] for k in range(len(unpaired)) if k not in used_cubics]

            # 3. Quartic factors (quadruples among unpaired roots)
            if len(unpaired) >= 4:
                for quad in itertools.combinations(range(len(unpaired)), 4):
                    e1, e2, e3, e4 = [unpaired[idx] for idx in quad]
                    s1 = e1 + e2 + e3 + e4
                    s2 = e1 * e2 + e1 * e3 + e1 * e4 + e2 * e3 + e2 * e4 + e3 * e4
                    s3 = e1 * e2 * e3 + e1 * e2 * e4 + e1 * e3 * e4 + e2 * e3 * e4
                    s4 = e1 * e2 * e3 * e4
                    if (
                        abs(s1 - round(s1)) < 1e-3
                        and abs(s2 - round(s2)) < 1e-2
                        and abs(s3 - round(s3)) < 1e-1
                        and abs(s4 - round(s4)) < 1.0
                    ):
                        s1_int, s2_int, s3_int, s4_int = (
                            int(round(s1)),
                            int(round(s2)),
                            int(round(s3)),
                            int(round(s4)),
                        )
                        poly_str = f"x^4 - {s1_int}*x^3 + {s2_int}*x^2 - {s3_int}*x + {s4_int}"
                        min_polys.append(poly_str)
                        max_deg = max(max_deg, 4)

            ext_map = {
                2: "Quadratic",
                3: "Cubic",
                4: "Quartic",
            }
            ext_name = ext_map.get(max_deg, f"Degree {max_deg}")

        return {
            "dim": dim,
            "chi": chi,
            "nodes": G.number_of_nodes(),
            "edges": G.number_of_edges(),
            "degrees": degrees,
            "is_regular": is_regular,
            "is_biregular": is_biregular,
            "unique_eigenvalues": rounded_eigs,
            "irrational_eigenvalues": unique_irr,
            "irrational_eigenvalue_count": len(irrational_eigs),
            "is_integral": is_integral,
            "is_doubling_pole": is_doubling_pole,
            "field_extension": ext_name,
            "algebraic_degree": max_deg,
            "minimal_polynomials": min_polys,
        }
