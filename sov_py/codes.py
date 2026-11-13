"""
Binary Linear Codes, MOG Embeddings, and Antipodal Involutions.

Analyzes the error-correcting codes and finite geometric structures induced by the
sedenion zero-divisor annihilation graph Γ:
- [24, 4, 8] doubly-even binary linear codes per Ramanujan component
- Miracle Octad Generator (MOG) 4x6 coordinate array embeddings
- Antipodal transposition involution on the quotient 6-cycle C_6
- [168, 28, 8] total orthogonal direct sum code of dimension 28 = dim(so(8))
"""

from collections import Counter
from itertools import product
from typing import Any

import networkx as nx
import numpy as np

from .graph import AnnihilationGraph
from .stratification import CrossOctetVector


def gf2_rref(matrix: np.ndarray) -> tuple[int, np.ndarray]:
    """
    Computes row echelon form (RREF) over GF(2) via Gaussian elimination.
    Returns (rank, basis_rows).
    """
    mat = matrix.copy() % 2
    r = 0
    rows, cols = mat.shape
    for c in range(cols):
        pivot = None
        for i in range(r, rows):
            if mat[i, c] == 1:
                pivot = i
                break
        if pivot is not None:
            mat[[r, pivot]] = mat[[pivot, r]]
            for i in range(rows):
                if i != r and mat[i, c] == 1:
                    mat[i] = (mat[i] + mat[r]) % 2
            r += 1
    return r, mat[:r]


class BinaryLinearCode:
    """Represents a binary linear code over GF(2)."""

    def __init__(self, generator_matrix: np.ndarray):
        mat = np.array(generator_matrix, dtype=int) % 2
        self.dimension, self.basis = gf2_rref(mat)
        self.generator_matrix = self.basis
        self.length = mat.shape[1]

    def generate_all_codewords(self) -> list[np.ndarray]:
        """Generates all 2^k codewords in the binary linear space."""
        codewords = []
        for bits in product([0, 1], repeat=self.dimension):
            c = np.zeros(self.length, dtype=int)
            for bit, row in zip(bits, self.basis, strict=True):
                if bit:
                    c = (c + row) % 2
            codewords.append(c)
        return codewords

    def weight_distribution(self) -> dict[int, int]:
        """Computes the exact weight enumerator histogram of the code."""
        codewords = self.generate_all_codewords()
        weights = [int(c.sum()) for c in codewords]
        return dict(Counter(weights))

    @property
    def minimum_distance(self) -> int:
        """Returns the minimum non-zero Hamming weight."""
        wd = self.weight_distribution()
        non_zeros = [w for w in wd if w > 0]
        return min(non_zeros) if non_zeros else 0

    def is_doubly_even(self) -> bool:
        """Returns True iff all codeword weights are divisible by 4."""
        wd = self.weight_distribution()
        return all(w % 4 == 0 for w in wd)

    def is_triply_even(self) -> bool:
        """Returns True iff all codeword weights are divisible by 8."""
        wd = self.weight_distribution()
        return all(w % 8 == 0 for w in wd)


class MOGComponentEmbedding:
    """
    Embeds a 24-vertex Ramanujan component into a 4x6 Miracle Octad Generator grid.

    6 Columns: The 6 ordered index pairs (i, j) along the quotient 6-cycle C_6.
    4 Rows: The 4 sign combinations (+,+), (+,-), (-,+), (-,-).
    """

    SIGN_ORDER: list[tuple[int, int]] = [(1, 1), (1, -1), (-1, 1), (-1, -1)]

    def __init__(self, component_graph: "nx.Graph[Any]"):
        self.graph = component_graph
        self.nodes = list(component_graph.nodes)
        if len(self.nodes) != 24:
            raise ValueError(f"Component must have exactly 24 vertices, got {len(self.nodes)}")

        # Extract vectors
        self.node_vectors: dict[int, CrossOctetVector] = {
            n: component_graph.nodes[n]["vector"] for n in self.nodes
        }

        # Extract XOR charge
        charges = {v.i ^ v.j for v in self.node_vectors.values()}
        if len(charges) != 1:
            raise ValueError(
                f"All vectors in component must share identical XOR charge, got {charges}"
            )
        self.chi = next(iter(charges))

        # Discover the 6 clusters and the cyclic ordering
        self.clusters, self.ordered_pairs = self._order_cycle_pairs()

    def _order_cycle_pairs(self) -> tuple[dict[tuple[int, int], list[int]], list[tuple[int, int]]]:
        """Finds the 6 clusters and puts them in order along the C_6 cycle."""
        from collections import defaultdict

        clusters: dict[tuple[int, int], list[int]] = defaultdict(list)
        for n, v in self.node_vectors.items():
            clusters[(v.i, v.j)].append(n)

        # Build cluster adjacency
        pair_list = list(clusters.keys())
        pair_graph: nx.Graph[Any] = nx.Graph()
        for p in pair_list:
            pair_graph.add_node(p)
        for i in range(len(pair_list)):
            for j in range(i + 1, len(pair_list)):
                p1, p2 = pair_list[i], pair_list[j]
                if self.graph.has_edge(clusters[p1][0], clusters[p2][0]):
                    pair_graph.add_edge(p1, p2)

        # Traverse the 6-cycle
        cycles = nx.cycle_basis(pair_graph)
        cycle_nodes = cycles[0] if cycles else pair_list
        return clusters, cycle_nodes

    def verify_antipodal_transposition(self) -> bool:
        """
        Verifies that (i, j) and (j, i) are always antipodal (distance 3 in C_6).
        """
        n = len(self.ordered_pairs)
        if n != 6:
            raise ValueError(f"Ordered pairs must form a 6-cycle, got {n}")
        for idx, (i, j) in enumerate(self.ordered_pairs):
            transpose = (j, i)
            trans_idx = self.ordered_pairs.index(transpose)
            dist = min((idx - trans_idx) % n, (trans_idx - idx) % n)
            if dist != 3:
                return False
        return True

    def canonical_mog_nodes(self) -> list[int]:
        """
        Returns the 24 node IDs ordered canonically by the 6 cycle pairs and 4 signs.
        """
        ordered_nodes: list[int] = []
        for pair in self.ordered_pairs:
            cluster = self.clusters[pair]
            sign_map = {(self.node_vectors[n].s1, self.node_vectors[n].s2): n for n in cluster}
            for s in self.SIGN_ORDER:
                ordered_nodes.append(sign_map[s])
        return ordered_nodes

    def build_canonical_binary_code(self) -> BinaryLinearCode:
        """
        Constructs the [24, 4, 8] code with canonical MOG coordinate ordering.
        """
        nodes = self.canonical_mog_nodes()
        A: np.ndarray = nx.to_numpy_array(self.graph, nodelist=nodes, dtype=int)
        return BinaryLinearCode(A)

    def build_binary_code(self) -> BinaryLinearCode:
        """Constructs the [24, 4, 8] doubly-even code from the adjacency matrix."""
        A: np.ndarray = nx.to_numpy_array(self.graph, dtype=int)
        return BinaryLinearCode(A)


class LeechLatticeEmbedding:
    """
    Construction B embedding of [24, 4, 8] doubly-even Fano component codes
    into the 24-dimensional Leech lattice Lambda_24.

    Given codeword c in {0, 1}^24 (weights 0, 8, 16):
    - Scale 'norm8': x = c in Z^24 with sum(x_i) = wt(c) = 0 mod 4.
      Weight-8 octads embed to vectors of squared Euclidean norm ||x||^2 = 8.
      Pairwise inner products of distinct octads lie in {0, 4}.
    - Scale 'norm32': x = 2*c in {0, 2}^24 with sum(x_i) = 2*wt(c) = 0 mod 4.
      Weight-8 octads embed to vectors of squared Euclidean norm ||x||^2 = 32.
      Pairwise inner products of distinct octads lie in {0, 16}.
    """

    def __init__(self, scale: str = "norm8") -> None:
        if scale not in ("norm8", "norm32"):
            raise ValueError(f"scale must be 'norm8' or 'norm32', got '{scale}'")
        self.scale = scale

    def embed_codeword(self, codeword: np.ndarray, scale: str | None = None) -> np.ndarray:
        """
        Embeds a binary codeword c in {0, 1}^24 into a Construction B lattice vector x in Z^24.
        Verifies sum(x_i) = 0 mod 4.
        """
        c = np.asarray(codeword, dtype=int)
        if c.ndim != 1 or c.shape[0] != 24:
            raise ValueError(f"Codeword must be 1D array of length 24, got shape {c.shape}")
        if not np.all((c == 0) | (c == 1)):
            raise ValueError("Codeword entries must be binary (0 or 1)")
        wt = int(np.sum(c))
        if wt % 4 != 0:
            raise ValueError(
                f"Construction B requires doubly-even codeword weight (0 mod 4), got {wt}"
            )

        effective_scale = scale if scale is not None else self.scale
        if effective_scale == "norm8":
            x = c.copy()
        elif effective_scale == "norm32":
            x = 2 * c
        else:
            raise ValueError(f"Unknown scale: {effective_scale}")

        if int(np.sum(x)) % 4 != 0:
            raise ValueError("Construction B condition sum(x_i) = 0 mod 4 violated")
        return x

    def extract_octads(self, code: BinaryLinearCode) -> list[np.ndarray]:
        """
        Extracts the 6 weight-8 octads from the [24, 4, 8] code.
        """
        cws = code.generate_all_codewords()
        octads = [c for c in cws if int(np.sum(c)) == 8]
        if len(octads) != 6:
            raise ValueError(f"Expected exactly 6 octads of weight 8, got {len(octads)}")
        return octads

    def embed_octads(self, code: BinaryLinearCode, scale: str | None = None) -> list[np.ndarray]:
        """
        Embeds all 6 weight-8 octads of the code into lattice vectors.
        """
        octads = self.extract_octads(code)
        return [self.embed_codeword(octad, scale=scale) for octad in octads]

    @staticmethod
    def inner_product(v1: np.ndarray, v2: np.ndarray) -> int:
        """Computes exact Euclidean inner product between lattice vectors."""
        return int(np.dot(v1, v2))

    @staticmethod
    def gram_matrix(vectors: list[np.ndarray] | np.ndarray) -> np.ndarray:
        """
        Computes the Gram matrix G_ij = <v_i, v_j> for a collection of lattice vectors.
        """
        V = np.asarray(vectors, dtype=float)
        return np.asarray(V @ V.T, dtype=float)

    @staticmethod
    def is_positive_semidefinite(gram: np.ndarray, tol: float = 1e-9) -> bool:
        """
        Verifies that the Gram matrix is positive semi-definite (all eigenvalues >= -tol).
        """
        eigs = np.linalg.eigvalsh(gram)
        return bool(np.all(eigs >= -tol))

    @staticmethod
    def octad_intersections(octads: list[np.ndarray]) -> np.ndarray:
        """
        Computes the 6x6 matrix of pairwise intersection sizes |O_i cap O_j|.
        """
        oct_mat = np.asarray(octads, dtype=int)
        return np.asarray(oct_mat @ oct_mat.T, dtype=int)

    def evaluate_component_octads(
        self, code: BinaryLinearCode, scale: str | None = None
    ) -> dict[str, Any]:
        """
        Evaluates norms, Gram matrix, and intersection structure for octads in a component.
        """
        effective_scale = scale if scale is not None else self.scale
        octads = self.extract_octads(code)
        vectors = [self.embed_codeword(o, scale=effective_scale) for o in octads]
        gram = self.gram_matrix(vectors)
        intersections = self.octad_intersections(octads)
        norms_sq = [self.inner_product(v, v) for v in vectors]
        target_norm = 8 if effective_scale == "norm8" else 32

        # Distinct off-diagonal inner products and intersections
        n_oct = len(octads)
        distinct_intersections: set[int] = set()
        distinct_inner_products: set[int] = set()
        for i in range(n_oct):
            for j in range(i + 1, n_oct):
                distinct_intersections.add(int(intersections[i, j]))
                distinct_inner_products.add(int(gram[i, j]))

        expected_inner = {0, 4} if effective_scale == "norm8" else {0, 16}
        return {
            "scale": effective_scale,
            "num_octads": n_oct,
            "target_norm_sq": target_norm,
            "all_norms_match": all(n == target_norm for n in norms_sq),
            "gram_matrix": gram,
            "is_psd": self.is_positive_semidefinite(gram),
            "intersections": intersections,
            "distinct_intersections": sorted(distinct_intersections),
            "distinct_inner_products": sorted(distinct_inner_products),
            "intersections_valid": distinct_intersections.issubset({0, 4}),
            "inner_products_valid": distinct_inner_products.issubset(expected_inner),
            "octad_vectors": vectors,
        }

    def cross_component_evaluation(
        self,
        component_codes: list[BinaryLinearCode] | None = None,
        mode: str = "canonical_mog",
    ) -> dict[str, Any]:
        """
        Evaluates inner products and intersections across all 7 Fano components.

        Modes:
        - 'canonical_mog': each component's code is viewed in canonical 24D MOG coordinates.
        - 'direct_sum_168': all 7 components are embedded into disjoint 24-coordinate blocks
          of R^168 (the total direct sum code).
        """
        if component_codes is None:
            g = AnnihilationGraph()
            components = g.component_subgraphs()
            if mode == "canonical_mog":
                component_codes = [
                    MOGComponentEmbedding(comp).build_canonical_binary_code() for comp in components
                ]
            else:
                component_codes = [
                    MOGComponentEmbedding(comp).build_binary_code() for comp in components
                ]

        if len(component_codes) != 7:
            raise ValueError(f"Expected 7 component codes, got {len(component_codes)}")

        all_octads = [self.extract_octads(c) for c in component_codes]

        if mode == "direct_sum_168":
            vectors_168: list[np.ndarray] = []
            for comp_idx, octs in enumerate(all_octads):
                for octad in octs:
                    v = np.zeros(168, dtype=int)
                    v[comp_idx * 24 : (comp_idx + 1) * 24] = (
                        octad if self.scale == "norm8" else 2 * octad
                    )
                    vectors_168.append(v)
            gram = self.gram_matrix(vectors_168)
            n_tot = len(vectors_168)
            distinct_inners: set[int] = set()
            for i in range(n_tot):
                for j in range(i + 1, n_tot):
                    distinct_inners.add(int(gram[i, j]))
            expected = {0, 4} if self.scale == "norm8" else {0, 16}
            return {
                "mode": mode,
                "total_octads": n_tot,
                "gram_matrix": gram,
                "is_psd": self.is_positive_semidefinite(gram),
                "distinct_off_diagonal_inner_products": sorted(distinct_inners),
                "inner_products_valid": distinct_inners.issubset(expected),
            }
        else:
            cross_intersections: set[int] = set()
            cross_inners: set[int] = set()
            for c1 in range(7):
                for c2 in range(c1 + 1, 7):
                    for o1 in all_octads[c1]:
                        for o2 in all_octads[c2]:
                            inter = int(np.dot(o1, o2))
                            cross_intersections.add(inter)
                            v1 = self.embed_codeword(o1)
                            v2 = self.embed_codeword(o2)
                            cross_inners.add(self.inner_product(v1, v2))

            expected_inner = {0, 4} if self.scale == "norm8" else {0, 16}
            target_norm = 8 if self.scale == "norm8" else 32
            return {
                "mode": mode,
                "cross_intersections": sorted(cross_intersections),
                "cross_inner_products": sorted(cross_inners),
                "intersections_valid": cross_intersections.issubset({0, 4, 8}),
                "distinct_intersections_valid": {x for x in cross_intersections if x != 8}.issubset(
                    {0, 4}
                ),
                "inner_products_valid": {x for x in cross_inners if x != target_norm}.issubset(
                    expected_inner
                ),
            }


def embed_fano_component_into_leech(component_idx: int = 0) -> dict[str, Any]:
    """
    Embeds the [24, 4, 8] code of Fano component `component_idx` into the Leech lattice.
    Returns minimal norms, Gram matrices for norm8 and norm32, and pairwise intersections.
    """
    g = AnnihilationGraph()
    comps = g.component_subgraphs()
    if 0 <= component_idx < len(comps):
        idx = component_idx
    elif 1 <= component_idx <= len(comps):
        idx = component_idx - 1
    else:
        idx = component_idx % len(comps)

    comp = comps[idx]
    emb = MOGComponentEmbedding(comp)
    code = emb.build_canonical_binary_code()
    chi = emb.chi

    leech_norm8 = LeechLatticeEmbedding(scale="norm8")
    eval_norm8 = leech_norm8.evaluate_component_octads(code)

    leech_norm32 = LeechLatticeEmbedding(scale="norm32")
    eval_norm32 = leech_norm32.evaluate_component_octads(code)

    return {
        "component_idx": idx,
        "chi": chi,
        "code": code,
        "octads": eval_norm8["octad_vectors"],
        "lattice_vectors_norm8": eval_norm8["octad_vectors"],
        "lattice_vectors_norm32": eval_norm32["octad_vectors"],
        "minimal_norm_norm8": 8,
        "minimal_norm_norm32": 32,
        "gram_matrix_norm8": eval_norm8["gram_matrix"],
        "gram_matrix_norm32": eval_norm32["gram_matrix"],
        "is_positive_semidefinite_norm8": eval_norm8["is_psd"],
        "is_positive_semidefinite_norm32": eval_norm32["is_psd"],
        "intersections": eval_norm8["intersections"],
        "distinct_intersections": eval_norm8["distinct_intersections"],
        "distinct_inner_products_norm8": eval_norm8["distinct_inner_products"],
        "distinct_inner_products_norm32": eval_norm32["distinct_inner_products"],
        "all_octad_norms_match": (eval_norm8["all_norms_match"] and eval_norm32["all_norms_match"]),
        "pairwise_intersections_valid": eval_norm8["intersections_valid"],
        "sum_mod_4_verified": all(int(np.sum(v)) % 4 == 0 for v in eval_norm8["octad_vectors"]),
    }


def analyze_annihilation_codes() -> dict[str, Any]:
    """
    Computes the full coding-theoretic invariants across all components
    and for the total 168-vertex graph.
    """
    g = AnnihilationGraph()
    components = g.component_subgraphs()

    component_codes: list[BinaryLinearCode] = []
    antipodal_verified: list[bool] = []

    for comp in components:
        embedding = MOGComponentEmbedding(comp)
        code = embedding.build_binary_code()
        component_codes.append(code)
        antipodal_verified.append(embedding.verify_antipodal_transposition())

    # Full graph code
    A_full: np.ndarray = nx.to_numpy_array(g.nx_graph, dtype=int)
    full_code = BinaryLinearCode(A_full)

    return {
        "all_antipodal_distance_3": all(antipodal_verified),
        "component_dimension": component_codes[0].dimension,
        "component_minimum_distance": component_codes[0].minimum_distance,
        "component_weight_distribution": component_codes[0].weight_distribution(),
        "component_is_doubly_even": component_codes[0].is_doubly_even(),
        "component_is_triply_even": component_codes[0].is_triply_even(),
        "full_graph_dimension": full_code.dimension,
        "dim_so8_match": full_code.dimension == 28,
        "component_codes": component_codes,
    }
