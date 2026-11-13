"""
Zero-Divisor Annihilation Graph.

Constructs and analyzes the 8-regular annihilation graph Γ on the 168 cross-octet
zero divisors in the sedenion algebra.
"""

from typing import TYPE_CHECKING, Any

import networkx as nx
import numpy as np
import numpy.typing as npt

if TYPE_CHECKING:
    from typing import TypeAlias

    NXGraph: TypeAlias = nx.Graph[Any]
else:
    NXGraph = nx.Graph

from .stratification import CrossOctetVector, stratify_cross_octet


class AnnihilationGraph:
    """Graph of zero divisors where edges represent mutual annihilation."""

    def __init__(
        self,
        zero_divisors: list[CrossOctetVector] | None = None,
        annihilator_map: dict[CrossOctetVector, list[CrossOctetVector]] | None = None,
    ):
        if zero_divisors is None or annihilator_map is None:
            zd, _, ann_map = stratify_cross_octet()
            self.zero_divisors = zd
            self.annihilator_map = ann_map
        else:
            self.zero_divisors = zero_divisors
            self.annihilator_map = annihilator_map

        self.zd_to_id: dict[CrossOctetVector, int] = {
            v: idx for idx, v in enumerate(self.zero_divisors)
        }
        self.id_to_zd: dict[int, CrossOctetVector] = dict(enumerate(self.zero_divisors))
        self.nx_graph: NXGraph = self._build_graph()

    def _build_graph(self) -> NXGraph:
        """Constructs the undirected NetworkX graph."""
        G: NXGraph = nx.Graph()
        for idx in range(len(self.zero_divisors)):
            G.add_node(idx, vector=self.id_to_zd[idx])

        for u, neighbors in self.annihilator_map.items():
            u_id = self.zd_to_id[u]
            for v in neighbors:
                v_id = self.zd_to_id[v]
                G.add_edge(u_id, v_id)

        return G

    @property
    def num_vertices(self) -> int:
        return int(self.nx_graph.number_of_nodes())

    @property
    def num_edges(self) -> int:
        return int(self.nx_graph.number_of_edges())

    def degrees(self) -> list[int]:
        return [deg for _, deg in self.nx_graph.degree()]

    def is_regular(self) -> tuple[bool, int]:
        degs = set(self.degrees())
        if len(degs) == 1:
            return True, next(iter(degs))
        return False, -1

    def is_symmetric(self) -> bool:
        """Verifies u * v = 0 <=> v * u = 0 for all zero divisors."""
        for u, neighbors in self.annihilator_map.items():
            for v in neighbors:
                if u not in self.annihilator_map[v]:
                    return False
        return True

    def compute_spectrum(self) -> tuple[np.ndarray, dict[float, int]]:
        """
        Computes the adjacency matrix eigenvalues and their algebraic multiplicities.
        """
        A: npt.NDArray[np.float64] = nx.to_numpy_array(self.nx_graph)
        eigenvalues = np.linalg.eigvalsh(A)
        # Round eigenvalues to 5 decimal places to aggregate multiplicities
        rounded = np.round(eigenvalues, decimals=5)
        unique, counts = np.unique(rounded, return_counts=True)
        multiplicities = {float(val): int(count) for val, count in zip(unique, counts, strict=True)}
        return eigenvalues, multiplicities

    def connected_components(self) -> list[set[int]]:
        return list(nx.connected_components(self.nx_graph))

    def girth(self) -> int:
        """Returns the length of the shortest cycle (girth) of the graph."""
        try:
            girth_val = nx.girth(self.nx_graph)
            return int(girth_val)
        except AttributeError:
            cycles = nx.cycle_basis(self.nx_graph)
            min_cycle = min(len(c) for c in cycles) if cycles else float("inf")
            return int(min_cycle)

    def clique_number(self) -> int:
        """Computes the maximum clique size."""
        cliques = nx.find_cliques(self.nx_graph)
        return max(len(c) for c in cliques)

    def component_subgraphs(self) -> list[NXGraph]:
        """Returns the induced subgraphs for all connected components."""
        comps = self.connected_components()
        return [self.nx_graph.subgraph(c).copy() for c in comps]

    @staticmethod
    def analyze_component_quotient(comp: NXGraph) -> dict[str, Any]:
        """
        Analyzes the twin-partition quotient structure of a 24-vertex component.
        Verifies that it is isomorphic to the blowup K_{3,3}[4].
        """
        import math
        from collections import defaultdict

        # Identify bipartite sets
        v1, v2 = nx.bipartite.sets(comp)

        # Group by identical neighborhood
        clusters_v1: dict[frozenset[int], list[int]] = defaultdict(list)
        for u in v1:
            clusters_v1[frozenset(comp.neighbors(u))].append(u)

        clusters_v2: dict[frozenset[int], list[int]] = defaultdict(list)
        for w in v2:
            clusters_v2[frozenset(comp.neighbors(w))].append(w)

        all_clusters: list[list[int]] = list(clusters_v1.values()) + list(clusters_v2.values())

        # Build quotient graph
        quotient: nx.Graph[Any] = nx.Graph()
        for idx in range(len(all_clusters)):
            quotient.add_node(idx, size=len(all_clusters[idx]))

        for i, c_i in enumerate(all_clusters):
            rep_i = c_i[0]
            for j in range(i + 1, len(all_clusters)):
                rep_j = all_clusters[j][0]
                if comp.has_edge(rep_i, rep_j):
                    quotient.add_edge(i, j)

        # Check if quotient is isomorphic to C_6 (6-cycle / hexagon)
        c6 = nx.cycle_graph(6)
        is_c6 = nx.is_isomorphic(quotient, c6)

        # Automorphism group order of C_6[4] (blowup of 6-cycle with 4 vertices per cluster)
        # |Aut(C_6)| = |D_6| = 12 (symmetries of the hexagon)
        # Internal cluster permutations = (4!)^6 = 24^6 = 191,102,976
        # Total order = 12 * (4!)^6 = 2,293,235,712
        cluster_sizes = [len(c) for c in all_clusters]
        all_size_4 = all(s == 4 for s in cluster_sizes)
        aut_order = 12 * (math.factorial(4) ** 6) if (is_c6 and all_size_4) else None

        # Ramanujan check: degree d=8, 2*sqrt(d-1) = 2*sqrt(7)
        A = nx.to_numpy_array(comp)
        evals = np.sort(np.linalg.eigvalsh(A))[::-1]
        lambda_2 = float(evals[1])
        ramanujan_bound = float(2.0 * np.sqrt(7.0))
        is_ramanujan = lambda_2 <= ramanujan_bound

        return {
            "is_c6_blowup": is_c6 and all_size_4,
            "num_clusters": len(all_clusters),
            "cluster_sizes": cluster_sizes,
            "automorphism_order": aut_order,
            "lambda_2": round(lambda_2, 6),
            "ramanujan_bound": ramanujan_bound,
            "is_ramanujan": is_ramanujan,
        }


_CACHED_GRAPH: AnnihilationGraph | None = None


def get_cached_annihilation_graph() -> AnnihilationGraph:
    """Returns a process-level cached instance of the 8-regular Annihilation Graph."""
    global _CACHED_GRAPH
    if _CACHED_GRAPH is None:
        _CACHED_GRAPH = AnnihilationGraph()
    return _CACHED_GRAPH
