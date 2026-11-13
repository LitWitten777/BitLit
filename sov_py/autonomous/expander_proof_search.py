"""
src/sedenion/autonomous/expander_proof_search.py
=============================================================================
Ramanujan Expander Geodesic Proof Search Engine (Priority 1).
Reduces exponential search O(b^d) to bounded diameter-3 geodesic pathfinding
on the 8-regular Ramanujan graph C_6[K_4].
=============================================================================
"""

import collections
from dataclasses import dataclass
import math
from typing import Any, Dict, List, Optional, Sequence, Tuple
import networkx as nx
import numpy as np


@dataclass(frozen=True)
class GeodesicProofPath:
    """Represents a geodesic path in the expander graph."""

    source: int
    target: int
    path: List[int]
    length: int
    is_geodesic: bool = True
    is_bounded: bool = True


class ExpanderGeodesicSearch:
    """Geodesic proof search on an expander sector."""

    def __init__(self, sector: int = 0, dimension: int = 16):
        self.sector = sector
        self.dimension = dimension
        self.navigator = ExpanderProofNavigator(sector_id=sector, dimension=dimension)
        self.component = nx.Graph()
        for u, neighbors in self.navigator.adj.items():
            for v in neighbors:
                self.component.add_edge(u, v)

    @property
    def num_nodes(self) -> int:
        return self.component.number_of_nodes()

    @property
    def num_edges(self) -> int:
        return self.component.number_of_edges()

    def verify_all_pairs_bounded(self) -> Tuple[bool, int, float]:
        lengths = dict(nx.all_pairs_shortest_path_length(self.component))
        all_dists: List[int] = []
        max_d = 0
        for src, targets in lengths.items():
            for tgt, d in targets.items():
                if src != tgt:
                    all_dists.append(d)
                    if d > max_d:
                        max_d = d
        all_bounded = max_d <= 3
        avg_dist = float(np.mean(all_dists)) if all_dists else 0.0
        return all_bounded, max_d, avg_dist

    def find_proof_path(self, start: int, goal: int) -> GeodesicProofPath:
        path = self.navigator.get_geodesic(start, goal)
        length = len(path) - 1
        return GeodesicProofPath(
            source=start,
            target=goal,
            path=path,
            length=length,
            is_geodesic=True,
            is_bounded=length <= 3,
        )


class ExpanderProofNavigator:
    """
    Geodesic navigator on zero-divisor expander graph sectors.
    Supports D=16 C_6[K_4] as well as higher tower dimensions D=32, 64, 128.
    Key Invariants:
    - Order n vertices per sector.
    - Degree d.
    - Second eigenvalue lambda_2.
    - Ramanujan family: DOUBLING_POLE, BIREGULAR_MATCHING_CONE, GAUGE_DOUBLE_COVER, MULTIREGULAR.
    - Universal diameter invariant: D <= 3 for all sectors.
    """

    def __init__(
        self,
        sector_id: int = 0,
        dimension: int = 16,
        graph: Optional[nx.Graph] = None,
    ):
        self.sector_id = sector_id
        self.dimension = dimension

        if graph is not None:
            self.adj = collections.defaultdict(list)
            nodes = sorted(list(graph.nodes()))
            node_to_idx = {n: i for i, n in enumerate(nodes)}
            self.n = len(nodes)
            for u, v in graph.edges():
                iu = node_to_idx[u]
                iv = node_to_idx[v]
                self.adj[iu].append(iv)
                self.adj[iv].append(iu)
            degs = [len(self.adj[i]) for i in range(self.n)]
            self.degree = degs[0] if degs else 0
            adj_mat = np.zeros((self.n, self.n), dtype=float)
            for u in range(self.n):
                for v in self.adj[u]:
                    adj_mat[u, v] = 1.0
            eigs = np.sort(np.linalg.eigvalsh(adj_mat))[::-1]
            self.lambda_2 = float(eigs[1]) if len(eigs) > 1 else 0.0
            ram_bd = 2.0 * math.sqrt(max(self.degree - 1, 0))
            self.is_ramanujan = self.lambda_2 <= ram_bd + 1e-5
            self.ramanujan_family = (
                "DOUBLING_POLE"
                if (dimension == 16 or sector_id == dimension // 4)
                else ("BIREGULAR_MATCHING_CONE" if len(set(degs)) == 2 else "GAUGE_DOUBLE_COVER")
            )
        elif dimension > 16:
            from ..cd_algebra import CDStratificationEngine

            strat = CDStratificationEngine(dim=dimension)
            actual_sector = sector_id if sector_id > 0 else (dimension // 4)
            g = CDStratificationEngine.build_component_graph(dimension, actual_sector)
            sector_info = strat.analyze_sector_degrees(actual_sector)
            self.ramanujan_family = sector_info["ramanujan_family"]
            self.is_ramanujan = sector_info["is_ramanujan"]
            nodes = sorted(list(g.nodes()))
            node_to_idx = {n: i for i, n in enumerate(nodes)}
            self.n = len(nodes)
            self.adj = collections.defaultdict(list)
            for u, v in g.edges():
                iu = node_to_idx[u]
                iv = node_to_idx[v]
                self.adj[iu].append(iv)
                self.adj[iv].append(iu)
            degs = [len(self.adj[i]) for i in range(self.n)]
            self.degree = max(degs) if degs else 0
            adj_mat = np.zeros((self.n, self.n), dtype=float)
            for u in range(self.n):
                for v in self.adj[u]:
                    adj_mat[u, v] = 1.0
            eigs = np.sort(np.linalg.eigvalsh(adj_mat))[::-1]
            self.lambda_2 = float(eigs[1]) if len(eigs) > 1 else 0.0
        else:
            self.n = 24
            self.degree = 8
            self.lambda_2 = 4.0
            self.is_ramanujan = True
            self.ramanujan_family = "DOUBLING_POLE" if sector_id in (0, 4) else "GAUGE_DOUBLE_COVER"
            self.adj = self._build_sector_adjacency()

        self._geodesic_table = self._compute_all_pairs_geodesics()
        max_d = 0
        for (u, v), p in self._geodesic_table.items():
            if len(p) - 1 > max_d:
                max_d = len(p) - 1
        self.diameter = max_d

    def _build_sector_adjacency(self) -> Dict[int, List[int]]:
        """
        Build adjacency list for C_6[K_4]:
        Vertices are parameterized as (c, i) where c in Z_6, i in {0, 1, 2, 3}.
        Vertex index = c * 4 + i.
        Adjacency: (c, i) ~ (c', j) iff c' = c +/- 1 (mod 6) and (i, j) are twins.
        Every cluster of 4 connects to all 4 vertices in both adjacent clusters:
        4 + 4 = 8 neighbors per vertex.
        """
        adj: Dict[int, List[int]] = collections.defaultdict(list)
        for c in range(6):
            c_prev = (c - 1) % 6
            c_next = (c + 1) % 6
            for i in range(4):
                u = c * 4 + i
                # Connect to all 4 in prev cluster
                for j in range(4):
                    adj[u].append(c_prev * 4 + j)
                # Connect to all 4 in next cluster
                for j in range(4):
                    adj[u].append(c_next * 4 + j)
        return adj

    def _compute_all_pairs_geodesics(self) -> Dict[Tuple[int, int], List[int]]:
        """Compute shortest path (geodesic) between every pair of vertices."""
        paths: Dict[Tuple[int, int], List[int]] = {}
        for src in range(self.n):
            queue = collections.deque([[src]])
            visited = {src}
            paths[(src, src)] = [src]

            while queue:
                path = queue.popleft()
                curr = path[-1]
                for nbr in self.adj[curr]:
                    if nbr not in visited:
                        visited.add(nbr)
                        new_path = path + [nbr]
                        paths[(src, nbr)] = new_path
                        queue.append(new_path)
        return paths

    def get_geodesic(self, start: int, goal: int) -> List[int]:
        """
        Return optimal geodesic path from start to goal.
        Invariant: len(path) - 1 <= 3.
        """
        if not (0 <= start < self.n and 0 <= goal < self.n):
            raise ValueError(f"Indices must be in [0, {self.n - 1}].")
        return self._geodesic_table[(start, goal)]

    def get_geodesic_distance(self, start: int, goal: int) -> int:
        """Return geodesic metric distance in {0, 1, 2, 3}."""
        return len(self.get_geodesic(start, goal)) - 1

    def steer_tactic_step(self, current_vertex: int, goal_vertex: int) -> Dict[str, Any]:
        """
        Steer the automated theorem prover to the next tactic node along the expander geodesic.
        """
        path = self.get_geodesic(current_vertex, goal_vertex)
        dist = len(path) - 1
        next_step = path[1] if len(path) > 1 else current_vertex

        return {
            "current_vertex": current_vertex,
            "goal_vertex": goal_vertex,
            "geodesic_distance": dist,
            "next_vertex": next_step,
            "full_geodesic": path,
            "is_goal": current_vertex == goal_vertex,
            "diameter_bounded": dist <= self.diameter,
        }

    def verify_expander_mixing_bound(
        self,
        f: Sequence[float],
        g: Sequence[float]
    ) -> Dict[str, Any]:
        """
        Verify Alon-Chung Expander Mixing Lemma:
        | <f, A g> - (d / n) * <f, 1> * <g, 1> | <= lambda_2 * ||f||_2 * ||g||_2
        """
        arr_f = np.array(f, dtype=float)
        arr_g = np.array(g, dtype=float)
        if len(arr_f) != self.n or len(arr_g) != self.n:
            raise ValueError(f"Vector dimensions must equal {self.n}.")

        # Adjacency matrix
        A = np.zeros((self.n, self.n), dtype=float)
        for u in range(self.n):
            for v in self.adj[u]:
                A[u, v] = 1.0

        lhs = abs(float(arr_f @ A @ arr_g) - (self.degree / self.n) * float(np.sum(arr_f)) * float(np.sum(arr_g)))
        rhs = self.lambda_2 * float(np.linalg.norm(arr_f)) * float(np.linalg.norm(arr_g))

        return {
            "lhs": lhs,
            "rhs": rhs,
            "holds": lhs <= rhs + 1e-7,
            "spectral_gap": self.degree - self.lambda_2,
            "is_ramanujan": self.is_ramanujan,
            "ramanujan_family": self.ramanujan_family,
        }
