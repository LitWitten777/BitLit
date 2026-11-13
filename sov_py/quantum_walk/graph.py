"""
Graph structure for the quantum-walk emulator.

The primary object is the 24-vertex connected component of the Cayley–Dickson
zero-divisor annihilation graph — the hexagonal blowup C₆[K̄₄] established
in HYP-007.

Vertices: (c, i) where c ∈ {0..5} is the cycle position and i ∈ {0..3} is
the twin-cluster member. Neighbors of (c, i) are (c±1 mod 6, j) for all
j ∈ {0..3} — so each vertex has 4 neighbors in each adjacent cluster,
8 total.

Spectral properties (HYP-002, HYP-005, HYP-051):
- 8-regular, bipartite
- λ₂ = 4, Ramanujan (4 < 2√7 ≈ 5.2915)
- Spectrum: {(±8)^1, (±4)^2, 0^18}
- Diameter 3, radius 3 (HYP-081)

The full 168-vertex graph is 7 disjoint copies of this component.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

import numpy as np


@dataclass(frozen=True)
class RamanujanGraph:
    """The 24-vertex connected component C₆[K̄₄] of the annihilation graph."""

    n_vertices: int = 24
    degree: int = 8
    cycle_length: int = 6
    cluster_size: int = 4

    def __post_init__(self) -> None:
        if self.n_vertices != self.cycle_length * self.cluster_size:
            raise ValueError("n_vertices must equal cycle_length * cluster_size")

    # -- Indexing ------------------------------------------------------------

    def index(self, c: int, i: int) -> int:
        """Map (cycle position, cluster member) to a linear vertex index."""
        if not (0 <= c < self.cycle_length and 0 <= i < self.cluster_size):
            raise IndexError(f"invalid vertex ({c}, {i})")
        return c * self.cluster_size + i

    def coords(self, v: int) -> tuple[int, int]:
        """Inverse of `index`."""
        if not (0 <= v < self.n_vertices):
            raise IndexError(f"invalid vertex index {v}")
        return divmod(v, self.cluster_size)

    # -- Adjacency -----------------------------------------------------------

    def neighbors(self, v: int) -> list[int]:
        """All 8 neighbors of vertex v, in a canonical order."""
        c, _ = self.coords(v)
        out: list[int] = []
        for dc in (-1, +1):
            cp = (c + dc) % self.cycle_length
            for j in range(self.cluster_size):
                out.append(self.index(cp, j))
        return out

    def neighbor(self, v: int, direction: int) -> int:
        """The neighbor of v in the given direction ∈ {0..7}.

        Directions 0..3 go "backward" (c-1); directions 4..7 go "forward" (c+1).
        """
        if not (0 <= direction < self.degree):
            raise IndexError(f"invalid direction {direction}")
        c, _ = self.coords(v)
        dc = -1 if direction < 4 else +1
        j = direction % 4
        cp = (c + dc) % self.cycle_length
        return self.index(cp, j)

    def reverse_direction(self, v: int, direction: int) -> int:
        """The direction from neighbor(v, direction) back to v.

        Guarantees that neighbor(neighbor(v, d), reverse_direction(v, d)) == v,
        making the quantum walk arc-shift operator an exact involution.
        """
        if not (0 <= direction < self.degree):
            raise IndexError(f"invalid direction {direction}")
        _, i = self.coords(v)
        return (4 + i) if direction < 4 else i

    def edges(self) -> Iterator[tuple[int, int]]:
        """Yield the 96 undirected edges (u < v)."""
        for u in range(self.n_vertices):
            for v in self.neighbors(u):
                if u < v:
                    yield (u, v)

    # -- Matrix representations ---------------------------------------------

    def adjacency_matrix(self) -> np.ndarray:
        """The 24×24 symmetric 0/1 adjacency matrix."""
        A = np.zeros((self.n_vertices, self.n_vertices), dtype=np.int8)
        for u, v in self.edges():
            A[u, v] = 1
            A[v, u] = 1
        return A

    def spectrum(self) -> np.ndarray:
        """Eigenvalues of the adjacency matrix, sorted descending."""
        A = self.adjacency_matrix().astype(float)
        return np.sort(np.linalg.eigvalsh(A))[::-1]

    # -- Verification --------------------------------------------------------

    def verify_invariants(self) -> dict:
        """Check the structural and spectral invariants from HYP-002/005/051."""
        A = self.adjacency_matrix()
        degrees = A.sum(axis=1)
        spectrum = self.spectrum()
        n_edges = A.sum() // 2

        lambda2 = float(spectrum[1])
        ramanujan_bound = 2.0 * np.sqrt(self.degree - 1)

        return {
            "n_vertices": self.n_vertices,
            "n_edges": int(n_edges),
            "degree_min": int(degrees.min()),
            "degree_max": int(degrees.max()),
            "is_regular": bool((degrees == self.degree).all()),
            "is_symmetric": bool((A == A.T).all()),
            "lambda_max": float(spectrum[0]),
            "lambda2": lambda2,
            "ramanujan_bound": float(ramanujan_bound),
            "is_ramanujan": bool(abs(lambda2) <= ramanujan_bound + 1e-9),
        }


def build_full_annihilation_graph() -> np.ndarray:
    """The full 168-vertex adjacency matrix (7 disjoint copies of C₆[K̄₄]).

    Returns a 168×168 symmetric 0/1 matrix. Used for the element-distinctness
    and multi-component walk experiments.
    """
    g = RamanujanGraph()
    A_component = g.adjacency_matrix()
    A = np.zeros((168, 168), dtype=np.int8)
    for block in range(7):
        offset = block * 24
        A[offset : offset + 24, offset : offset + 24] = A_component
    return A
