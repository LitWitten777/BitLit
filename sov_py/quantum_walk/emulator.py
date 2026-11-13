"""
Core discrete-time quantum-walk engine on Γ = C₆[K̄₄].

State space: H = ℂ²⁴ ⊗ ℂ⁸ (vertex ⊗ direction).
One-step operator: U = S · (I₂₄ ⊗ C), where
C : ℂ⁸ → ℂ⁸  is the coin,
S : |v, c⟩ → |n_c(v), rev_c(v)⟩  is the arc-reversal shift involution.

Both S and (I ⊗ C) are unitary; hence U is unitary.

Observables:
- Position distribution over vertices
- Mean squared displacement (ballistic vs. diffusive)
- Return probability (Pólya-type recurrence)
- Mixing time to uniform
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field

import numpy as np

from .coins import CoinName, coin_operator, is_unitary
from .graph import RamanujanGraph

# ----------------------------------------------------------------------------
# Shift operator
# ----------------------------------------------------------------------------


def build_shift(graph: RamanujanGraph) -> np.ndarray:
    """The shift S: |v, c⟩ → |n_c(v), rev_c(v)⟩ as an involution permutation matrix.

    Layout convention: basis index = v * d + c, where d = graph.degree.
    """
    n, d = graph.n_vertices, graph.degree
    S = np.zeros((n * d, n * d), dtype=complex)
    for v in range(n):
        for c in range(d):
            w = graph.neighbor(v, c)
            c_rev = graph.reverse_direction(v, c)
            S[w * d + c_rev, v * d + c] = 1.0
    return S


# ----------------------------------------------------------------------------
# Statistics container
# ----------------------------------------------------------------------------


@dataclass
class WalkStatistics:
    """Time-series of scalar observables from a single walk run."""

    steps: list[int] = field(default_factory=list)
    msd: list[float] = field(default_factory=list)
    return_prob: list[float] = field(default_factory=list)
    max_prob: list[float] = field(default_factory=list)

    def as_dict(self) -> dict:
        return {
            "steps": self.steps,
            "msd": self.msd,
            "return_prob": self.return_prob,
            "max_prob": self.max_prob,
        }


# ----------------------------------------------------------------------------
# Core walk engine
# ----------------------------------------------------------------------------


class QuantumWalk:
    """Single-particle discrete-time quantum walk on the Ramanujan graph.

    Parameters
    ----------
    graph : RamanujanGraph
        The graph to walk on (defaults to the 24-vertex component).
    coin : str
        Coin name: 'hadamard', 'grover', 'dft', or 'identity'.
    """

    def __init__(
        self,
        graph: RamanujanGraph | None = None,
        coin: CoinName = "grover",
    ) -> None:
        self.graph = graph or RamanujanGraph()
        self.n = self.graph.n_vertices
        self.d = self.graph.degree
        self.coin_name = coin

        C = coin_operator(coin, self.d)
        if not is_unitary(C, tol=1e-10):
            raise ValueError(f"coin '{coin}' is not unitary")
        self.C = C

        self.S = build_shift(self.graph)
        self.I_n = np.eye(self.n, dtype=complex)

        # U = S · (I_n ⊗ C)
        self.U = self.S @ np.kron(self.I_n, self.C)

        if not is_unitary(self.U, tol=1e-9):
            raise RuntimeError("walk operator U is not unitary — check construction")

    # -- State preparation ---------------------------------------------------

    def uniform_state(self) -> np.ndarray:
        """The uniform superposition over all (v, c) pairs."""
        psi = np.ones(self.n * self.d, dtype=complex)
        return psi / np.linalg.norm(psi)

    def localized_state(
        self, v: int, coin_state: np.ndarray | None = None
    ) -> np.ndarray:
        """A state localized at vertex v with the given coin amplitudes.

        Default coin state is the uniform superposition over directions.
        """
        if coin_state is None:
            coin_state = np.ones(self.d, dtype=complex) / np.sqrt(self.d)
        if coin_state.shape != (self.d,):
            raise ValueError(f"coin_state must have shape ({self.d},)")
        psi = np.zeros(self.n * self.d, dtype=complex)
        psi[v * self.d : (v + 1) * self.d] = coin_state
        return psi / np.linalg.norm(psi)

    # -- Time evolution ------------------------------------------------------

    def step(self, psi: np.ndarray) -> np.ndarray:
        """Apply one walk step."""
        return self.U @ psi

    def evolve(self, psi: np.ndarray, steps: int) -> np.ndarray:
        """Apply `steps` walk steps."""
        for _ in range(steps):
            psi = self.U @ psi
        return psi

    # -- Observables ---------------------------------------------------------

    def position_distribution(self, psi: np.ndarray) -> np.ndarray:
        """Marginal probability over vertices."""
        prob = np.abs(psi) ** 2
        return prob.reshape(self.n, self.d).sum(axis=1)

    def msd(self, psi: np.ndarray, origin: int = 0) -> float:
        """Mean squared graph distance from `origin` weighted by |ψ|².

        Uses BFS distances on the graph.
        """
        dists = self._bfs_distances(origin)
        p = self.position_distribution(psi)
        return float(np.sum(p * (dists**2)))

    def return_probability(self, psi: np.ndarray, origin: int = 0) -> float:
        """Probability mass at the origin vertex."""
        return float(self.position_distribution(psi)[origin])

    def _bfs_distances(self, source: int) -> np.ndarray:
        dist = np.full(self.n, np.inf)
        dist[source] = 0.0
        q: deque[int] = deque([source])
        while q:
            u = q.popleft()
            for w in self.graph.neighbors(u):
                if np.isinf(dist[w]):
                    dist[w] = dist[u] + 1.0
                    q.append(w)
        return dist

    # -- Time series ---------------------------------------------------------

    def run_statistics(
        self,
        steps: int,
        initial: np.ndarray | None = None,
        origin: int = 0,
    ) -> WalkStatistics:
        """Evolve and record observables at each step."""
        psi = initial if initial is not None else self.localized_state(origin)
        stats = WalkStatistics()
        for t in range(steps + 1):
            stats.steps.append(t)
            stats.msd.append(self.msd(psi, origin=origin))
            stats.return_prob.append(self.return_probability(psi, origin=origin))
            stats.max_prob.append(float(self.position_distribution(psi).max()))
            if t < steps:
                psi = self.step(psi)
        return stats
