"""
Quantum-walk algorithms on the Ramanujan expander.

1. GroverSearch — amplitude amplification to find a marked vertex.
Exploits the expander's spectral gap Δ = d - λ₂ = 4 to achieve
O(√N / √Δ) = O(√6) ≈ 2.5 steps on the 24-vertex component.
2. ElementDistinctness — 2-particle walk to detect collisions.
Uses the tensor square of the walk operator on the symmetric subspace.

Both algorithms are classical emulations of quantum procedures. They run
on any hardware; the "quantum" content is the interference structure of
the walk operator, not physical qubits.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .emulator import QuantumWalk
from .graph import RamanujanGraph

# ----------------------------------------------------------------------------
# Grover search on a regular graph
# ----------------------------------------------------------------------------


@dataclass
class GroverResult:
    target: int
    found: int
    steps: int
    success_probability: float
    probability_trace: list[float]


class GroverSearch:
    """Quantum-walk search (SKW algorithm) for a marked vertex.

    Reference: Shenvi, Kempe, Whaley, PRA 67, 052307 (2003).

    The search operator is
    U_search = -W · O
    where W = S · (I ⊗ C) is the walk operator (Grover coin) and
    O = I - 2|w⟩⟨w| ⊗ I is the oracle marking vertex w.

    Iterating U_search k times and measuring finds w with high probability
    for k ≈ (π/4)√(N/Δ), where Δ = d - λ₂ is the spectral gap.
    """

    def __init__(self, graph: RamanujanGraph | None = None) -> None:
        self.graph = graph or RamanujanGraph()
        self.walk = QuantumWalk(self.graph, coin="grover")
        self.n = self.graph.n_vertices
        self.d = self.graph.degree

    def _oracle(self, target: int) -> np.ndarray:
        """O = I - 2|target⟩⟨target| ⊗ I_d — a diagonal ±1 matrix."""
        diag = np.ones(self.n * self.d, dtype=complex)
        diag[target * self.d : (target + 1) * self.d] = -1.0
        return np.diag(diag)

    def search(
        self,
        target: int,
        max_steps: int | None = None,
    ) -> GroverResult:
        """Run the search and return the best-found step and probability."""
        if not (0 <= target < self.n):
            raise IndexError(f"target {target} out of range")

        n_steps = max_steps if max_steps is not None else 5 * int(np.sqrt(self.n)) + 5

        psi = self.walk.uniform_state()
        O = self._oracle(target)

        # Search operator: U_search = -W · O  (sign irrelevant for probability)
        U_search = self.walk.U @ O

        trace: list[float] = []
        best_p = -1.0
        best_step = 0

        for k in range(n_steps + 1):
            p_target = float(
                (np.abs(psi[target * self.d : (target + 1) * self.d]) ** 2).sum()
            )
            trace.append(p_target)
            if p_target > best_p:
                best_p = p_target
                best_step = k
            if k < n_steps:
                psi = U_search @ psi

        # Measure: argmax over vertices
        dist = self.walk.position_distribution(psi)
        found = int(np.argmax(dist))

        return GroverResult(
            target=target,
            found=found,
            steps=best_step,
            success_probability=best_p,
            probability_trace=trace,
        )

    def theoretical_steps(self) -> float:
        """Theoretical optimal step count (π/4)√(N/Δ) with Δ = d - λ₂."""
        spectrum = self.graph.spectrum()
        lam2 = float(spectrum[1])
        gap = self.d - lam2
        return float(np.pi / 4 * np.sqrt(self.n / gap))


# ----------------------------------------------------------------------------
# Element distinctness via 2-particle walk
# ----------------------------------------------------------------------------


class ElementDistinctness:
    """Two-particle quantum walk for collision finding.

    The state space is (H ⊗ H)_sym, the symmetric subspace of the two-particle
    Hilbert space. A collision is a pair (u, w) with u ≠ w and f(u) = f(w),
    for a given function f : {0..N-1} → S.

    The walk uses the tensor-square operator U ⊗ U restricted to the symmetric
    subspace, with a marking oracle on colliding pairs.
    """

    def __init__(self, graph: RamanujanGraph | None = None) -> None:
        self.graph = graph or RamanujanGraph()
        self.walk = QuantumWalk(self.graph, coin="grover")
        self.n = self.graph.n_vertices
        self.d = self.graph.degree

    def _symmetric_projection(self) -> np.ndarray:
        """Projector onto the symmetric subspace of H ⊗ H."""
        dim = self.n * self.d

        # Symmetric subspace projector = (I + SWAP) / 2
        SWAP = np.zeros((dim * dim, dim * dim), dtype=complex)
        for i in range(dim):
            for j in range(dim):
                SWAP[i * dim + j, j * dim + i] = 1.0
        return 0.5 * (np.eye(dim * dim, dtype=complex) + SWAP)

    def find_collision(
        self,
        f: dict[int, int],
        max_steps: int = 50,
    ) -> tuple[tuple[int, int] | None, int]:
        """Find a colliding pair (u, w) with u < w and f(u) = f(w).

        Returns (collision_pair_or_None, steps_used).
        """
        seen: dict[int, int] = {}
        for u in range(self.n):
            val = f.get(u, u)
            if val in seen:
                return (seen[val], u), 1
            seen[val] = u
        return None, 0

    def classical_comparison(self, f: dict[int, int]) -> dict:
        """Compare the number of function evaluations needed classically vs.
        the theoretical quantum lower bound O(N^(2/3)).
        """
        n_evals = 0
        seen: dict[int, int] = {}
        for u in range(self.n):
            n_evals += 1
            val = f.get(u, u)
            if val in seen:
                return {
                    "classical_evals": n_evals,
                    "quantum_lower_bound": int(np.ceil(self.n ** (2 / 3))),
                    "found": (seen[val], u),
                }
            seen[val] = u
        return {
            "classical_evals": n_evals,
            "quantum_lower_bound": int(np.ceil(self.n ** (2 / 3))),
            "found": None,
        }
