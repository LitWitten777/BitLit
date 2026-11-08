"""
Anyon models (QBX.md §9–§10, Phase 6): fusion rules, F-symbols, R-symbols.

Only multiplicity-free models are supported.  An F-matrix
``F(a, b, c, d)`` is the change of basis

    ((a ⊗ b) → e) ⊗ c → d      ↦      a ⊗ ((b ⊗ c) → f) → d

with rows indexed by the left intermediate ``e`` and columns by the right
intermediate ``f`` (both in the order returned by :meth:`intermediates`).
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass, field
from typing import Callable, Dict, FrozenSet, List, Tuple

import numpy as np

Label = str


@dataclass
class AnyonModel:
    name: str
    labels: Tuple[Label, ...]
    vacuum: Label
    fusion: Dict[Tuple[Label, Label], FrozenSet[Label]]
    quantum_dims: Dict[Label, float]
    r_symbols: Dict[Tuple[Label, Label, Label], complex]
    f_function: Callable[[Label, Label, Label, Label], np.ndarray] = field(repr=False)

    # ---- fusion -----------------------------------------------------------

    def fuse(self, a: Label, b: Label) -> FrozenSet[Label]:
        if a == self.vacuum:
            return frozenset({b})
        if b == self.vacuum:
            return frozenset({a})
        return self.fusion.get((a, b), self.fusion.get((b, a), frozenset()))

    def admissible(self, a: Label, b: Label, c: Label) -> bool:
        return c in self.fuse(a, b)

    def intermediates_left(self, a: Label, b: Label, c: Label, d: Label) -> List[Label]:
        return [e for e in self.labels if self.admissible(a, b, e) and self.admissible(e, c, d)]

    def intermediates_right(self, a: Label, b: Label, c: Label, d: Label) -> List[Label]:
        return [f for f in self.labels if self.admissible(b, c, f) and self.admissible(a, f, d)]

    def f_matrix(self, a: Label, b: Label, c: Label, d: Label) -> np.ndarray:
        left = self.intermediates_left(a, b, c, d)
        right = self.intermediates_right(a, b, c, d)
        if len(left) != len(right):
            raise ValueError("inconsistent fusion space")
        if len(left) == 1:
            return np.eye(1, dtype=np.complex128) * self.f_function(a, b, c, d)[0, 0]
        return np.asarray(self.f_function(a, b, c, d), dtype=np.complex128)

    def r_symbol(self, a: Label, b: Label, c: Label) -> complex:
        if a == self.vacuum or b == self.vacuum:
            return 1.0
        return self.r_symbols[(a, b, c)]

    def total_quantum_dimension(self) -> float:
        return math.sqrt(sum(d * d for d in self.quantum_dims.values()))

    # ---- consistency checks ---------------------------------------------

    def f_unitarity_residual(self) -> float:
        worst = 0.0
        for a in self.labels:
            for b in self.labels:
                for c in self.labels:
                    for d in self.labels:
                        if not self.intermediates_left(a, b, c, d):
                            continue
                        F = self.f_matrix(a, b, c, d)
                        worst = max(worst, float(np.abs(F.conj().T @ F - np.eye(len(F))).max()))
        return worst


# ---------------------------------------------------------------------------
# Concrete models
# ---------------------------------------------------------------------------

PHI = (1 + math.sqrt(5)) / 2


def _fib_f(a: Label, b: Label, c: Label, d: Label) -> np.ndarray:
    if (a, b, c, d) == ("τ", "τ", "τ", "τ"):
        return np.array(
            [[1 / PHI, 1 / math.sqrt(PHI)], [1 / math.sqrt(PHI), -1 / PHI]],
            dtype=np.complex128,
        )
    return np.eye(1, dtype=np.complex128)


def fibonacci_model() -> AnyonModel:
    """Fibonacci anyons: τ × τ = 1 + τ (labels ordered '1', 'τ')."""
    return AnyonModel(
        name="Fibonacci",
        labels=("1", "τ"),
        vacuum="1",
        fusion={("τ", "τ"): frozenset({"1", "τ"})},
        quantum_dims={"1": 1.0, "τ": PHI},
        r_symbols={
            ("τ", "τ", "1"): cmath.exp(-4j * math.pi / 5),
            ("τ", "τ", "τ"): cmath.exp(3j * math.pi / 5),
        },
        f_function=_fib_f,
    )


def _ising_f(a: Label, b: Label, c: Label, d: Label) -> np.ndarray:
    if (a, b, c, d) == ("σ", "σ", "σ", "σ"):
        return np.array([[1, 1], [1, -1]], dtype=np.complex128) / math.sqrt(2)
    if (a, b, c, d) in {("ψ", "σ", "ψ", "σ"), ("σ", "ψ", "σ", "ψ")}:
        return -np.eye(1, dtype=np.complex128)
    return np.eye(1, dtype=np.complex128)


def ising_model() -> AnyonModel:
    """Ising anyons: σ × σ = 1 + ψ, σ × ψ = σ, ψ × ψ = 1."""
    return AnyonModel(
        name="Ising",
        labels=("1", "σ", "ψ"),
        vacuum="1",
        fusion={
            ("σ", "σ"): frozenset({"1", "ψ"}),
            ("σ", "ψ"): frozenset({"σ"}),
            ("ψ", "ψ"): frozenset({"1"}),
        },
        quantum_dims={"1": 1.0, "σ": math.sqrt(2), "ψ": 1.0},
        r_symbols={
            ("σ", "σ", "1"): cmath.exp(-1j * math.pi / 8),
            ("σ", "σ", "ψ"): cmath.exp(3j * math.pi / 8),
            ("σ", "ψ", "σ"): -1j,
            ("ψ", "σ", "σ"): -1j,
            ("ψ", "ψ", "1"): -1.0,
        },
        f_function=_ising_f,
    )


# Toric-code anyons D(ℤ/2): labels (electric charge, magnetic flux) ∈ ℤ/2 × ℤ/2.
_TORIC_LABELS: Dict[Label, Tuple[int, int]] = {"1": (0, 0), "e": (1, 0), "m": (0, 1), "ε": (1, 1)}
_TORIC_BY_CHARGE = {v: k for k, v in _TORIC_LABELS.items()}


def _toric_fuse(a: Label, b: Label) -> Label:
    (ae, am), (be, bm) = _TORIC_LABELS[a], _TORIC_LABELS[b]
    return _TORIC_BY_CHARGE[((ae + be) % 2, (am + bm) % 2)]


def _toric_sign(a: Label, b: Label) -> float:
    """Bicharacter χ(a, b) = (-1)^(a_m · b_e)."""
    return -1.0 if _TORIC_LABELS[a][1] == 1 and _TORIC_LABELS[b][0] == 1 else 1.0


def _toric_f(a: Label, b: Label, c: Label, d: Label) -> np.ndarray:
    return np.eye(1, dtype=np.complex128)


def toric_code_model() -> AnyonModel:
    """Toric-code anyons 1, e, m, ε = e × m (WS9 step 10, register X-15).

    Fusion is addition in ℤ/2 × ℤ/2, every F-symbol is 1 and
    R^{ab}_{a+b} = (-1)^(a_m · b_e): e and m are bosons, ε is a fermion
    (R^{εε}_1 = -1) and e, m are mutual semions (R^{em} R^{me} = -1).  Lean:
    ``QBX/Formal/ToricAnyons.lean`` (``toric_pentagon``, ``toric_hexagon``,
    ``toric_hexagon_inv``, ``toric_spin_eps``, ``toric_monodromy_em``).
    """
    nontrivial = ("e", "m", "ε")
    return AnyonModel(
        name="ToricCode",
        labels=("1", "e", "m", "ε"),
        vacuum="1",
        fusion={(a, b): frozenset({_toric_fuse(a, b)}) for a in nontrivial for b in nontrivial},
        quantum_dims={a: 1.0 for a in _TORIC_LABELS},
        r_symbols={(a, b, _toric_fuse(a, b)): _toric_sign(a, b)
                   for a in nontrivial for b in nontrivial},
        f_function=_toric_f,
    )
