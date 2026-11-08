"""
Garside left normal form — an exact solution of the word problem in B_n.

Every braid β ∈ B_n has a unique *left normal form*

    β = Δ^r · A_1 · A_2 ⋯ A_k

where Δ is the positive half twist, each A_j is a positive permutation braid
(a "simple" braid, 1 ≠ A_j ≠ Δ) and consecutive factors are *left-weighted*:
S(A_{j+1}) ⊆ F(A_j), with S/F the starting/finishing sets.  Two words
represent the same braid group element iff their left normal forms coincide
(Garside 1969; Elrifai–Morton 1994; Thurston, "Word Processing in Groups",
ch. 9).  This module is what makes WORD equality in QBX-IR exact.

Conventions
-----------
A simple braid is stored as a permutation ``p`` (tuple, 0-indexed) with
``p[k]`` = final position of the strand that starts at position ``k``.
Strands starting at positions a < b cross iff p[a] > p[b].
Words are read bottom → top, matching :class:`qbx_ir.core.braid.Braid`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Sequence, Tuple

from qbx_ir.core.braid import Braid

Perm = Tuple[int, ...]


# ---------------------------------------------------------------------------
# Permutation helpers
# ---------------------------------------------------------------------------

def _identity(n: int) -> Perm:
    return tuple(range(n))


def _delta(n: int) -> Perm:
    return tuple(n - 1 - k for k in range(n))


def _inverse(p: Perm) -> Perm:
    inv = [0] * len(p)
    for k, v in enumerate(p):
        inv[v] = k
    return tuple(inv)


def _then(p: Perm, q: Perm) -> Perm:
    """Permutation of the braid 'p first, then q'."""
    return tuple(q[p[k]] for k in range(len(p)))


def _swap(n: int, i: int) -> Perm:
    """Permutation of σ_i (1-indexed i): swaps positions i-1 and i."""
    s = list(range(n))
    s[i - 1], s[i] = s[i], s[i - 1]
    return tuple(s)


def _tau(p: Perm) -> Perm:
    """Conjugation by Δ (σ_i ↦ σ_{n-i}) on a simple braid."""
    n = len(p)
    return tuple(n - 1 - p[n - 1 - k] for k in range(n))


def starting_set(p: Perm) -> frozenset:
    """S(A) = {i : A = σ_i · (positive)} (1-indexed generators)."""
    return frozenset(i + 1 for i in range(len(p) - 1) if p[i] > p[i + 1])


def finishing_set(p: Perm) -> frozenset:
    """F(A) = {i : A = (positive) · σ_i} (1-indexed generators)."""
    q = _inverse(p)
    return frozenset(i + 1 for i in range(len(p) - 1) if q[i] > q[i + 1])


def simple_word(p: Perm) -> List[int]:
    """A positive word (short form) for the permutation braid of ``p``."""
    p = tuple(p)
    word: List[int] = []
    n = len(p)
    while True:
        descent = next((i for i in range(n - 1) if p[i] > p[i + 1]), None)
        if descent is None:
            return word
        i = descent + 1
        word.append(i)
        # A = σ_i · A'  ⇒  p = p' ∘ s_i  ⇒  p' = p ∘ s_i
        s = _swap(n, i)
        p = tuple(p[s[k]] for k in range(n))


# ---------------------------------------------------------------------------
# Normal form
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GarsideNormalForm:
    """Δ^power · factors[0] ⋯ factors[-1] (left-weighted, unique)."""

    strand_count: int
    power: int
    factors: Tuple[Perm, ...]

    @property
    def infimum(self) -> int:
        return self.power

    @property
    def supremum(self) -> int:
        return self.power + len(self.factors)

    @property
    def canonical_length(self) -> int:
        return len(self.factors)

    def to_short_form(self) -> List[int]:
        n = self.strand_count
        delta_word = simple_word(_delta(n))
        word: List[int] = []
        if self.power >= 0:
            word.extend(delta_word * self.power)
        else:
            inv = [-x for x in reversed(delta_word)]
            word.extend(inv * (-self.power))
        for f in self.factors:
            word.extend(simple_word(f))
        return word

    def to_braid(self, name: str = "NF") -> Braid:
        return Braid.from_short_form(self.strand_count, self.to_short_form(), name=name)

    def __str__(self) -> str:
        parts = [f"Δ^{self.power}"] + [
            "[" + " ".join(f"σ{i}" for i in simple_word(f)) + "]" for f in self.factors
        ]
        return " · ".join(parts)


def _make_left_weighted(factors: List[Perm]) -> List[Perm]:
    changed = True
    while changed:
        changed = False
        for j in range(len(factors) - 1):
            a, b = factors[j], factors[j + 1]
            n = len(a)
            while True:
                movable = starting_set(b) - finishing_set(a)
                if not movable:
                    break
                i = min(movable)
                s = _swap(n, i)
                a = _then(a, s)  # A ← A·σ_i
                b = tuple(b[s[k]] for k in range(n))  # B ← σ_i⁻¹·B
                changed = True
            factors[j], factors[j + 1] = a, b
    return factors


def left_normal_form_from_short(n: int, short: Sequence[int]) -> GarsideNormalForm:
    """Left normal form of the braid with the given short-form word."""
    if n < 1:
        raise ValueError("strand count must be ≥ 1")
    delta = _delta(n)
    ident = _identity(n)
    power = 0
    factors: List[Perm] = []
    for x in short:
        i = abs(x)
        if not 1 <= i < n:
            raise ValueError(f"generator {x} out of range for n={n}")
        if x > 0:
            factors.append(_swap(n, i))
        else:
            # σ_i⁻¹ = X_i · Δ⁻¹ with X_i = σ_i⁻¹Δ simple; push Δ⁻¹ to the front.
            x_i = tuple(delta[_swap(n, i)[k]] for k in range(n))
            factors = [_tau(f) for f in factors] + [_tau(x_i)]
            power -= 1
    factors = [f for f in factors if f != ident]
    factors = _make_left_weighted(factors)
    # Absorb leading Δ's; drop trailing identities.
    while factors and factors[0] == delta:
        factors.pop(0)
        power += 1
    while factors and factors[-1] == ident:
        factors.pop()
    if n == 1:
        power = 0  # B_1 is trivial; Δ_1 = 1
    return GarsideNormalForm(strand_count=n, power=power, factors=tuple(factors))


def left_normal_form(braid: Braid) -> GarsideNormalForm:
    return left_normal_form_from_short(braid.strand_count, braid.short_form())


def garside_normal_form(braid: Braid) -> Braid:
    """The braid rewritten in Garside left normal form (as a word)."""
    nf = left_normal_form(braid)
    return nf.to_braid(name=f"NF({braid.name})")


def braid_group_equal(b1: Braid, b2: Braid) -> bool:
    """Exact decision of b1 = b2 in the braid group B_n."""
    if b1.strand_count != b2.strand_count:
        return False
    return left_normal_form(b1) == left_normal_form(b2)


def is_trivial(braid: Braid) -> bool:
    """True iff the braid is the identity element of B_n."""
    nf = left_normal_form(braid)
    return nf.power == 0 and not nf.factors


__all__ = [
    "GarsideNormalForm",
    "left_normal_form",
    "left_normal_form_from_short",
    "garside_normal_form",
    "braid_group_equal",
    "is_trivial",
    "starting_set",
    "finishing_set",
    "simple_word",
]
