"""
Structural braid maps mirrored from the Lean library ``QBX/Formal``.

Every function here is the executable counterpart of a definition that is
machine-checked in Lean; the docstrings name the Lean declaration and the
theorem that the tests in ``tests/qbx_ir/test_structural.py`` use as an oracle.

- :func:`torus_matrix` — ``b3ToSL2 : B₃ →* SL(2, ℤ)``
  (``QBX/Formal/Connections/BraidTorusSL2.lean``).
- :func:`braid_hash`, :func:`encode_bits`, :func:`decode_hash` — the Cayley
  hash of ``QBX/Formal/BraidHash.lean`` (bits ↦ σ₁, σ₂⁻¹).  The hash is
  injective (``braidHash_injective``); :func:`decode_hash` is the constructive
  inverse (Euclid / Stern–Brocot descent).
- :func:`free_hash`, :func:`free_hash_braid` — the hash on reduced group
  words over {σ₁^{±2}, σ₂^{∓2}} (``QBX/Formal/BraidFreeHash.lean``), injective
  by Sanov's theorem (``freeHash_injective``).
- :func:`tangle_fraction` — rational-tangle action
  (``QBX/Formal/Bio/RationalTangles.lean``).
- :func:`fox_colourings` — Fox p-colourings of a braid closure
  (``QBX/Notes/TernaryBraids.lean`` for n = 3, p = 3; here for any n, p).
- :func:`crossing_change`, :func:`crossing_strands`, :func:`total_linking`,
  :func:`decatenation_lower_bound` — crossing changes / strand passage and the
  decatenation bound (``QBX/Formal/Bio/Catenanes.lean``).
- :func:`decatenate` — an explicit shortest decatenation, following the proof of
  ``sharp_decatenation`` (``QBX/Formal/Bio/Catenanes.lean``).
- :func:`carry`, :func:`carry_cocycle` — the generator of H³(ℤ/n, U(1))
  (``QBX/Formal/Hebrew/CyclicGenerator.lean``).
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Iterable, List, Sequence, Tuple

from qbx_ir.algebra.invariants import closure_components, linking_matrix
from qbx_ir.core.braid import Braid

Mat2 = Tuple[Tuple[int, int], Tuple[int, int]]

IDENTITY: Mat2 = ((1, 0), (0, 1))
MAT_A: Mat2 = ((1, 1), (0, 1))  # image of σ₁
MAT_L: Mat2 = ((1, 0), (-1, 1))  # image of σ₂
MAT_B: Mat2 = ((1, 0), (1, 1))  # image of σ₂⁻¹


def mat_mul(x: Mat2, y: Mat2) -> Mat2:
    return (
        (x[0][0] * y[0][0] + x[0][1] * y[1][0], x[0][0] * y[0][1] + x[0][1] * y[1][1]),
        (x[1][0] * y[0][0] + x[1][1] * y[1][0], x[1][0] * y[0][1] + x[1][1] * y[1][1]),
    )


def mat_inv(x: Mat2) -> Mat2:
    """Inverse of a determinant-1 integer matrix."""
    (a, b), (c, d) = x
    return ((d, -b), (-c, a))


# ---------------------------------------------------------------------------
# B₃ → SL(2, ℤ)
# ---------------------------------------------------------------------------


def torus_matrix(braid: Braid) -> Mat2:
    """
    Image of a 3-strand braid under ``b3ToSL2`` (σ₁ ↦ [[1,1],[0,1]],
    σ₂ ↦ [[1,0],[-1,1]]); the word is multiplied left to right.
    """
    if braid.strand_count != 3:
        raise ValueError("torus_matrix is defined on 3-strand braids")
    m = IDENTITY
    for g in braid.word:
        base = MAT_A if g.index == 1 else MAT_L
        m = mat_mul(m, base if g.sign > 0 else mat_inv(base))
    return m


# ---------------------------------------------------------------------------
# The braid hash
# ---------------------------------------------------------------------------


def encode_bits(bits: Iterable[int], name: str = "H") -> Braid:
    """Bit 0 ↦ σ₁, bit 1 ↦ σ₂⁻¹ (Lean ``BraidHash.encode``)."""
    return Braid.from_short_form(3, [-2 if b else 1 for b in bits], name=name)


def braid_hash(bits: Iterable[int]) -> Mat2:
    """
    Lean ``BraidHash.braidHash``: product of A = [[1,1],[0,1]] (bit 0) and
    B = [[1,0],[1,1]] (bit 1).  Equals ``torus_matrix(encode_bits(bits))``.
    """
    m = IDENTITY
    for b in bits:
        m = mat_mul(m, MAT_B if b else MAT_A)
    return m


def decode_hash(m: Mat2) -> List[int]:
    """
    Recover the bit string from its hash (constructive form of
    ``braidHash_injective``).  Raises ``ValueError`` if ``m`` is not a hash.

    If ``m = A·m'`` the first row dominates the second; if ``m = B·m'`` the
    second row dominates the first (``matA_mul_ne_matB_mul``).  Each step
    strictly decreases the entry sum, so the descent terminates.
    """
    bits: List[int] = []
    (a, b), (c, d) = m
    if a * d - b * c != 1 or min(a, b, c, d) < 0:
        raise ValueError("not a braid hash: need det 1 and non-negative entries")
    while (a, b, c, d) != (1, 0, 0, 1):
        if a >= c and b >= d:  # m = A · m'
            bits.append(0)
            a, b = a - c, b - d
        elif c >= a and d >= b:  # m = B · m'
            bits.append(1)
            c, d = c - a, d - b
        else:
            raise ValueError("not a braid hash")
    return bits


def free_hash(word: Iterable[int]) -> Mat2:
    """
    Hash of a group word over {σ₁^{±2}, σ₂^{∓2}} (Lean ``FreeHash.freeHash``):
    letter ``+1``/``-1`` is σ₁^{±2} ↦ [[1,±2],[0,1]], letter ``+2``/``-2`` is
    σ₂^{∓2} ↦ [[1,0],[±2,1]].  Injective on reduced words (Sanov's theorem,
    ``freeHash_injective``).
    """
    mats = {1: ((1, 2), (0, 1)), -1: ((1, -2), (0, 1)), 2: ((1, 0), (2, 1)), -2: ((1, 0), (-2, 1))}
    m = IDENTITY
    for letter in word:
        m = mat_mul(m, mats[letter])
    return m


def free_hash_braid(word: Iterable[int], name: str = "F") -> Braid:
    """The braid σ₁^{±2}, σ₂^{∓2} word whose torus matrix is :func:`free_hash`."""
    short: List[int] = []
    for letter in word:
        short += [letter, letter] if abs(letter) == 1 else [-letter, -letter]
    return Braid.from_short_form(3, short, name=name)


def pos_hash(bits: Iterable[int]) -> Mat2:
    """Bits ↦ σ₁, σ₂ (both positive): Lean ``posHash`` — not injective."""
    m = IDENTITY
    for b in bits:
        m = mat_mul(m, MAT_L if b else MAT_A)
    return m


# ---------------------------------------------------------------------------
# Rational tangles
# ---------------------------------------------------------------------------


def tangle_fraction(braid: Braid, v: Tuple[int, int] = (0, 1)) -> Tuple[int, int]:
    """
    Lean ``RationalTangles.act``: the column vector ``torus_matrix(braid) · v``.
    Starting from the zero tangle ``(0, 1)`` this gives the numerator and
    denominator ``(p, q)`` of the tangle fraction; it is coprime whenever ``v``
    is (``primitive_act``).
    """
    (a, b), (c, d) = torus_matrix(braid)
    return (a * v[0] + b * v[1], c * v[0] + d * v[1])


def tangle_parity(braid: Braid, v: Tuple[int, int] = (0, 1)) -> Tuple[int, int]:
    """``(p mod 2, q mod 2)``; depends only on the strand permutation."""
    p, q = tangle_fraction(braid, v)
    return (p % 2, q % 2)


# ---------------------------------------------------------------------------
# Fox colourings
# ---------------------------------------------------------------------------


def _fox_fwd(i: int, x: List[int], p: int) -> List[int]:
    """σ_i (1-indexed): over-strand label moves left, under-label a ↦ 2b − a."""
    y = list(x)
    a, b = x[i - 1], x[i]
    y[i - 1] = b
    y[i] = (2 * b - a) % p
    return y


def _fox_bwd(i: int, x: List[int], p: int) -> List[int]:
    y = list(x)
    a, b = x[i - 1], x[i]
    y[i - 1] = (2 * a - b) % p
    y[i] = a
    return y


def fox_action(braid: Braid, x: Sequence[int], p: int = 3) -> List[int]:
    """
    The action of the braid on labellings in (ℤ/p)ⁿ, with Lean's convention
    ``foxHom (g * h) = foxHom g * foxHom h`` (so the last letter acts first).
    """
    y = [v % p for v in x]
    for g in reversed(braid.word):
        y = _fox_fwd(g.index, y, p) if g.sign > 0 else _fox_bwd(g.index, y, p)
    return y


def fox_colourings(braid: Braid, p: int = 3) -> int:
    """
    Number of Fox p-colourings of the closure: labellings fixed by the braid
    (Lean ``colourings`` for n = 3, p = 3).  Brute force over pⁿ labellings.
    """
    n = braid.strand_count
    return sum(
        1 for x in product(range(p), repeat=n) if fox_action(braid, list(x), p) == list(x)
    )


def is_tricolourable(braid: Braid) -> bool:
    """Has a non-constant 3-colouring (Lean ``Tricolourable``)."""
    return fox_colourings(braid, 3) > 3


def torus_braid_3(q: int) -> Braid:
    """``(σ₁σ₂)^q`` on 3 strands, closing to the torus link T(3, q)."""
    return Braid.from_short_form(3, [1, 2] * q, name=f"T(3,{q})")


# ---------------------------------------------------------------------------
# Crossing changes and the decatenation bound
# ---------------------------------------------------------------------------


def crossing_change(braid: Braid, k: int) -> Braid:
    """Flip the sign of the k-th letter (0-indexed): ``a·σᵢ^{±1}·b ↦ a·σᵢ^{∓1}·b``."""
    word = list(braid.word)
    word[k] = word[k].inverse()
    return Braid(strand_count=braid.strand_count, word=tuple(word), strands=braid.strands,
                 name=f"{braid.name}~{k}")


def crossing_strands(braid: Braid, k: int) -> Tuple[int, int]:
    """
    The two strands (initial positions, 1-indexed) meeting at letter k —
    Lean ``ccLeft``/``ccRight``.
    """
    c = braid.crossings()[k]
    return (c.left_strand_id, c.right_strand_id)


def total_linking(braid: Braid) -> int:
    """
    Lean ``totalLinking``: Σ over *ordered* pairs of distinct closure
    components of |lk| (so twice the sum over unordered pairs).
    """
    return 2 * sum(abs(v) for v in linking_matrix(braid).values())


def decatenation_lower_bound(braid: Braid) -> int:
    """
    Minimum number of crossing changes (type II topoisomerase strand passages)
    needed to make all components pairwise homologically unlinked is at least
    Σ_{a<b} |lk(C_a, C_b)| (Lean ``decatenation_lower_bound``); sharp for the
    two-ring catenane σ₁^{2m} (``catenane_decatenation``).
    """
    return total_linking(braid) // 2


def decatenate(braid: Braid) -> Tuple[Braid, List[int]]:
    """
    A shortest sequence of strand passages removing all pairwise linking —
    the construction in the proof of Lean ``sharp_decatenation``.

    While two components C ≠ D have lk(C, D) ≠ 0, pick a crossing between C
    and D whose sign equals the sign of lk(C, D) (one exists:
    ``exists_pos_crossing`` / ``exists_neg_crossing``) and flip it; this lowers
    ``total_linking`` by exactly 2 (``totalLinking_step``).  Returns the final
    braid and the flipped letter positions; their number is
    ``total_linking(braid) // 2``, which is optimal by
    ``decatenation_lower_bound`` (``decatenation_minimum``).
    """
    flips: List[int] = []
    b = braid
    while True:
        idx = component_index(b)
        lks = linking_matrix(b)
        target = next(((pair, v) for pair, v in sorted(lks.items()) if v != 0), None)
        if target is None:
            return b, flips
        (ca, cb), v = target
        sign = 1 if v > 0 else -1
        for k, c in enumerate(b.crossings()):
            if c.sign == sign and {idx[c.left_strand_id], idx[c.right_strand_id]} == {ca, cb}:
                b = crossing_change(b, k)
                flips.append(k)
                break
        else:  # pragma: no cover - excluded by exists_pos_crossing / exists_neg_crossing
            raise AssertionError("no crossing of the required sign between linked components")


def component_index(braid: Braid) -> dict:
    return {s: idx for idx, comp in enumerate(closure_components(braid)) for s in comp}


# ---------------------------------------------------------------------------
# The carry cocycle: generator of H³(ℤ/n, U(1))
# ---------------------------------------------------------------------------


def carry(n: int, b: int, c: int) -> int:
    """Carry digit of b + c in base n (b, c reduced mod n)."""
    return 0 if (b % n) + (c % n) < n else 1


def carry_cocycle(n: int, a: int, b: int, c: int, m: int = 1) -> Fraction:
    """
    ``m · ω(a, b, c) = m · a · carry(b, c) / n`` in ℝ/ℤ, returned as a
    Fraction in [0, 1).  ω is the generator of H³(ℤ/n, U(1)) (Lean
    ``genCocycle``); the multiple ``m·ω`` is a coboundary iff n | m
    (``genCocycle_order``).
    """
    return Fraction(m * (a % n) * carry(n, b, c), n) % 1


def cobdry3(f, n: int, a: int, b: int, c: int, d: int) -> Fraction:
    """Inhomogeneous coboundary of a 3-cochain on ℤ/n, values in ℝ/ℤ."""
    return (f(b, c, d) - f((a + b) % n, c, d) + f(a, (b + c) % n, d)
            - f(a, b, (c + d) % n) + f(a, b, c)) % 1


def telescope_invariant(f, n: int, g: int = 1) -> Fraction:
    """
    Σ_k f(g, k, g) in ℝ/ℤ.  Vanishes on every coboundary
    (Lean ``sum_cobdry2_telescope``); equals m/n on m·ω.
    """
    return sum((f(g, k, g) for k in range(n)), Fraction(0)) % 1


def sliding_phase(f, xs) -> Fraction:
    """
    The "cumulative 3-cocycle phase" Σᵢ f(xᵢ, xᵢ₊₁, xᵢ₊₂) over all windows of three
    consecutive symbols, in ℝ/ℤ (Lean ``QBX.Forensics.GenesisBlock.slidingPhase``).
    For the carry cocycle the result always lies in (1/n)ℤ/ℤ
    (``nsmul_slidingPhase_genCocycle``) and depends on the cocycle representative, not only on
    its class (``slidingPhase_not_cohomology_invariant``).
    """
    xs = list(xs)
    return sum((f(xs[i], xs[i + 1], xs[i + 2]) for i in range(len(xs) - 2)), Fraction(0)) % 1
