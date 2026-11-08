"""
Polynomial invariants of braid closures (QBX.md §18, Phase 7).

- kauffman_bracket(B):  ⟨\\hat B⟩ ∈ ℤ[A, A⁻¹], normalised so ⟨unknot⟩ = 1,
  computed exactly in the Temperley–Lieb algebra (linear in the number of
  crossings; kauffman_bracket_state_sum is the 2^m state-sum reference)
      ⟨σ_i⟩ = A·id + A⁻¹·e_i,   ⟨σ_i⁻¹⟩ = A⁻¹·id + A·e_i,
  each closed loop beyond the first contributing d = −A² − A⁻².
- jones_polynomial(B):  V(t) = (−A³)^{−w} ⟨\\hat B⟩ with A = t^{−1/4};
  returned as a Laurent polynomial in s = t^{1/2}.
- burau_matrix(B):      the reduced Burau representation, exact.
- alexander_polynomial(B): Δ(t) ≐ det(I − ρ̄(B)) · (1 − t)/(1 − tⁿ).

These are invariants of the *closure* (a link), hence also of the braid
group element and of Markov moves.
"""

from __future__ import annotations

from typing import List

from qbx_ir.algebra.invariants import writhe
from qbx_ir.algebra.laurent import Laurent, det, identity_matrix, matmul
from qbx_ir.core.braid import Braid

MAX_STATE_SUM_CROSSINGS = 22


def _count_loops(n: int, word, choices: int) -> int:
    """Number of loops in the closure of the TL-smoothed braid."""
    m = len(word)
    parent = list(range((m + 1) * n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for k, g in enumerate(word):
        i = g.index - 1  # 0-indexed left position
        cup = (choices >> k) & 1
        base0, base1 = k * n, (k + 1) * n
        for p in range(n):
            if p in (i, i + 1):
                continue
            union(base0 + p, base1 + p)
        if cup:
            union(base0 + i, base0 + i + 1)
            union(base1 + i, base1 + i + 1)
        else:
            union(base0 + i, base1 + i)
            union(base0 + i + 1, base1 + i + 1)
    for p in range(n):  # closure
        union(m * n + p, p)
    return len({find(x) for x in range((m + 1) * n)})


def kauffman_bracket_state_sum(braid: Braid) -> Laurent:
    """Kauffman bracket by the explicit 2^m state sum (reference; m ≤ MAX_STATE_SUM_CROSSINGS)."""
    word = braid.word
    m = len(word)
    if m > MAX_STATE_SUM_CROSSINGS:
        raise ValueError(f"state sum limited to {MAX_STATE_SUM_CROSSINGS} crossings")
    n = braid.strand_count
    d = Laurent({2: -1, -2: -1})
    d_powers = [Laurent.const(1)]
    total = Laurent()
    for choices in range(1 << m):
        a_exp = 0
        for k, g in enumerate(word):
            cup = (choices >> k) & 1
            # σ⁺: id ↦ A, cup ↦ A⁻¹ ; σ⁻: id ↦ A⁻¹, cup ↦ A
            if g.sign == 1:
                a_exp += -1 if cup else 1
            else:
                a_exp += 1 if cup else -1
        loops = _count_loops(n, word, choices)
        while len(d_powers) < loops:
            d_powers.append(d_powers[-1] * d)
        total = total + d_powers[loops - 1].shift(a_exp)
    return total


def _poly_add_shift(acc, poly, shift):
    for k, v in poly.items():
        k2 = k + shift
        c = acc.get(k2, 0) + v
        if c:
            acc[k2] = c
        else:
            acc.pop(k2, None)


def _times_d(poly):
    """poly · (−A² − A⁻²) on integer-coefficient dicts."""
    out = {}
    _poly_add_shift(out, {k: -v for k, v in poly.items()}, 2)
    _poly_add_shift(out, {k: -v for k, v in poly.items()}, -2)
    return out


def _closure_loops(n: int, match) -> int:
    """Loops of the closure of a Temperley–Lieb diagram (top j joined to bottom j)."""
    seen = [False] * (2 * n)
    loops = 0
    for start in range(2 * n):
        if seen[start]:
            continue
        loops += 1
        p = start
        while not seen[p]:
            seen[p] = True
            q = match[p]
            seen[q] = True
            p = q - n if q >= n else q + n   # closure edge
    return loops


def kauffman_bracket(braid: Braid) -> Laurent:
    """Kauffman bracket of the closure, in the variable A, ⟨O⟩ = 1.

    Computed exactly in the Temperley–Lieb algebra TL_n: the braid word is
    multiplied out with ⟨σ_i⟩ = A·id + A⁻¹·e_i and ⟨σ_i⁻¹⟩ = A⁻¹·id + A·e_i,
    keeping one integer Laurent coefficient per planar diagram (at most
    Catalan(n) of them), then closed up, each closed loop beyond the first
    contributing d = −A² − A⁻².  This is the same sum as
    :func:`kauffman_bracket_state_sum` (tests check they agree) but runs in
    time linear in the number of crossings instead of exponential.
    """
    n = braid.strand_count
    identity = tuple(list(range(n, 2 * n)) + list(range(n)))
    states = {identity: {0: 1}}
    for g in braid.word:
        i = g.index - 1
        a_id, a_cup = (1, -1) if g.sign == 1 else (-1, 1)
        new_states = {}
        for match, poly in states.items():
            acc = new_states.setdefault(match, {})
            _poly_add_shift(acc, poly, a_id)
            # match · e_i : cap the bottom points i, i+1 and add a new cup.
            bi, bj = n + i, n + i + 1
            x, y = match[bi], match[bj]
            m2 = list(match)
            if x == bj:
                coeff = _times_d(poly)
            else:
                m2[x], m2[y] = y, x
                coeff = poly
            m2[bi], m2[bj] = bj, bi
            key = tuple(m2)
            acc2 = new_states.setdefault(key, {})
            _poly_add_shift(acc2, coeff, a_cup)
        states = {k: v for k, v in new_states.items() if v}
    total = {}
    d_powers = [{0: 1}]
    for match, poly in states.items():
        loops = _closure_loops(n, match)
        while len(d_powers) < loops:
            d_powers.append(_times_d(d_powers[-1]))
        dp = d_powers[loops - 1]
        for k1, v1 in poly.items():
            for k2, v2 in dp.items():
                total[k1 + k2] = total.get(k1 + k2, 0) + v1 * v2
    return Laurent(total)


def jones_polynomial(braid: Braid) -> Laurent:
    """
    Jones polynomial of the closure as a Laurent polynomial in s = t^{1/2}
    (key k ↦ coefficient of t^{k/2}).  V(unknot) = 1.
    """
    w = writhe(braid)
    bracket = kauffman_bracket(braid)
    sign = -1 if w % 2 else 1
    f = bracket.shift(-3 * w) * sign  # (−A³)^{−w}⟨L⟩
    out = {}
    for k, v in f.items():
        if k % 2:
            raise AssertionError("odd A-exponent in Jones polynomial")
        out[-k // 2] = v  # A^k = t^{-k/4} = s^{-k/2}
    return Laurent(out)


def format_jones(v: Laurent) -> str:
    return v.format("t", half=True)


# ---------------------------------------------------------------------------
# Burau / Alexander
# ---------------------------------------------------------------------------

_T = Laurent.monomial(1)
_TINV = Laurent.monomial(-1)


def _reduced_burau_generator(n: int, i: int, sign: int) -> List[List[Laurent]]:
    m = n - 1
    mat = identity_matrix(m)
    r = i - 1  # row of generator i (0-indexed)
    row = [Laurent() for _ in range(m)]
    if sign == 1:
        if r - 1 >= 0:
            row[r - 1] = _T
        row[r] = -_T
        if r + 1 < m:
            row[r + 1] = Laurent.const(1)
    else:
        if r - 1 >= 0:
            row[r - 1] = Laurent.const(1)
        row[r] = -_TINV
        if r + 1 < m:
            row[r + 1] = _TINV
    mat[r] = row
    return mat


def burau_matrix(braid: Braid) -> List[List[Laurent]]:
    """Reduced Burau matrix ρ̄(B) ∈ GL_{n-1}(ℤ[t, t⁻¹]) (generators in word order)."""
    n = braid.strand_count
    mat = identity_matrix(n - 1)
    for g in braid.word:
        mat = matmul(mat, _reduced_burau_generator(n, g.index, g.sign))
    return mat


def alexander_polynomial(braid: Braid) -> Laurent:
    """
    Alexander polynomial of the closure, normalised up to ±t^k so that the
    lowest degree is 0 and the lowest coefficient is positive.
    """
    n = braid.strand_count
    if n == 1:
        return Laurent.const(1)
    b = burau_matrix(braid)
    i_minus = [[(Laurent.const(1) if r == c else Laurent()) - b[r][c] for c in range(n - 1)]
               for r in range(n - 1)]
    d = det(i_minus)
    denom = Laurent({k: 1 for k in range(n)})  # 1 + t + … + t^{n-1}
    return d.divmod_exact(denom).normalize_unit()


__all__ = [
    "kauffman_bracket",
    "jones_polynomial",
    "format_jones",
    "burau_matrix",
    "alexander_polynomial",
]
