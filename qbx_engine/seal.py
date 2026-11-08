"""Runtime counterparts of the Phase 4 seal-lane theorems S3–S6.

Each function computes exactly what the matching Lean theorem is about, with exact arithmetic
(``fractions.Fraction``), so the engine and the proofs talk about the same objects:

* ``merge`` — S3 (``QBX/Formal/Seal/MergeOrder.lean``): merging lattice states with a join.
  The Lean theorem ``MergeTree.eval_eq_of_mem_iff`` says the result depends only on the *set*
  of merged states, so any delivery order, bracketing or duplication gives the same state.
* ``kleene`` / ``chaotic`` — S4 (``Seal/KleeneFinite.lean``): synchronous Kleene iteration
  from bottom reaches the least fixed point within ``card`` rounds
  (``iterate_card_bot_eq_lfp``); fair asynchronous iteration reaches the same point
  (``chaotic_eventually_lfp``).
* ``coded_encode`` / ``coded_decode`` — S5 (``Seal/CodedDecoding.lean``): a matrix polynomial
  with ``k`` coefficient matrices is recovered from any ``k`` evaluations by Lagrange
  interpolation (``coded_decode_of_workers``).
* ``final_chord`` — S6 (``Seal/FinalChord.lean``): cycle type, writhe and the characteristic
  polynomial of the reduced Burau matrix; equal braids give equal chords
  (``Word.chord_eq_of_eval_eq``).

No dependencies beyond the standard library.
"""

from __future__ import annotations

from fractions import Fraction
from functools import reduce
from typing import Callable, Hashable, Iterable, List, Sequence, Tuple

# ----------------------------------------------------------------------------------- S3


def merge(states: Iterable, join: Callable):
    """Merge a non-empty sequence of lattice states with ``join`` (left to right)."""
    states = list(states)
    if not states:
        raise ValueError("merge needs at least one state")
    return reduce(join, states)


def merge_tree(tree, join: Callable):
    """Evaluate a merge schedule: a ``Leaf`` is a state, a pair ``(left, right)`` is a merge."""
    if isinstance(tree, Leaf):
        return tree.value
    left, right = tree
    return join(merge_tree(left, join), merge_tree(right, join))


class Leaf:
    """A leaf of a merge schedule."""

    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value


# ----------------------------------------------------------------------------------- S4


def kleene(F: Callable, bottom, max_rounds: int):
    """Iterate ``F`` from ``bottom`` until a fixed point; return ``(point, rounds)``.

    On a finite lattice with ``max_rounds >= card`` this always terminates at the least fixed
    point (Lean: ``iterate_card_bot_eq_lfp``)."""
    x = bottom
    for r in range(max_rounds + 1):
        y = F(x)
        if y == x:
            return x, r
        x = y
    raise RuntimeError("no fixed point within max_rounds")


def chaotic(F: Callable, bottom: Tuple, schedule: Iterable[int], steps: int) -> Tuple:
    """Asynchronous iteration: at step ``k`` only component ``schedule[k]`` is recomputed."""
    x = tuple(bottom)
    it = iter(schedule)
    for _ in range(steps):
        i = next(it)
        fx = F(x)
        x = x[:i] + (fx[i],) + x[i + 1:]
    return x


# ----------------------------------------------------------------------------------- S5

Matrix = List[List[Fraction]]


def _mat_add(A: Matrix, B: Matrix) -> Matrix:
    return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def _mat_scale(c: Fraction, A: Matrix) -> Matrix:
    return [[c * a for a in row] for row in A]


def coded_encode(coeffs: Sequence[Matrix], x: Fraction) -> Matrix:
    """Evaluate ``P(x) = Σ_e coeffs[e] xᵉ`` (one worker's share)."""
    rows, cols = len(coeffs[0]), len(coeffs[0][0])
    acc = [[Fraction(0)] * cols for _ in range(rows)]
    for c in reversed(coeffs):  # Horner
        acc = _mat_add(_mat_scale(Fraction(x), acc), [[Fraction(v) for v in r] for r in c])
    return acc


def coded_decode(responses: Sequence[Tuple[Fraction, Matrix]], k: int) -> List[Matrix]:
    """Recover the ``k`` coefficient matrices from any ``k`` responses ``(x, P(x))``
    with distinct ``x`` (Lagrange interpolation, entrywise)."""
    pts = list(responses)[:k]
    if len(pts) < k:
        raise ValueError("need at least k responses (Lean: coded_insufficient)")
    xs = [Fraction(x) for x, _ in pts]
    if len(set(xs)) != k:
        raise ValueError("evaluation points must be distinct")
    rows, cols = len(pts[0][1]), len(pts[0][1][0])
    out = [[[Fraction(0)] * cols for _ in range(rows)] for _ in range(k)]
    for j, (xj, Mj) in enumerate(zip(xs, (m for _, m in pts))):
        # basis polynomial ℓ_j(X) = Π_{m≠j} (X − x_m)/(x_j − x_m), as coefficients
        poly = [Fraction(1)]
        denom = Fraction(1)
        for m, xm in enumerate(xs):
            if m == j:
                continue
            poly = [Fraction(0)] + poly  # multiply by X
            for e in range(len(poly) - 1):
                poly[e] -= xm * poly[e + 1]
            denom *= xj - xm
        for e in range(k):
            c = poly[e] / denom
            for r in range(rows):
                for s in range(cols):
                    out[e][r][s] += c * Fraction(Mj[r][s])
    return out


# ----------------------------------------------------------------------------------- S6

Letter = Tuple[int, bool]  # (0-based generator index i, positive?)


def _perm_of_word(word: Sequence[Letter], n: int) -> List[int]:
    p = list(range(n))
    for i, _ in word:
        p[i], p[i + 1] = p[i + 1], p[i]
    return p


def cycle_type(perm: Sequence[int]) -> Tuple[int, ...]:
    """Cycle lengths ≥ 2, sorted (Mathlib's ``cycleType``)."""
    seen, out = set(), []
    for s in range(len(perm)):
        if s in seen:
            continue
        L, x = 0, s
        while x not in seen:
            seen.add(x)
            x = perm[x]
            L += 1
        if L >= 2:
            out.append(L)
    return tuple(sorted(out))


def burau(word: Sequence[Letter], n: int, t: Fraction) -> Matrix:
    """Reduced Burau matrix, letter by letter in word order (``Word.burau`` in Lean)."""
    d = n - 1
    t = Fraction(t)
    M = [[Fraction(int(r == c)) for c in range(d)] for r in range(d)]
    for i, pos in word:
        G = [[Fraction(int(r == c)) for c in range(d)] for r in range(d)]
        r = i
        G[r] = [Fraction(0)] * d
        vals = (t, -t, Fraction(1)) if pos else (Fraction(1), -1 / t, 1 / t)
        for off, v in zip((-1, 0, 1), vals):
            c = r + off
            if 0 <= c < d:
                G[r][c] = v
        M = [[sum(M[a][b] * G[b][c] for b in range(d)) for c in range(d)] for a in range(d)]
    return M


def charpoly(M: Matrix) -> Tuple[Fraction, ...]:
    """Characteristic polynomial ``det(X − M)``, coefficients from degree 0 upward
    (Faddeev–LeVerrier, exact)."""
    d = len(M)
    if d == 0:
        return (Fraction(1),)
    coeffs = [Fraction(0)] * (d + 1)
    coeffs[d] = Fraction(1)
    Mk = [[Fraction(0)] * d for _ in range(d)]
    I = [[Fraction(int(r == c)) for c in range(d)] for r in range(d)]
    for k in range(1, d + 1):
        Mk = [[sum(M[a][b] * (Mk[b][c] + coeffs[d - k + 1] * I[b][c]) for b in range(d))
               for c in range(d)] for a in range(d)]
        coeffs[d - k] = -sum(Mk[a][a] for a in range(d)) / k
    return tuple(coeffs)


def final_chord(word: Sequence[Letter], n: int, t: Fraction = Fraction(2)):
    """``(cycle type, writhe, Burau characteristic polynomial)`` — Lean ``Word.chord``."""
    writhe = sum(1 if pos else -1 for _, pos in word)
    return (cycle_type(_perm_of_word(word, n)), writhe, charpoly(burau(word, n, t)))
