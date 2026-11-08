"""Temperley–Lieb generators and Jones–Wenzl projectors on spin chains (exact arithmetic).

Companion to the Lean files ``QBX/Formal/MultiProver/TemperleyLieb*.lean``.  The Lean side
proves Wenzl's theorem for every ``n`` in any algebra and builds the 3-spin model; this module
computes the same objects on ``(Q^2)^{⊗n}`` for any ``n`` with exact rational arithmetic, so
the projectors of larger chains can be inspected.  Nothing here is a proof: the checks in
``check_wenzl`` are finite computations for the chosen ``q`` and ``n``.

Conventions match ``TemperleyLiebModel.lean``: the two-site generator is
``E = [[0,0,0,0],[0,q,-1,0],[0,-1,1/q,0],[0,0,0,0]]`` and ``e_i`` acts on sites ``i, i+1``;
the loop value is ``δ = q + 1/q`` and ``[k]`` are the Chebyshev quantum integers.
"""

from __future__ import annotations

from fractions import Fraction
from typing import List, Sequence

Matrix = List[List[Fraction]]


def identity(dim: int) -> Matrix:
    return [[Fraction(int(i == j)) for j in range(dim)] for i in range(dim)]


def zeros(dim: int) -> Matrix:
    return [[Fraction(0)] * dim for _ in range(dim)]


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    bt = list(zip(*b))
    return [[sum((x * y for x, y in zip(row, col)), Fraction(0)) for col in bt] for row in a]


def mat_add(a: Matrix, b: Matrix, s: Fraction = Fraction(1)) -> Matrix:
    """Return ``a + s * b``."""
    return [[x + s * y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def scale(s: Fraction, a: Matrix) -> Matrix:
    return [[s * x for x in row] for row in a]


def trace(a: Matrix) -> Fraction:
    return sum((a[i][i] for i in range(len(a))), Fraction(0))


def is_zero(a: Matrix) -> bool:
    return all(x == 0 for row in a for x in row)


def local_E(q: Fraction) -> Matrix:
    q = Fraction(q)
    return [
        [Fraction(0)] * 4,
        [Fraction(0), q, Fraction(-1), Fraction(0)],
        [Fraction(0), Fraction(-1), 1 / q, Fraction(0)],
        [Fraction(0)] * 4,
    ]


def tl_generator(q: Fraction, n_sites: int, i: int) -> Matrix:
    """``e_i`` on ``n_sites`` spins (sites ``i`` and ``i + 1``, 0-based; bit 0 = leftmost)."""
    if not 0 <= i < n_sites - 1:
        raise ValueError("generator index out of range")
    E = local_E(q)
    dim = 2 ** n_sites
    out = zeros(dim)
    shift = n_sites - i - 2  # position of the pair (i, i+1) from the right

    for x in range(dim):
        for y in range(dim):
            mask = ~(0b11 << shift)
            if (x & mask) != (y & mask):
                continue
            a = (x >> shift) & 0b11
            b = (y >> shift) & 0b11
            out[x][y] = E[a][b]
    return out


def q_int(delta: Fraction, k: int) -> Fraction:
    a, b = Fraction(0), Fraction(1)
    if k == 0:
        return a
    for _ in range(k - 1):
        a, b = b, delta * b - a
    return b


def jones_wenzl(q: Fraction, n_sites: int, k: int | None = None) -> Matrix:
    """``p_k`` (default ``k = n_sites``) acting on ``n_sites`` spins, by Wenzl's recursion."""
    q = Fraction(q)
    k = n_sites if k is None else k
    delta = q + 1 / q
    dim = 2 ** n_sites
    p = identity(dim)
    for m in range(k - 1):  # builds p_{m+2} from p_{m+1}
        num, den = q_int(delta, m + 1), q_int(delta, m + 2)
        if den == 0:
            raise ZeroDivisionError(f"[{m + 2}] = 0: the projector p_{m + 2} does not exist")
        e = tl_generator(q, n_sites, m)
        pep = mat_mul(mat_mul(p, e), p)
        p = mat_add(p, pep, -num / den)
    return p


def quantum_trace(q: Fraction, a: Matrix, n_sites: int) -> Fraction:
    """Unnormalised quantum trace ``tr(K^{⊗n} a)`` with ``K = diag(q, 1/q)``."""
    q = Fraction(q)
    total = Fraction(0)
    for x in range(2 ** n_sites):
        ones = bin(x).count("1")
        total += q ** (n_sites - ones) * (1 / q) ** ones * a[x][x]
    return total


def check_wenzl(q: Fraction, n_sites: int) -> dict:
    """Finite check of the Lean statements for one ``q`` and ``n``.

    Returns the TL relations, idempotence, the annihilation property, and the ordinary and
    quantum traces of ``p_n`` (expected ``n + 1`` and ``[n + 1]``).
    """
    q = Fraction(q)
    delta = q + 1 / q
    es = [tl_generator(q, n_sites, i) for i in range(n_sites - 1)]
    rel_sq = all(mat_mul(e, e) == scale(delta, e) for e in es)
    rel_braid = all(
        mat_mul(mat_mul(es[i], es[i + 1]), es[i]) == es[i]
        and mat_mul(mat_mul(es[i + 1], es[i]), es[i + 1]) == es[i + 1]
        for i in range(len(es) - 1)
    )
    rel_far = all(
        mat_mul(es[i], es[j]) == mat_mul(es[j], es[i])
        for i in range(len(es))
        for j in range(i + 2, len(es))
    )
    p = jones_wenzl(q, n_sites)
    return {
        "tl_relations": rel_sq and rel_braid and rel_far,
        "idempotent": mat_mul(p, p) == p,
        "killed": all(is_zero(mat_mul(e, p)) and is_zero(mat_mul(p, e)) for e in es),
        "trace": trace(p),
        "quantum_trace": quantum_trace(q, p, n_sites),
        "expected_quantum_trace": q_int(delta, n_sites + 1),
    }


def kauffman_generators(a: Fraction, n_sites: int) -> List[Matrix]:
    """Kauffman crossings ``g_i = a + a^{-1} e_i`` on the spin chain with ``q = -a^2``,
    so that ``δ = q + 1/q = -a^2 - a^{-2}`` (as in ``TLFamily.kauffman``)."""
    a = Fraction(a)
    q = -a * a
    dim = 2 ** n_sites
    return [
        mat_add(scale(a, identity(dim)), tl_generator(q, n_sites, i), 1 / a)
        for i in range(n_sites - 1)
    ]


def check_kauffman(a: Fraction, n_sites: int) -> dict:
    """Braid relations for the Kauffman crossings and absorption ``g_i p_n = a p_n``."""
    a = Fraction(a)
    gs = kauffman_generators(a, n_sites)
    braid = all(
        mat_mul(mat_mul(gs[i], gs[i + 1]), gs[i]) == mat_mul(mat_mul(gs[i + 1], gs[i]), gs[i + 1])
        for i in range(len(gs) - 1)
    )
    p = jones_wenzl(-a * a, n_sites)
    absorb = all(mat_mul(g, p) == scale(a, p) for g in gs)
    return {"braid": braid, "absorb": absorb}
