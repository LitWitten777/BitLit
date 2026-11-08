"""Braids with braids.

Braid words are lists of signed generator indices (+i = sigma_i, -i = its
inverse, 1-based, as in `qbx_micro.braid`).  Operations on two braids:

  tensor(m, u, n, v)    u on the lower m strands, v on the upper n strands
  compose(u, v)         u then v (same strands)
  conjugate(h, g)       h g h^-1: braiding g by h
  commutator(u, v)      u v u^-1 v^-1

Lean (`QBX/Formal/Engine/BraidBraid.lean`):

  layers_commute        tensor(m, u, n, []) and tensor(m, [], n, v) commute, for all braids
  tensor_mul            (u1 (x) v1)(u2 (x) v2) = (u1 u2) (x) (v1 v2)   (interchange law)
  writhe_tensor         writhe adds
  perm_embedAt_fixes    a braid on a block of strands only permutes that block
  braid_acts_on_braid   conjugation keeps closure components and linking numbers

`checks` re-derives these on examples with the invariants of `qbx_micro.braid`
(permutation, writhe, linking numbers, Burau matrix at a random point mod p).
Agreement of these invariants is evidence, not a proof, that two words are the same
braid; the Lean theorems are the proof.
"""

import random

try:
    from qbx_micro import braid as _braid
except ImportError:  # pragma: no cover
    _braid = None


def inverse(w):
    return [-x for x in reversed(w)]


def compose(u, v):
    return list(u) + list(v)


def shift(w, k):
    return [x + k if x > 0 else x - k for x in w]


def tensor(m, u, n, v):
    """u on strands 1..m, v on strands m+1..m+n; returns (strand count, word)."""
    return m + n, list(u) + shift(v, m)


def conjugate(h, g):
    return list(h) + list(g) + inverse(h)


def commutator(u, v):
    return list(u) + list(v) + inverse(u) + inverse(v)


def writhe(w):
    return sum(1 if x > 0 else -1 for x in w)


def perm(n, w):
    if _braid is not None:
        return list(_braid.fold(n, w))
    p = list(range(n))
    for x in w:
        i = abs(x) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    return p


def invariants(n, w, t=None, p=2305843009213693951):
    out = {"perm": perm(n, w), "writhe": writhe(w)}
    if _braid is not None and n >= 2:
        out["link"] = _braid.link(n, w)
        if t is not None:
            out["burau"] = _braid.burau_mod(n, w, t, p)
    return out


def same_invariants(n, u, v, t=None):
    return invariants(n, u, t) == invariants(n, v, t)


def checks(trials=20, seed=3):
    rng = random.Random(seed)
    t = rng.randrange(2, 10 ** 9)
    ok = {"layers_commute": True, "interchange": True, "writhe_adds": True,
          "block_permutation": True, "conjugation_invariants": True}

    def rw(n, L):
        return [rng.choice([1, -1]) * rng.randint(1, n - 1) for _ in range(L)]

    for _ in range(trials):
        m, n = rng.randint(2, 4), rng.randint(2, 4)
        u1, u2, v1, v2 = rw(m, 5), rw(m, 4), rw(n, 5), rw(n, 3)
        N, low = tensor(m, u1, n, [])
        _, high = tensor(m, [], n, v1)
        if not same_invariants(N, low + high, high + low, t):
            ok["layers_commute"] = False
        _, a = tensor(m, u1, n, v1)
        _, b = tensor(m, u2, n, v2)
        _, c = tensor(m, u1 + u2, n, v1 + v2)
        if not same_invariants(N, a + b, c, t):
            ok["interchange"] = False
        if writhe(a) != writhe(u1) + writhe(v1):
            ok["writhe_adds"] = False
        pr = perm(N, a)
        if any(pr[i] >= m for i in range(m)) or any(pr[i] < m for i in range(m, N)):
            ok["block_permutation"] = False
        h, g = rw(N, 4), rw(N, 6)
        if _braid is not None:
            k1, k2 = _braid.link(N, conjugate(h, g)), _braid.link(N, g)
            # number of components and the multiset of linking numbers agree
            if k1[0] != k2[0] or sorted(k1[1]) != sorted(k2[1]):
                ok["conjugation_invariants"] = False
    return ok


def interact(texts_a, texts_b, mode="written"):
    """Two bundles of texts as two braids, side by side and braided through each other."""
    from . import braidlines
    wa, _ = braidlines.braid_word(texts_a, mode) if len(texts_a) > 1 else ([], None)
    wb, _ = braidlines.braid_word(texts_b, mode) if len(texts_b) > 1 else ([], None)
    m, n = len(texts_a), len(texts_b)
    N, side = tensor(m, wa, n, wb)
    # braid the side-by-side pair by a double crossing at the gap between the bundles
    gap = [m] * 2
    through = conjugate(gap, side)
    return {"strands": N, "a": {"strands": m, "word": wa}, "b": {"strands": n, "word": wb},
            "side_by_side": side, "side_by_side_invariants": invariants(N, side),
            "b_braided_through_a": through, "through_invariants": invariants(N, through)}
