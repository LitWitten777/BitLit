"""Which structure is the model?  The 6-cube Q6, E8, E8+E8+E8 and the Leech lattice side by side.

Everything here is exact integer arithmetic; the Lean companion is
`sovereign/Sovereign/Organism/HypercubeLattices.lean` (Q6 shells and squares, Leech minimum norm,
Leech is not E8^3).  Conventions:

* E8 in doubled coordinates (as `Sovereign.Steering.E8`): all coordinates even or all odd, sum = 0 mod 4;
  true norm = (x.x) / 4.
* Leech in Conway's coordinates scaled by sqrt 8, built on the same extended Golay code as
  `QEC.golay24`; true norm = (x.x) / 8.
* "Shell n" of a lattice = the vectors of true norm 2n; the theta series lists the shell sizes.
"""
from itertools import combinations, product
from math import comb


# --------------------------------------------------------------------------- Q6, the model itself
def q6_shells(source=0):
    """Number of cells at Hamming distance k = 0..6 from `source` (the same for every source)."""
    out = [0] * 7
    for c in range(64):
        out[bin(source ^ c).count("1")] += 1
    return out


def q6_squares():
    """Square faces of Q6: (base cell, i, j) with i < j and bits i, j of the base cell zero."""
    return [(v, i, j) for v in range(64) for i in range(6) for j in range(i + 1, 6)
            if not (v >> i) & 1 and not (v >> j) & 1]


# --------------------------------------------------------------------------- the Golay code
QR = [1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0]


def _golay_b(i, j):
    if i == 0:
        return 0 if j == 0 else 1
    if j == 0:
        return 1
    return QR[(j - 1 + i - 1) % 11]


GOLAY_ROWS = [[(1 if k == i else 0) if k < 12 else _golay_b(i, k - 12) for k in range(24)] for i in range(12)]


def golay_codewords():
    """All 4096 codewords of the extended Golay code, as 24-bit integers (bit k = coordinate k)."""
    rows = [sum(b << k for k, b in enumerate(r)) for r in GOLAY_ROWS]
    words = []
    for m in range(4096):
        w = 0
        for i in range(12):
            if (m >> i) & 1:
                w ^= rows[i]
        words.append(w)
    return words


def golay_weight_distribution():
    d = {}
    for w in golay_codewords():
        d[bin(w).count("1")] = d.get(bin(w).count("1"), 0) + 1
    return dict(sorted(d.items()))


# --------------------------------------------------------------------------- E8
def e8_roots():
    """The 240 roots of E8 in doubled coordinates (norm 8 here = true norm 2)."""
    roots = []
    for i, j in combinations(range(8), 2):
        for si, sj in product((2, -2), repeat=2):
            v = [0] * 8
            v[i], v[j] = si, sj
            roots.append(tuple(v))
    for signs in product((1, -1), repeat=8):
        if signs.count(-1) % 2 == 0:
            roots.append(signs)
    return roots


def in_e8(x):
    return (all(a % 2 == 0 for a in x) or all(a % 2 == 1 for a in x)) and sum(x) % 4 == 0


# --------------------------------------------------------------------------- Leech
def in_leech(x, code=None):
    """Conway's membership test (scaled by sqrt 8), mirroring `Leech` in the Lean file."""
    code = code if code is not None else set(golay_codewords())
    hi = sum((1 << k) for k, a in enumerate(x) if a % 4 in (2, 3))
    if hi not in code:
        return False
    if all(a % 2 == 0 for a in x):
        return sum(x) % 8 == 0
    if all(a % 2 == 1 for a in x):
        return (sum(x) - 4) % 8 == 0
    return False


def leech_minimal_vectors():
    """The minimal vectors (true norm 4) of the three classical shapes, each checked for membership.

    (+-4, +-4, 0^22): 1104;  (+-2^8 on an octad, 0^16) with an even number of minus signs: 97152;
    (-+3, +-1^23): 98304.  Total 196560 (the kissing number)."""
    code = set(golay_codewords())
    vecs = []
    for i, j in combinations(range(24), 2):
        for si, sj in product((4, -4), repeat=2):
            v = [0] * 24
            v[i], v[j] = si, sj
            vecs.append(tuple(v))
    octads = [w for w in code if bin(w).count("1") == 8]
    for w in octads:
        pos = [k for k in range(24) if (w >> k) & 1]
        for signs in product((2, -2), repeat=8):
            if signs.count(-2) % 2 == 0:
                v = [0] * 24
                for k, s in zip(pos, signs):
                    v[k] = s
                vecs.append(tuple(v))
    for w in code:
        for k in range(24):
            v = [(-1 if (w >> t) & 1 else 1) for t in range(24)]
            v[k] = -3 * v[k]
            vecs.append(tuple(v))
    bad = [v for v in vecs if not in_leech(v, code) or sum(a * a for a in v) != 32]
    return vecs, bad


# --------------------------------------------------------------------------- theta series (shells)
def _sigma(n, k):
    return sum(d ** k for d in range(1, n + 1) if n % d == 0)


def _mul(a, b, n):
    return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(n)]


def theta_e8(n=6):
    """Shell sizes of E8 by true norm 0, 2, 4, ...: 1, 240, 2160, 6720, ... (= E4 = 1 + 240 sum sigma3)."""
    return [1] + [240 * _sigma(k, 3) for k in range(1, n)]


def delta(n=6):
    """Ramanujan's Delta = q prod (1 - q^k)^24, coefficients of q^0 .. q^(n-1)."""
    p = [1] + [0] * (n - 1)
    for k in range(1, n):
        for _ in range(24):
            p = [p[i] - (p[i - k] if i >= k else 0) for i in range(n)]
    return [0] + p[:n - 1]


def theta_e8_cubed(n=6):
    e4 = theta_e8(n)
    return _mul(_mul(e4, e4, n), e4, n)


def theta_leech(n=6):
    """Theta_Leech = E4^3 - 720 Delta: 1, 0, 196560, 16773120, 398034000, ..."""
    t, d = theta_e8_cubed(n), delta(n)
    return [a - 720 * b for a, b in zip(t, d)]


def report():
    vecs, bad = leech_minimal_vectors()
    roots = e8_roots()
    return {
        "model_is": "the 6-cube Q6 = (Z/2)^6: 64 cells, finite; E8 and Leech are infinite lattices in R^8, R^24",
        "q6_shells_from_any_cell": q6_shells(0),
        "q6_same_shells_for_every_source": all(q6_shells(s) == q6_shells(0) for s in range(64)),
        "q6_square_faces": len(q6_squares()),
        "q6_edges": 64 * 6 // 2,
        "e8_roots": len(roots),
        "e8_roots_all_in_lattice": all(in_e8(r) and sum(a * a for a in r) == 8 for r in roots),
        "e8_roots_under_spin16": {"integer type (adjoint of SO(16) minus Cartan)": 112, "half-integer (spinor 128)": 128},
        "golay_weights": golay_weight_distribution(),
        "theta_shells_by_true_norm_0_2_4_6_8": {
            "E8": theta_e8(5), "E8+E8+E8": theta_e8_cubed(5), "Leech": theta_leech(5)},
        "leech_minimal_vectors_constructed": len(set(vecs)),
        "leech_minimal_vectors_failing_membership": len(bad),
        "verdict": ("Both lattices have rank 24, but Leech has no vectors of norm 2 (no roots) while "
                    "E8+E8+E8 has 720, and the shell sizes differ at every norm after that, so they are "
                    "different lattices. The cube Q6 is neither: it is a finite 64-vertex graph."),
    }
