"""gosset: an exact address structure on E8 and the Gosset polytope 4_21.

Everything is integer arithmetic in *doubled coordinates* (v = 2x, so a root has
sum(v_i^2) = 8 and inner products between roots are 8, 4, 0, -4, -8).  The numbers that the
module computes are the ones proved in Lean (QBX/Formal/Gosset/*.lean); the tests check that
the two agree.  MicroPython-compatible (no numpy, no f-strings, no dataclasses).

Layers of structure on the 240 roots (= vertices of 4_21):

  relation(r, s)        one of five shells: same / adjacent (60 deg) / orthogonal /
                        obtuse (120 deg) / antipodal, sizes 1, 56, 126, 56, 1
  flag_coord(r)         8 integers in {-2..2}: inner products with a fixed flag of 8 pairwise
                        adjacent roots.  A complete address (injective on roots).
  ladder_depth(r)       how far r goes down the Gosset ladder 240 > 56 > 27 > 16 > 10 > 6 > 3 > 1
  ring_address(r)       (ring, phase) in 8 x Z/30: r = c^phase(ring representative), where c is
                        the Coxeter element.  c acts as phase -> phase + 1 (a clock of order 30).
  star_point(r)         one of 13 points of the A2 weight lattice ("magic star"):
                        72 at the centre (E6), 1 at each of 6 outer points, 27 at each of the 6
                        hexagram points
  nearest_lattice_point exact E8 decoder (Conway-Sloane) for rational input

and an honest test harness:

  placement_test(placement, pairs)  permutation test: does a proposed placement of items on the
                        roots put the given related pairs in a chosen shell more often than a
                        random placement does?
"""

from fractions import Fraction

# ----------------------------------------------------------------------------- roots

def _int_roots():
    out = []
    for i in range(8):
        for j in range(8):
            if i < j:
                for s in (2, -2):
                    for t in (2, -2):
                        v = [0] * 8
                        v[i] = s
                        v[j] = t
                        out.append(tuple(v))
    return out


def _half_roots():
    out = []
    # same order as Lean's List.sections (first coordinate varies slowest, +1 before -1)
    for m in range(256):
        v = tuple(1 if (m >> (7 - k)) & 1 == 0 else -1 for k in range(8))
        if v.count(-1) % 2 == 0:
            out.append(v)
    return out


ROOTS = tuple(_int_roots() + _half_roots())
INDEX = dict((r, i) for i, r in enumerate(ROOTS))


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def neg(v):
    return tuple(-a for a in v)


SHELLS = {8: "same", 4: "adjacent", 0: "orthogonal", -4: "obtuse", -8: "antipodal"}


def relation(r, s):
    """The shell of s seen from r."""
    return SHELLS[dot(r, s)]


# ----------------------------------------------------------------------------- the flag

FLAG = (
    (2, 2, 0, 0, 0, 0, 0, 0), (2, 0, 2, 0, 0, 0, 0, 0), (2, 0, 0, 2, 0, 0, 0, 0),
    (2, 0, 0, 0, 2, 0, 0, 0), (2, 0, 0, 0, 0, 2, 0, 0), (2, 0, 0, 0, 0, 0, 2, 0),
    (2, 0, 0, 0, 0, 0, 0, 2), (1, 1, 1, 1, 1, 1, 1, 1),
)

GOSSET_NAMES = ("4_21", "3_21", "2_21", "1_21", "0_21", "-1_21", "triangle", "point", "empty")
CHAIN_NAMES = ("E8", "E7", "E6", "D5", "A4", "A2xA1", "A1", "-", "-")


def flag_coord(r):
    return tuple(dot(r, f) // 4 for f in FLAG)


def layer(k):
    """Roots adjacent to each of the first k flag roots (Lean: Gosset.layer)."""
    return [r for r in ROOTS if all(dot(r, f) == 4 for f in FLAG[:k])]


def perp(k):
    """Roots orthogonal to each of the first k flag roots (Lean: Gosset.perp)."""
    return [r for r in ROOTS if all(dot(r, f) == 0 for f in FLAG[:k])]


def ladder_depth(r):
    k = 0
    while k < 8 and dot(r, FLAG[k]) == 4:
        k += 1
    return k


# ----------------------------------------------------------------------------- Coxeter rings

SIMPLE_E8 = (
    (0, 2, -2, 0, 0, 0, 0, 0), (0, 0, 2, -2, 0, 0, 0, 0), (0, 0, 0, 2, -2, 0, 0, 0),
    (0, 0, 0, 0, 2, -2, 0, 0), (0, 0, 0, 0, 0, 2, -2, 0), (0, 0, 0, 0, 0, 0, 2, 2),
    (0, 0, 0, 0, 0, 0, 2, -2), (1, -1, -1, -1, -1, -1, -1, 1),
)
SIMPLE_E7 = SIMPLE_E8[1:]
SIMPLE_E6 = SIMPLE_E8[2:]

RING_REPS_E8 = (
    (2, 2, 0, 0, 0, 0, 0, 0), (2, 0, 0, 0, 0, 0, 0, 2), (2, 0, 0, 0, 0, -2, 0, 0),
    (2, 0, 0, 0, -2, 0, 0, 0), (1, 1, 1, -1, 1, -1, 1, 1), (1, 1, 1, -1, -1, 1, 1, 1),
    (1, 1, -1, 1, -1, -1, 1, -1), (1, 1, -1, -1, -1, 1, -1, 1),
)
COXETER_NUMBER = {"E8": 30, "E7": 18, "E6": 12}


def reflect(a, v):
    """Reflection in the root a (doubled coordinates)."""
    k = dot(v, a) // 4
    return tuple(x - k * y for x, y in zip(v, a))


def coxeter(v, simple=SIMPLE_E8):
    """c = s_1 s_2 ... s_n applied to v (s_n acts first)."""
    for a in reversed(simple):
        v = reflect(a, v)
    return v


def orbit(r, simple=SIMPLE_E8):
    out = [r]
    v = coxeter(r, simple)
    while v != r:
        out.append(v)
        v = coxeter(v, simple)
    return out


_RING_TABLE = None


def _ring_table():
    global _RING_TABLE
    if _RING_TABLE is None:
        t = {}
        for k, rep in enumerate(RING_REPS_E8):
            for j, v in enumerate(orbit(rep)):
                t[v] = (k, j)
        _RING_TABLE = t
    return _RING_TABLE


def ring_address(r):
    """(ring, phase) with r = c^phase(RING_REPS_E8[ring])."""
    return _ring_table()[tuple(r)]


def root_at(ring, phase):
    v = RING_REPS_E8[ring]
    for _ in range(phase % 30):
        v = coxeter(v)
    return v


# ----------------------------------------------------------------------------- magic star

STAR_TABLE = {
    (0, 0): 72,
    (2, 1): 1, (1, 2): 1, (-1, 1): 1, (-2, -1): 1, (-1, -2): 1, (1, -1): 1,
    (1, 1): 27, (-1, 0): 27, (0, -1): 27, (-1, -1): 27, (1, 0): 27, (0, 1): 27,
}
HEXAGRAM = ((1, 1), (-1, 0), (0, -1), (-1, -1), (1, 0), (0, 1))


def star_point(r):
    return (dot(r, FLAG[0]) // 4, dot(r, FLAG[1]) // 4)


def star_fibre(p):
    return [r for r in ROOTS if star_point(r) == p]


# ----------------------------------------------------------------------------- 27 lines

def lines27():
    return layer(2)


def sixes():
    """The 72 sixes (mutually skew 6-sets of lines), one for each E6 root."""
    L = lines27()
    return dict((a, [x for x in L if dot(a, x) == 4]) for a in perp(2))


# ----------------------------------------------------------------------------- decoder

def _round_half_away(q):
    # nearest integer, ties away from zero (deterministic)
    f = q.numerator // q.denominator
    r = q - f
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and q > 0):
        return f + 1
    return f


def _nearest_d8(x):
    y = [_round_half_away(q) for q in x]
    if sum(y) % 2 != 0:
        # re-round the coordinate with the largest rounding error the other way
        errs = [abs(q - yi) for q, yi in zip(x, y)]
        k = max(range(8), key=lambda i: (errs[i], -i))
        y[k] += 1 if x[k] > y[k] else -1
    return y


def nearest_lattice_point(x):
    """Nearest point of E8 to x (rational coordinates, normal scale); doubled coordinates."""
    x = [Fraction(q) for q in x]
    y0 = _nearest_d8(x)
    half = Fraction(1, 2)
    y1 = [v + half for v in _nearest_d8([q - half for q in x])]
    d0 = sum((q - v) ** 2 for q, v in zip(x, y0))
    d1 = sum((q - v) ** 2 for q, v in zip(x, y1))
    best = y0 if d0 <= d1 else y1
    return tuple(int(2 * v) for v in best)


def is_lattice_point(v):
    """Doubled coordinates of an E8 point: one parity, sum divisible by 4."""
    return all(a % 2 == v[0] % 2 for a in v) and sum(v) % 4 == 0


def nearest_root(x):
    """The root maximising <x, r> (first in ROOTS order on ties); exact for rational x."""
    x = [Fraction(q) for q in x]
    best, bi = None, -1
    for i, r in enumerate(ROOTS):
        s = sum(q * a for q, a in zip(x, r))
        if best is None or s > best:
            best, bi = s, i
    return ROOTS[bi]


# ----------------------------------------------------------------------------- tests of placements

class _LCG:
    """Small deterministic generator (MicroPython has no random.Random with seeds everywhere)."""

    def __init__(self, seed):
        self.s = seed & 0xFFFFFFFF

    def below(self, n):
        self.s = (1103515245 * self.s + 12345) & 0x7FFFFFFF
        return self.s % n


def placement_test(placement, pairs, shell="adjacent", trials=2000, seed=1):
    """Permutation test for a proposed placement of items on roots.

    placement: dict item -> root (distinct roots).  pairs: list of (item, item) that some
    tradition or hypothesis says are related.  Counts the pairs whose roots are in `shell`, and
    compares with `trials` random injective placements of the same items.

    Returns dict(observed, expected, p_value): expected is the exact mean under a uniformly
    random injective placement; p_value = P(random count >= observed), estimated with add-one
    smoothing.
    """
    items = list(placement)
    target = [k for k, v in SHELLS.items() if v == shell][0]
    obs = sum(1 for a, b in pairs if dot(placement[a], placement[b]) == target)
    sizes = {8: 1, 4: 56, 0: 126, -4: 56, -8: 1}
    distinct = [(a, b) for a, b in pairs if a != b]
    expected = Fraction(sizes[target], 239) * len(distinct) if target != 8 else Fraction(0)
    expected += sum(1 for a, b in pairs if a == b) if target == 8 else 0
    g = _LCG(seed)
    hits = 0
    n = len(ROOTS)
    for _ in range(trials):
        perm = list(range(n))
        for i in range(len(items)):
            j = i + g.below(n - i)
            perm[i], perm[j] = perm[j], perm[i]
        rnd = dict((it, ROOTS[perm[i]]) for i, it in enumerate(items))
        c = sum(1 for a, b in pairs if dot(rnd[a], rnd[b]) == target)
        if c >= obs:
            hits += 1
    return {"observed": obs, "expected": float(expected),
            "p_value": (hits + 1) / (trials + 1.0)}


# ----------------------------------------------------------------------------- summary

def summary():
    return {
        "roots": len(ROOTS),
        "shells": [sum(1 for s in ROOTS if dot(ROOTS[0], s) == c) for c in (8, 4, 0, -4, -8)],
        "ladder": [len(layer(k)) for k in range(9)],
        "chain": [len(perp(k)) for k in range(9)],
        "rings": [len(orbit(r)) for r in RING_REPS_E8],
        "star": dict(("%d,%d" % p, len(star_fibre(p))) for p in STAR_TABLE),
        "sixes": len(sixes()),
    }
