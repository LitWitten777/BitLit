"""Factorions, hypercube nets and Curtis's MOG partitions (2026-10-23).

Three families of exact patterns, computed here and partly proved in Lean
(`Sovereign.Organism.HypercubePatterns`):

1. **Factorions.**  `n` is a factorion in base `b` if it equals the sum of the factorials of its
   base-`b` digits.  The search is complete: a `k`-digit number is at least `b^(k-1)` while its digit
   factorial sum is at most `k (b-1)!`, so only finitely many `k` are possible, and for each `k` it
   suffices to try every *multiset* of `k` digits (the sum does not depend on the order).
   Base 10: exactly `1, 2, 145, 40585` (Lean: `factorions_base10`).
2. **Hypercube nets.**  Unfolding the `n`-cube into `R^(n-1)` means cutting it along ridges until the
   `2n` facets hang together as a tree; the facets `±e_i` are adjacent unless opposite, so the
   facet graph is the cocktail-party graph `K_(n×2)` (the 1-skeleton of the cross-polytope), and a
   net is a spanning tree of it up to the `2^n n!` symmetries of the cube.  Computed: `1, 11, 261`
   nets for `n = 2, 3, 4` (the cube's 11 nets; Turney's 261 nets of the tesseract).  The number of
   spanning trees is `(2n)^(n-2) (2n-2)^n` (`4, 384, 82944, ...`), and nets / (trees / 2^n n!) -> 1:
   almost every unfolding has no symmetry.
3. **Curtis's Miracle Octad Generator (MOG).**  The 24 points are a 4 × 6 array; rows are labelled by
   the field `F4 = {0, 1, w, w̄}`.  A set is a Golay codeword iff (a) every column and the top row have
   the same parity and (b) the column "scores" (sum of the row labels of the chosen points) form a
   word of the **hexacode**, the `[6, 3, 4]` code over `F4`.  The hexacode has `4^3 = 64` words, the
   same number as the cells of the cube, and each hexacode word has `64` interpretations, so the
   Golay code has `64 · 64 = 4096` words.  From it: 759 octads, 2576 dodecads, the **1771 sextets**
   (partitions of the 24 points into six tetrads, any two of which form an octad; every 4-set lies in
   exactly one sextet) and the **3795 trios** (partitions into three octads).  The six columns of the
   MOG form a sextet and the three "bricks" (pairs of columns) form a trio.
"""
import itertools
import math
from collections import Counter
from functools import lru_cache

# ----------------------------------------------------------------------------- factorions


def digit_factorial_sum(n, base=10):
    s = 0
    while True:
        n, d = divmod(n, base)
        s += math.factorial(d)
        if n == 0:
            return s


def factorion_bound(base):
    """Largest digit count k with base^(k-1) <= k (base-1)!."""
    k, f = 1, math.factorial(base - 1)
    while base ** k <= (k + 1) * f:
        k += 1
    return k


def factorions(base=10):
    """All factorions in `base` (complete; multiset search)."""
    fact = [math.factorial(d) for d in range(base)]
    found = set()
    for k in range(1, factorion_bound(base) + 1):
        for ms in itertools.combinations_with_replacement(range(base), k):
            s = sum(fact[d] for d in ms)
            digits, t = [], s
            while True:
                t, d = divmod(t, base)
                digits.append(d)
                if t == 0:
                    break
            if len(digits) == k and sorted(digits) == list(ms):
                found.add(s)
    return sorted(found)


def factorion_table(bases=range(2, 13)):
    return {b: factorions(b) for b in bases}


# ----------------------------------------------------------------------------- hypercube nets


def facet_graph(n):
    """Facets of the n-cube as 0..2n-1 (2i = +e_i, 2i+1 = -e_i); edges between non-opposite ones."""
    return [(a, b) for a in range(2 * n) for b in range(a + 1, 2 * n) if a // 2 != b // 2]


def cube_symmetries(n):
    """The 2^n n! symmetries of the n-cube acting on facets."""
    out = []
    for perm in itertools.permutations(range(n)):
        for signs in range(2 ** n):
            out.append([2 * perm[f // 2] + ((f % 2) ^ ((signs >> (f // 2)) & 1)) for f in range(2 * n)])
    return out


def spanning_trees(n):
    """All spanning trees of the facet graph, as frozensets of edges."""
    edges, v = facet_graph(n), 2 * n
    out = []
    for combo in itertools.combinations(edges, v - 1):
        parent = list(range(v))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        ok = True
        for a, b in combo:
            ra, rb = find(a), find(b)
            if ra == rb:
                ok = False
                break
            parent[ra] = rb
        if ok:
            out.append(frozenset(combo))
    return out


def tree_count_formula(n):
    """Spanning trees of K_(n×2): (2n)^(n-2) (2n-2)^n."""
    return (2 * n) ** (n - 2) * (2 * n - 2) ** n if n >= 2 else 1


def count_nets(n):
    """Orbits of spanning trees of the facet graph under the cube's symmetries."""
    trees = spanning_trees(n)
    syms = cube_symmetries(n)
    seen, orbits, sizes = set(), 0, Counter()
    for t in trees:
        if t in seen:
            continue
        orbit = set()
        for g in syms:
            orbit.add(frozenset(tuple(sorted((g[a], g[b]))) for a, b in t))
        seen |= orbit
        orbits += 1
        sizes[len(syms) // len(orbit)] += 1
    return {"n": n, "spanning_trees": len(trees), "formula": tree_count_formula(n),
            "symmetries": len(syms), "nets": orbits, "stabiliser_sizes": dict(sorted(sizes.items())),
            "trees_over_symmetries": round(len(trees) / len(syms), 3)}


# ----------------------------------------------------------------------------- MOG / hexacode

# F4 = {0, 1, w, w̄} as 0, 1, 2, 3: addition is XOR; multiplication by the table below.
F4_MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]


def f4_mul(a, b):
    return F4_MUL[a][b]


@lru_cache(maxsize=1)
def hexacode():
    """The 64 words (a, b, c, φ(1), φ(w), φ(w̄)) with φ(x) = a x² + b x + c."""
    words = []
    for a, b, c in itertools.product(range(4), repeat=3):
        def phi(x):
            return f4_mul(a, f4_mul(x, x)) ^ f4_mul(b, x) ^ c
        words.append((a, b, c, phi(1), phi(2), phi(3)))
    return words


def point(row, col):
    """MOG position (row 0..3 labelled 0, 1, w, w̄; column 0..5) -> point 0..23."""
    return 4 * col + row


@lru_cache(maxsize=1)
def mog_golay():
    """The Golay code built from the hexacode by Curtis's MOG rule, as 24-bit masks."""
    hexa = set(hexacode())
    cols = {}                     # (score, parity) -> list of 4-bit column patterns
    for pat in range(16):
        score = 0
        for r in range(4):
            if pat >> r & 1:
                score ^= r        # row label of row r is r (0, 1, w=2, w̄=3)
        cols.setdefault((score, bin(pat).count("1") % 2), []).append(pat)
    code = set()
    for h in hexa:
        for parity in (0, 1):
            for choice in itertools.product(*[cols[(h[c], parity)] for c in range(6)]):
                top = sum(p & 1 for p in choice) % 2
                if top != parity:
                    continue
                mask = 0
                for c, p in enumerate(choice):
                    mask |= p << (4 * c)
                code.add(mask)
    return sorted(code)


def weight_distribution(code):
    return dict(sorted(Counter(bin(w).count("1") for w in code).items()))


def is_linear(code):
    s = set(code)
    gens = []
    span = {0}
    for w in code:
        if w not in span:
            gens.append(w)
            span |= {x ^ w for x in span}
    return len(span) == len(s) and span == s, len(gens)


@lru_cache(maxsize=1)
def octads():
    return [w for w in mog_golay() if bin(w).count("1") == 8]


@lru_cache(maxsize=1)
def octad_of_5set():
    table = {}
    for o in octads():
        pts = [i for i in range(24) if o >> i & 1]
        for five in itertools.combinations(pts, 5):
            table[five] = o
    return table


def sextet_of(tetrad):
    """The sextet (six tetrads) determined by a 4-set."""
    table = octad_of_5set()
    t = tuple(sorted(tetrad))
    tm = sum(1 << i for i in t)
    parts, used = [tm], tm
    for p in range(24):
        if used >> p & 1:
            continue
        o = table[tuple(sorted(t + (p,)))]
        rest = o & ~tm
        parts.append(rest)
        used |= rest
    return frozenset(parts)


@lru_cache(maxsize=1)
def sextets():
    out = set()
    for t in itertools.combinations(range(24), 4):
        out.add(sextet_of(t))
    return out


@lru_cache(maxsize=1)
def trios():
    ocs = octads()
    out = set()
    full = (1 << 24) - 1
    oset = set(ocs)
    for i, a in enumerate(ocs):
        for b in ocs[i + 1:]:
            if a & b == 0 and (full ^ a ^ b) in oset:
                out.add(frozenset((a, b, full ^ a ^ b)))
    return out


def mog_report():
    code = mog_golay()
    lin, dim = is_linear(code)
    hexa = hexacode()
    sx = sextets()
    columns = frozenset(0xF << (4 * c) for c in range(6))
    bricks = frozenset(0xFF << (8 * k) for k in range(3))
    sextet_ok = all(len(s) == 6 and all(bin(x).count("1") == 4 for x in s) and
                    all((x | y) in set(octads()) for x, y in itertools.combinations(s, 2)) for s in sx)
    return {
        "hexacode_words": len(hexa),
        "hexacode_weights": weight_distribution([sum(1 << i for i, x in enumerate(h) if x) for h in hexa]),
        "golay_words": len(code), "golay_linear": lin, "golay_dimension": dim,
        "golay_weights": weight_distribution(code),
        "octads": len(octads()), "sextets": len(sx), "trios": len(trios()),
        "every_sextet_pair_is_an_octad": sextet_ok,
        "columns_form_a_sextet": columns in sx,
        "bricks_form_a_trio": bricks in trios(),
        "sextets_times_6_eq_tetrads": len(sx) * 6 == math.comb(24, 4),
    }


def report(nets_max=4, bases=range(2, 13)):
    out = {"factorions": factorion_table(bases),
           "nets": [count_nets(n) for n in range(2, nets_max + 1)],
           "mog": mog_report()}
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(report(), indent=1, default=str))
