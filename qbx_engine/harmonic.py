"""The harmonic map: values -> harmonics -> torus nodes.

A value v (a letter's number, a sample, a byte) is read in two ways.

  * as a harmonic: frequency v * f0 (the v-th partial of the base f0); its pitch
    class is the position of v inside its octave, in cents (log2 v mod 1);
  * as a node of the N x M torus: (v mod N, v mod M).

Lean (`QBX/Formal/Engine/Waves.lean`): the node map from Z/(N M) to Z/N x Z/M
preserves sums and products (`harmonicMap_add`, `harmonicMap_mul`); it is a
bijection exactly when gcd(N, M) = 1 (`harmonicMap_bijective`,
`harmonicMap_not_injective`).  So on a coprime torus every value below N M has
its own node, and adding values (stacking letters) is adding torus positions.
"""

import math

F0 = 432.0 / 16  # base frequency in Hz, so that harmonic 16 is 432 Hz (project convention)


def node(v, N, M):
    return (v % N, v % M)


def frequency(v, f0=F0):
    return v * f0


def pitch_class_cents(v):
    """Position of the v-th harmonic inside its octave, 0 <= c < 1200."""
    if v <= 0:
        return None
    return round((math.log2(v) % 1.0) * 1200.0, 3)


def interval_cents(v, w):
    return round(1200.0 * math.log2(w / v), 3) if v > 0 and w > 0 else None


def is_bijective(N, M):
    return math.gcd(N, M) == 1


def collisions(values, N, M):
    """Groups of distinct values that land on the same torus node."""
    groups = {}
    for v in sorted(set(values)):
        groups.setdefault(node(v, N, M), []).append(v)
    return {"%d,%d" % k: g for k, g in groups.items() if len(g) > 1}


def crt_inverse(a, b, N, M):
    """The unique value v mod N M with node (a, b), for coprime N, M."""
    for v in range(N * M):
        if v % N == a % N and v % M == b % M:
            return v
    return None


def letter_harmonics(letter, N=16, M=25, f0=F0):
    v = letter.value
    return {"value": v, "frequency_hz": frequency(v, f0), "pitch_class_cents": pitch_class_cents(v),
            "torus_node": node(v, N, M), "torus": [N, M]}


def checks(N=16, M=25, trials=200):
    import random
    rng = random.Random(7)
    ok = {"bijective_iff_coprime": True, "additive": True, "multiplicative": True}
    for n in range(1, 13):
        for m in range(1, 13):
            image = {node(v, n, m) for v in range(n * m)}
            if (len(image) == n * m) != is_bijective(n, m):
                ok["bijective_iff_coprime"] = False
    for _ in range(trials):
        v, w = rng.randrange(N * M), rng.randrange(N * M)
        a, b = node(v, N, M), node(w, N, M)
        if node(v + w, N, M) != ((a[0] + b[0]) % N, (a[1] + b[1]) % M):
            ok["additive"] = False
        if node(v * w, N, M) != ((a[0] * b[0]) % N, (a[1] * b[1]) % M):
            ok["multiplicative"] = False
    return ok
