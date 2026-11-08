"""Cayley-Dickson tower over the integers or floats, any level (mirrors CDTower.lean).

An element of level n is a list of 2**n numbers; level n+1 = pairs (a, b) of level n, with
    (a, b)(c, d) = (ac - conj(d) b, d a + b conj(c)),   conj(a, b) = (conj a, -b).
Level 2 = quaternions, 3 = octonions, 4 = sedenions, 5 = trigintaduonions, ...

Debug mode (environment variable Q6_CDCHECK=1): every `mul` first runs the pentagon checksum
`hypercube.cdcheck.debug_check` on a random basis word at its level, using the raw product.
A violation raises `CDCheckError`: it is a bug in the product, not a signal.
"""
import os

CDCHECK = os.environ.get("Q6_CDCHECK") == "1"


def conj(x):
    if len(x) == 1:
        return list(x)
    h = len(x) // 2
    return conj(x[:h]) + [-t for t in x[h:]]


def add(x, y):
    return [p + q for p, q in zip(x, y)]


def sub(x, y):
    return [p - q for p, q in zip(x, y)]


def scale(c, x):
    return [c * t for t in x]


def raw_mul(x, y):
    """The Cayley-Dickson product, unchecked."""
    if len(x) == 1:
        return [x[0] * y[0]]
    h = len(x) // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    return sub(raw_mul(a, c), raw_mul(conj(d), b)) + add(raw_mul(d, a), raw_mul(b, conj(c)))


def mul(x, y):
    """The Cayley-Dickson product; in debug mode (Q6_CDCHECK=1) checked by the pentagon checksum."""
    if CDCHECK:
        from hypercube.cdcheck import debug_check
        debug_check(len(x).bit_length() - 1, raw_mul)
    return raw_mul(x, y)


def norm2(x):
    return sum(t * t for t in x)


def basis(n, i):
    v = [0] * (2 ** n)
    v[i] = 1
    return v


def double(a, b):
    """Join two level-n elements into one level-(n+1) element (the doubling step)."""
    return list(a) + list(b)


def split(x):
    """Inverse of `double`."""
    h = len(x) // 2
    return x[:h], x[h:]


def fsgn(n, i, j):
    """Sign s with e_i e_j = s e_(i xor j), by the doubling recursion (Lean: `fsgn`)."""
    if n == 0:
        return 1
    h = 2 ** (n - 1)
    if i < h:
        return fsgn(n - 1, i, j) if j < h else fsgn(n - 1, j - h, i)
    if j < h:
        return (1 if j == 0 else -1) * fsgn(n - 1, i - h, j)
    return -((1 if j - h == 0 else -1) * fsgn(n - 1, j - h, i - h))


def two_term(n, i, j, s):
    v = basis(n, i)
    v[j] += s
    return v


def zero_divisor_census(n=4):
    """Two-term elements e_i + s e_j (1 <= i < j < 2^n) that annihilate another two-term
    element.  For n = 4 (sedenions): 210 elements, 84 zero divisors, 42 assessors, 336 ordered
    pairs (Lean: `two_term_zero_divisor_count`)."""
    N = 2 ** n
    els = [(i, j, s) for i in range(1, N) for j in range(i + 1, N) for s in (1, -1)]
    vec = {a: two_term(n, *a) for a in els}
    pairs = [(a, b) for a in els for b in els if not any(mul(vec[a], vec[b]))]
    zd = sorted({a for a, _ in pairs})
    return {"elements": len(els), "zero_divisors": len(zd),
            "assessors": len({(i, j) for i, j, _ in zd}), "ordered_pairs": len(pairs), "list": zd}


def associator(x, y, z):
    return sub(mul(mul(x, y), z), mul(x, mul(y, z)))


def properties(n, trials=200, seed=1):
    """Which laws survive at level n (random integer tests)."""
    import random
    rnd = random.Random(seed)
    N = 2 ** n
    r = lambda: [rnd.randint(-3, 3) for _ in range(N)]
    ok = {"commutative": True, "associative": True, "alternative": True, "norm_multiplicative": True}
    for _ in range(trials):
        x, y, z = r(), r(), r()
        if mul(x, y) != mul(y, x):
            ok["commutative"] = False
        if any(associator(x, y, z)):
            ok["associative"] = False
        if any(associator(x, x, y)):
            ok["alternative"] = False
        if norm2(mul(x, y)) != norm2(x) * norm2(y):
            ok["norm_multiplicative"] = False
    return ok


def annihilator_dim(x, tol=1e-9):
    """Dimension of {y : x y = 0} (left multiplication kernel), by Gaussian elimination."""
    N = len(x)
    cols = [mul(x, basis_f(N, j)) for j in range(N)]
    M = [[float(cols[j][i]) for j in range(N)] for i in range(N)]
    rank, row = 0, 0
    for c in range(N):
        piv = max(range(row, N), key=lambda r: abs(M[r][c]), default=None)
        if piv is None or abs(M[piv][c]) < tol:
            continue
        M[row], M[piv] = M[piv], M[row]
        for r in range(N):
            if r != row and abs(M[r][c]) > tol:
                f = M[r][c] / M[row][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[row])]
        row += 1
        rank += 1
        if row == N:
            break
    return N - rank


def basis_f(N, j):
    v = [0] * N
    v[j] = 1
    return v
