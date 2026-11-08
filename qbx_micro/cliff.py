"""Exact Clifford algebra Cl(p, q, r) on the hypercube of blades.

A basis blade is a bitmask: bit i set means the generator e_i is a factor.  The
2^n blades are the vertices of the n-cube, the grade of a blade is its Hamming
weight, and the grades form the nested lattice 0 < 1 < ... < n (the Boolean
lattice of subsets of the generators).  The geometric product of two blades is
the XOR of the masks times a sign, so the algebra is a twisted group algebra
of the cube group (Z/2)^n.

A multivector is a dict {mask: coefficient}.  Coefficients are Python integers
(arbitrary precision, also on MicroPython), so every computation is exact.

Signature: `sig` is a tuple of length n with entries +1, -1 or 0 giving e_i^2.
Cl(0, n) (all -1) is the algebra used by the braid channel.

This module is dependency-free and runs unchanged under MicroPython.
"""


def popcount(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c


def bitlen(x):
    """Number of binary digits of x >= 0 (int.bit_length is missing on MicroPython)."""
    n = 0
    while x:
        x >>= 1
        n += 1
    return n


def reorder_sign(a, b):
    """Sign from moving the generators of blade b past those of blade a."""
    a >>= 1
    swaps = 0
    while a:
        swaps += popcount(a & b)
        a >>= 1
    return -1 if swaps & 1 else 1


def blade_product(a, b, sig):
    """(sign, mask) of the product of basis blades a and b; sign 0 if it vanishes."""
    s = reorder_sign(a, b)
    common = a & b
    i = 0
    while common:
        if common & 1:
            m = sig[i]
            if m == 0:
                return 0, 0
            s *= m
        common >>= 1
        i += 1
    return s, a ^ b


def clean(x):
    return {k: v for k, v in x.items() if v != 0}


def gp(x, y, sig):
    """Geometric product of multivectors x and y."""
    out = {}
    for a, ca in x.items():
        for b, cb in y.items():
            s, m = blade_product(a, b, sig)
            if s:
                out[m] = out.get(m, 0) + s * ca * cb
    return clean(out)


def add(x, y, s=1):
    """x + s*y."""
    out = dict(x)
    for k, v in y.items():
        out[k] = out.get(k, 0) + s * v
    return clean(out)


def scale(x, c):
    return clean({k: c * v for k, v in x.items()})


def reverse(x):
    """Reversion: a grade-k blade picks up (-1)^(k(k-1)/2)."""
    out = {}
    for k, v in x.items():
        g = popcount(k)
        out[k] = -v if (g * (g - 1) // 2) & 1 else v
    return out


def involute(x):
    """Grade involution: a grade-k blade picks up (-1)^k."""
    return {k: (-v if popcount(k) & 1 else v) for k, v in x.items()}


def grade_part(x, g):
    return {k: v for k, v in x.items() if popcount(k) == g}


def grades(x):
    """Sorted list of the grades present in x."""
    return sorted(set(popcount(k) for k in x))


def is_even(x):
    return all(popcount(k) % 2 == 0 for k in x)


def gen(i):
    """The generator e_(i+1) (bit i) as a multivector."""
    return {1 << i: 1}


def blade_name(mask):
    if mask == 0:
        return "1"
    return "e" + "".join(str(i + 1) for i in range(bitlen(mask)) if mask >> i & 1)


def show(x):
    if not x:
        return "0"
    keys = sorted(x, key=lambda m: (popcount(m), m))
    return " + ".join("%d*%s" % (x[k], blade_name(k)) for k in keys)


# ----------------------------------------------------------------------------- hypercube view

def binomials(n):
    """C(n, k) for k = 0..n: the dimension of each grade of Cl(n)."""
    out = []
    c = 1
    for k in range(n + 1):
        out.append(c)
        c = c * (n - k) // (k + 1)
    return out


def cube_f_vector(n):
    """Number of k-dimensional faces of the n-cube, k = 0..n: C(n,k) 2^(n-k)."""
    return [c * (1 << (n - k)) for k, c in enumerate(binomials(n))]
