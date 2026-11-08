"""Splitting a signal into modes: exact on the hypercube, floating on the torus.

Hypercube (Z/2)^n  -- Walsh-Hadamard transform, exact integer arithmetic.
  The mode of a mask k is the Walsh function x -> (-1)^popcount(k & x); the
  grade of the mode is popcount(k) and its sequency band is the grade.  The
  transform applied twice is 2^n times the identity, so `iwht` divides exactly.
  Lean: `QBX.Formal.Engine.spec_inversion`, `spec_parseval`.

Torus Z/N x Z/M  -- discrete Fourier transform with `cmath` (floating point).
  Lean: the same theorems for G = ZMod N x ZMod M; `spec_shift`,
  `power_shift_invariant`, `bispec_shift_invariant`.

Colours.  A band of modes is given a colour and a wavelength by a fixed
convention: band b of B bands is placed linearly across the visible range,
from 700 nm (lowest band, red) to 400 nm (highest band, violet).  This is a
labelling, not physics: the same data with another convention would have the
same invariants.
"""

import cmath
import math



def popcount(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c


def next_pow2(n):
    k = 0
    while (1 << k) < n:
        k += 1
    return k


def pad_pow2(xs, bits=None):
    """Pad with zeros to length 2^bits; if longer, fold the excess by addition
    (lowering: summing over the fibres of Z/2^m -> Z/2^bits)."""
    if bits is None:
        bits = next_pow2(max(1, len(xs)))
    n = 1 << bits
    out = [0] * n
    for i, x in enumerate(xs):
        out[i % n] += x
    return out, bits


def wht(xs):
    """Unnormalised Walsh-Hadamard transform of an integer list of length 2^n."""
    a = list(xs)
    n = len(a)
    if n & (n - 1):
        raise ValueError("length must be a power of two")
    h = 1
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                x, y = a[j], a[j + h]
                a[j], a[j + h] = x + y, x - y
        h *= 2
    return a


def iwht(ys):
    n = len(ys)
    a = wht(ys)
    for v in a:
        if v % n:
            raise ArithmeticError("not the transform of an integer signal")
    return [v // n for v in a]


def grade_energy(spec):
    """Energy of the spectrum in each grade (exact)."""
    bits = next_pow2(len(spec))
    out = [0] * (bits + 1)
    for k, v in enumerate(spec):
        out[popcount(k)] += v * v
    return out


def dyadic_shift(xs, a):
    return [xs[i ^ a] for i in range(len(xs))]


def permute_bits(xs, perm):
    """x -> x with bit i moved to bit perm[i] (a symmetry of the cube)."""
    n = len(xs)
    out = [0] * n
    for i in range(n):
        j = 0
        for b, pb in enumerate(perm):
            if i >> b & 1:
                j |= 1 << pb
        out[j] = xs[i]
    return out


def colour_of_band(b, nbands):
    """(name, wavelength in nm) of band b of nbands (convention, see module doc)."""
    if nbands <= 1:
        t = 0.0
    else:
        t = b / (nbands - 1)
    wl = 700.0 - 300.0 * t
    return colour_name(wl), round(wl, 1)


def colour_name(wl):
    """Conventional colour name of a wavelength in nm."""
    for bound, name in ((620, "red"), (590, "orange"), (570, "yellow"), (495, "green"),
                        (450, "blue"), (425, "indigo")):
        if wl >= bound:
            return name
    return "violet"


# --- torus --------------------------------------------------------------------

def dft2(grid):
    """2D DFT, spec[a][b] = sum_{j,k} grid[j][k] * exp(-2 pi i (a j / N + b k / M))."""
    N = len(grid)
    M = len(grid[0])
    rows = []
    for j in range(N):
        rows.append([sum(grid[j][k] * cmath.exp(-2j * math.pi * b * k / M) for k in range(M))
                     for b in range(M)])
    return [[sum(rows[j][b] * cmath.exp(-2j * math.pi * a * j / N) for j in range(N))
             for b in range(M)] for a in range(N)]


def idft2(spec):
    N = len(spec)
    M = len(spec[0])
    rows = []
    for a in range(N):
        rows.append([sum(spec[a][b] * cmath.exp(2j * math.pi * b * k / M) for b in range(M))
                     for k in range(M)])
    return [[sum(rows[a][k] * cmath.exp(2j * math.pi * a * j / N) for a in range(N)) / (N * M)
             for k in range(M)] for j in range(N)]


def torus_band(a, b, N, M):
    """Octave band of the torus mode (a, b): floor(log2) of its wave number.

    The wave number uses the signed frequencies (a mod N centred at 0), so the
    band of a mode and of its mirror image agree; band 0 is the constant mode.
    Doubling the wave number moves a mode up exactly one band (halving the
    wavelength = one octave)."""
    fa = min(a, N - a)
    fb = min(b, M - b)
    r2 = fa * fa + fb * fb
    if r2 == 0:
        return 0
    return 1 + int(math.floor(math.log2(math.sqrt(r2)) + 1e-12))
