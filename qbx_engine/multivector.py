"""Eigenmode multivectors: storing a channel on the hypercube.

A channel of length L is padded (or folded) to 2^n samples.  Sample x is the
coefficient of the basis blade with bitmask x in the Clifford algebra Cl(n) of
`qbx_micro.cliff`; the Walsh-Hadamard spectrum is again a multivector, whose
blade k is the eigenmode (Walsh function) k.  Grade of a blade = number of
generators = sequency band = colour.  All arithmetic is exact (Python ints).

Operations (the outline's Cayley-Dickson operator suite, on stored data):

  double(A, B)   the pair (A, B) as one multivector on n+1 generators: B moves
                 to the blades containing the new generator e_n.  Its spectrum
                 is the butterfly (Â + B̂, Â - B̂)          [Lean: spec_double]
  halve(C)       the inverse split                          [halve_double, double_halve]
  lift(A, m)     constant extension to n+m generators       [spec_lift_trivial]
  lower(C, m)    sum over the top m generators              [spec_lower]
  cd_mul(x, y)   Cayley-Dickson product of coefficient vectors of length 2^n,
                 (a, b)(c, d) = (ac - d* b, da + b c*)
  cd_norm(x)     sum of squares

`lost_properties(n)` tests, on fixed integer samples, which algebraic laws of
the Cayley-Dickson algebra of dimension 2^n fail: commutativity fails from
n = 2, associativity from n = 3, norm multiplicativity (the composition law
behind the Hopf maps) from n = 4.  The outline treats each lost law as
information.
"""

from . import spectrum


def to_blades(xs):
    return {i: v for i, v in enumerate(xs) if v}


def from_blades(mv, bits):
    out = [0] * (1 << bits)
    for k, v in mv.items():
        out[k] += v
    return out


def double(a, b):
    if len(a) != len(b):
        raise ValueError("double needs two signals of the same length")
    return list(a) + list(b)


def halve(c):
    h = len(c) // 2
    return c[:h], c[h:]


def lift(a, m):
    return list(a) * (1 << m)


def lower(c, m):
    n = len(c) >> m
    out = [0] * n
    for i, v in enumerate(c):
        out[i % n] += v
    return out


# --- Cayley-Dickson ------------------------------------------------------------

def cd_conj(x):
    if len(x) == 1:
        return list(x)
    h = len(x) // 2
    return cd_conj(x[:h]) + [-v for v in x[h:]]


def cd_mul(x, y):
    if len(x) == 1:
        return [x[0] * y[0]]
    h = len(x) // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    left = [p - q for p, q in zip(cd_mul(a, c), cd_mul(cd_conj(d), b))]
    right = [p + q for p, q in zip(cd_mul(d, a), cd_mul(b, cd_conj(c)))]
    return left + right


def cd_norm(x):
    return sum(v * v for v in x)


def _samples(n, seed):
    out = []
    s = seed
    for _ in range(3):
        v = []
        for _ in range(1 << n):
            s = (s * 1103515245 + 12345) % (1 << 31)
            v.append(s % 7 - 3)
        out.append(v)
    return out


def lost_properties(n, trials=8):
    """Which laws fail in the Cayley-Dickson algebra of dimension 2^n (on samples)."""
    comm = assoc = normmul = True
    for t in range(trials):
        x, y, z = _samples(n, 17 + 31 * t)
        if cd_mul(x, y) != cd_mul(y, x):
            comm = False
        if cd_mul(cd_mul(x, y), z) != cd_mul(x, cd_mul(y, z)):
            assoc = False
        if cd_norm(cd_mul(x, y)) != cd_norm(x) * cd_norm(y):
            normmul = False
    if n >= 4 and normmul:
        # the standard sedenion zero-divisor pair (e3 + e10)(e6 - e15) = 0
        x = [0] * 16
        y = [0] * 16
        x[3], x[10], y[6], y[15] = 1, 1, 1, -1
        x = x + [0] * ((1 << n) - 16)
        y = y + [0] * ((1 << n) - 16)
        if cd_norm(cd_mul(x, y)) != cd_norm(x) * cd_norm(y):
            normmul = False
    lost = []
    if not comm:
        lost.append("commutative")
    if not assoc:
        lost.append("associative")
    if not normmul:
        lost.append("norm-multiplicative")
    return lost


class EigenMultivector:
    """A channel stored as its exact Walsh spectrum on Cl(bits)."""

    def __init__(self, samples, bits=None):
        self.signal, self.bits = spectrum.pad_pow2(list(samples), bits)
        self.spec = spectrum.wht(self.signal)

    @property
    def blades(self):
        return to_blades(self.spec)

    def grade_energy(self):
        return spectrum.grade_energy(self.spec)

    def colours(self):
        nb = self.bits + 1
        ge = self.grade_energy()
        return [{"grade": g, "colour": spectrum.colour_of_band(g, nb)[0],
                 "wavelength_nm": spectrum.colour_of_band(g, nb)[1], "energy": ge[g]}
                for g in range(nb)]

    def checks(self):
        """Exact re-derivations of the Lean facts on this channel."""
        n = 1 << self.bits
        sig, spec = self.signal, self.spec
        out = {
            "inversion": spectrum.iwht(spec) == sig,
            "parseval": sum(v * v for v in spec) == n * sum(v * v for v in sig),
        }
        a = (n - 1) // 3 if n > 1 else 0
        sh = spectrum.wht(spectrum.dyadic_shift(sig, a))
        out["dyadic_shift_power"] = all(sh[k] * sh[k] == spec[k] * spec[k] for k in range(n))
        if self.bits >= 2:
            perm = list(range(1, self.bits)) + [0]
            pe = spectrum.grade_energy(spectrum.wht(spectrum.permute_bits(sig, perm)))
            out["grade_energy_under_generator_permutation"] = pe == self.grade_energy()
        if self.bits >= 1:
            lo, hi = halve(sig)
            sl, shh = spectrum.wht(lo), spectrum.wht(hi)
            out["double_butterfly"] = spec == [p + q for p, q in zip(sl, shh)] + \
                [p - q for p, q in zip(sl, shh)]
            out["lower_commutes"] = spectrum.wht(lower(sig, 1)) == spec[: n // 2]
        return out
