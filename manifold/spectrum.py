"""Split / join data into spectra on the hypercube (mirrors Spectrum.lean).

A block of 2**n samples is a signal on Q_n.  `wht` is the Walsh-Hadamard transform by the
doubling butterfly (a, b) -> (a + b, a - b); `wht(wht(f)) = 2**n f` (Lean `wht_wht`), so
split -> join is lossless.  Index bit k of a sample position is coordinate k of the cube, so
frequency w has "sequency shell" popcount(w) = Hamming weight (Lean `shell`).

Bands:
* shells: frequencies grouped by Hamming weight (n+1 bands; for Q6: 1, 6, 15, 20, 15, 6, 1);
* hopf:   for Q6, frequencies grouped by their GF(8) Hopf fibre (9 fibres + the zero frequency),
          using `hypercube.hopf`;
* octaves: dyadic (wavelength) bands [2^k, 2^(k+1)) in sequency order.
"""
import math


def wht(f):
    """Unnormalised fast Walsh-Hadamard transform (natural / Hadamard order)."""
    a = list(f)
    h = 1
    n = len(a)
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                x, y = a[j], a[j + h]
                a[j], a[j + h] = x + y, x - y
        h *= 2
    return a


def iwht(F):
    n = len(F)
    return [v / n for v in wht(F)]


def popcount(w):
    return bin(w).count("1")


def shell_bands(n):
    """Band index of each frequency: its Hamming weight."""
    return [popcount(w) for w in range(2 ** n)]


def hopf_bands():
    """Band index of each of the 64 frequencies: 0 for the zero frequency, 1 + r for GF(8) fibre r."""
    from hypercube import hopf
    out = [0] * 64
    for r in range(9):
        for v in hopf.fiber(9, r):
            out[v] = 1 + r
    return out


def octave_bands(n):
    """Dyadic bands by sequency (number of sign changes): band k holds sequency in [2^(k-1), 2^k)."""
    N = 2 ** n
    seq = sequency(n)
    return [0 if seq[w] == 0 else seq[w].bit_length() for w in range(N)]


def sequency(n):
    """Number of sign changes of each Walsh function (natural order)."""
    N = 2 ** n
    out = []
    for w in range(N):
        row = [(-1) ** popcount(w & x) for x in range(N)]
        out.append(sum(1 for a, b in zip(row, row[1:]) if a != b))
    return out


def gain(f, g):
    """Equalizer: multiply frequency w by g[w], transform back (Lean `gain`)."""
    F = wht(f)
    return iwht([gw * Fw for gw, Fw in zip(g, F)])


def split(f, bands):
    """Split f into components, one per band label; they add back to f (Lean `sum_shells`,
    `band_add_compl`)."""
    F = wht(f)
    labels = sorted(set(bands))
    return {b: iwht([Fw if bw == b else 0 for bw, Fw in zip(bands, F)]) for b in labels}


def join(components):
    comps = list(components.values())
    return [sum(c[i] for c in comps) for i in range(len(comps[0]))]


def energy(f):
    return sum(v * v for v in f)


def band_energy(f, bands):
    return {b: energy(c) for b, c in split(f, bands).items()}


def denoise(f, threshold=None, soft=True, keep_dc=True):
    """Shrink small Walsh coefficients.  Default threshold: the universal threshold
    sigma * sqrt(2 ln N), sigma estimated from the median absolute coefficient of the upper half
    of the shells (Donoho-Johnstone style, adapted to the Walsh basis)."""
    N = len(f)
    F = wht(f)
    norm = math.sqrt(N)
    C = [v / norm for v in F]  # orthonormal coefficients
    if threshold is None:
        n = N.bit_length() - 1
        hi = [abs(C[w]) for w in range(N) if popcount(w) > n // 2]
        hi.sort()
        sigma = (hi[len(hi) // 2] / 0.6745) if hi else 0.0
        threshold = sigma * math.sqrt(2 * math.log(N))
    out = []
    for w, c in enumerate(C):
        if keep_dc and w == 0:
            out.append(c)
        elif abs(c) <= threshold:
            out.append(0.0)
        else:
            out.append(c - math.copysign(threshold, c) if soft else c)
    return iwht([c * norm for c in out]), threshold


def chip(f, bands, remove):
    """Chip away the bands in `remove` (gain 0)."""
    return gain(f, [0 if b in remove else 1 for b in bands])


def blowup(f, bands, boost):
    """Blow up bands: boost = {band: gain}."""
    return gain(f, [boost.get(b, 1) for b in bands])


def upsample_double(f):
    """Cayley-Dickson style doubling of a signal: (f, f) on Q_{n+1}.  Its spectrum is (2F, 0):
    the doubled signal lives entirely in the half of the spectrum with the new coordinate 0."""
    return list(f) + list(f)


def blocks(samples, n=6, pad=0):
    N = 2 ** n
    s = list(samples)
    if len(s) % N:
        s += [pad] * (N - len(s) % N)
    return [s[i:i + N] for i in range(0, len(s), N)]
