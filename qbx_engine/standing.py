"""Standing waves on the harmonic torus.

The standing wave of a signal g at time t along the (p, q) direction is the sum of
the wave moved forward and the wave moved backward:

    S_t(j, k) = g(j + t p, k + t q) + g(j - t p, k - t q).

Lean (`QBX/Formal/Engine/Waves.lean`):

  spec_standing          mode (a, b) of S_t = (psi + conj psi) * mode (a, b) of g,
                         psi = exp(2 pi i t (a p / N + b q / M))
  standing_factor_eq     the factor is the real number 2 cos(2 pi t (a p / N + b q / M))
  standing_phase_locked  so no mode turns: every mode only breathes
  standing_node          modes with factor 0 are silent at time t (nodes)
  standing_time_reversal S_{-t} = S_t

The motion repeats with period lcm(N / gcd(N, p), M / gcd(M, q))
(`joint_period`: the joint period of two cyclic clocks is the lcm).
"""

import cmath
import math

from . import spectrum


def standing(grid, p, q, t):
    N, M = len(grid), len(grid[0])
    return [[grid[(j + t * p) % N][(k + t * q) % M] + grid[(j - t * p) % N][(k - t * q) % M]
             for k in range(M)] for j in range(N)]


def factor(a, b, N, M, p, q, t):
    return 2.0 * math.cos(2.0 * math.pi * t * (a * p / N + b * q / M))


def period(N, M, p, q):
    tN = N // math.gcd(N, p % N or N)
    tM = M // math.gcd(M, q % M or M)
    return tN * tM // math.gcd(tN, tM)


def nodes(N, M, p, q, t, tol=1e-9):
    return [(a, b) for a in range(N) for b in range(M) if abs(factor(a, b, N, M, p, q, t)) < tol]


def frames(grid, p, q, count=None):
    """One standing-wave grid per tick over a full period."""
    N, M = len(grid), len(grid[0])
    T = period(N, M, p, q)
    count = T if count is None else min(count, T)
    return [standing(grid, p, q, t) for t in range(count)], T


def _close(x, y, tol=1e-6):
    return abs(x - y) <= tol * (1.0 + abs(x) + abs(y))


def check(grid, p=1, q=2, t=3):
    N, M = len(grid), len(grid[0])
    S = spectrum.dft2(grid)
    St = spectrum.dft2(standing(grid, p, q, t))
    ok = {"mode_factor": True, "phase_locked": True, "nodes_silent": True}
    for a in range(N):
        for b in range(M):
            psi = cmath.exp(2j * math.pi * t * (a * p / N + b * q / M))
            f = psi + psi.conjugate()
            if not (_close(St[a][b].real, (f * S[a][b]).real) and
                    _close(St[a][b].imag, (f * S[a][b]).imag)):
                ok["mode_factor"] = False
            if abs(f.imag) > 1e-9 or not _close(f.real, factor(a, b, N, M, p, q, t)):
                ok["phase_locked"] = False
    for a, b in nodes(N, M, p, q, t):
        if abs(St[a][b]) > 1e-6 * (1 + sum(abs(x) for row in grid for x in row)):
            ok["nodes_silent"] = False
    ok["time_reversal"] = standing(grid, p, q, -t) == standing(grid, p, q, t)
    T = period(N, M, p, q)
    ok["period"] = standing(grid, p, q, t + T) == standing(grid, p, q, t)
    return ok


def sonify(grid, p=1, q=1, seconds=2.0, rate=8000, f0=110.0, top=8):
    """Audio of the standing wave: the `top` strongest modes, each a partial whose amplitude
    breathes with its standing-wave factor (one torus tick per 1/8 s).  Floats in [-1, 1]."""
    N, M = len(grid), len(grid[0])
    S = spectrum.dft2(grid)
    # Only partials below half the sample rate can be represented; a partial above it would be
    # heard at a different (folded) frequency (`alias_fold`, `QBX/Formal/Engine/Reality.lean`).
    nyquist = rate / 2.0
    modes = sorted(((abs(S[a][b]), a, b) for a in range(N) for b in range(M)
                    if (a, b) != (0, 0) and f0 * (1 + a + b) < nyquist), reverse=True)[:top]
    if not modes or modes[0][0] == 0:
        return [0.0] * int(seconds * rate)
    out = []
    for n in range(int(seconds * rate)):
        s = n / rate
        t = s * 8.0
        v = 0.0
        for amp, a, b in modes:
            fac = 2.0 * math.cos(2.0 * math.pi * t * (a * p / N + b * q / M))
            v += amp * fac * math.sin(2.0 * math.pi * f0 * (1 + a + b) * s)
        out.append(v)
    peak = max(abs(x) for x in out) or 1.0
    return [x / peak for x in out]
