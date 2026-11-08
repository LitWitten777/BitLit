"""The harmonic torus: a grid of oscillating nodes on Z/N x Z/M.

A signal is laid on the N x M nodes in row-major order (excess samples are folded
in by addition, missing ones are zero).  Its modes are the characters
(j, k) -> exp(2 pi i (a j / N + b k / M)); each mode is a harmonic node with
wave vector (a, b).

Oscillation.  `flow(p, q, t)` moves the signal t steps along the (p, q)
direction of the torus -- the direction of the (p, q) torus knot.  In the mode
picture every node only turns its phase, by exp(2 pi i t (a p / N + b q / M)):
each mode oscillates at its own frequency.  What does not move (Lean,
`QBX/Formal/Engine/HarmonicTorus.lean`):

  * the power of each mode           (`power_shift_invariant`)
  * every bispectrum value           (`bispec_shift_invariant`)
  * the total energy, |G| times the signal energy (`spec_parseval`)

`invariants()` returns these, and `check_flow_invariance` recomputes them after
a flow and compares (floating point, tolerance 1e-6 relative).
"""

import cmath
import math

from . import spectrum


class HarmonicTorus:
    def __init__(self, N=16, M=16):
        self.N, self.M = N, M
        self.grid = [[0.0] * M for _ in range(N)]

    def load(self, samples):
        N, M = self.N, self.M
        g = [[0.0] * M for _ in range(N)]
        for i, x in enumerate(samples):
            p = i % (N * M)
            g[p // M][p % M] += x
        self.grid = g
        return self

    def spectrum(self):
        return spectrum.dft2(self.grid)

    def flow(self, p, q, t=1):
        """Move the signal t steps along direction (p, q) (a torus-knot direction)."""
        N, M = self.N, self.M
        g = self.grid
        self.grid = [[g[(j + t * p) % N][(k + t * q) % M] for k in range(M)] for j in range(N)]
        return self

    def oscillate_modes(self, p, q, t):
        """The same flow computed node by node in the mode picture: turn the phase of
        mode (a, b) by exp(2 pi i t (a p / N + b q / M)) and transform back."""
        N, M = self.N, self.M
        S = self.spectrum()
        S2 = [[S[a][b] * cmath.exp(2j * math.pi * t * (a * p / N + b * q / M))
               for b in range(M)] for a in range(N)]
        back = spectrum.idft2(S2)
        return [[back[j][k].real for k in range(M)] for j in range(N)]

    def invariants(self, nbi=4):
        N, M = self.N, self.M
        S = self.spectrum()
        power = [[abs(S[a][b]) ** 2 for b in range(M)] for a in range(N)]
        nb = 1 + max(spectrum.torus_band(a, b, N, M) for a in range(N) for b in range(M))
        bands = [0.0] * nb
        for a in range(N):
            for b in range(M):
                bands[spectrum.torus_band(a, b, N, M)] += power[a][b]
        bis = {}
        for a1 in range(min(nbi, N)):
            for a2 in range(min(nbi, N)):
                m1, m2 = (a1, 1 % M), (a2, 2 % M)
                m3 = ((a1 + a2) % N, 3 % M)
                v = S[m1[0]][m1[1]] * S[m2[0]][m2[1]] * S[m3[0]][m3[1]].conjugate()
                bis["%d,%d|%d,%d" % (m1 + m2)] = [v.real, v.imag]
        energy = sum(x * x for row in self.grid for x in row)
        return {
            "energy": energy,
            "mode_energy": sum(map(sum, power)),
            "band_energy": bands,
            "colours": [spectrum.colour_of_band(b, nb) for b in range(nb)],
            "bispectrum": bis,
            "power": power,
        }


def _close(x, y, tol=1e-6):
    return abs(x - y) <= tol * (1.0 + abs(x) + abs(y))


def check_flow_invariance(samples, N=8, M=8, p=1, q=2, t=3):
    """Recompute the invariants after a (p, q) flow and compare; dict name -> bool."""
    T = HarmonicTorus(N, M).load(samples)
    before = T.invariants()
    mode_pic = T.oscillate_modes(p, q, t)
    T.flow(p, q, t)
    after = T.invariants()
    out = {
        "parseval": _close(before["mode_energy"], N * M * before["energy"]),
        "power": all(_close(before["power"][a][b], after["power"][a][b])
                     for a in range(N) for b in range(M)),
        "bispectrum": all(_close(before["bispectrum"][k][i], after["bispectrum"][k][i])
                          for k in before["bispectrum"] for i in (0, 1)),
        "flow_is_mode_oscillation": all(_close(mode_pic[j][k], T.grid[j][k])
                                        for j in range(N) for k in range(M)),
    }
    return out
