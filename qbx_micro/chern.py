"""Chern numbers of two-band lattice models, integer by construction.

A two-band Bloch Hamiltonian is H(k) = d(k) . sigma, i.e. the grade-1 element
d_x e1 + d_y e2 + d_z e3 of Cl(3, 0) acting through the Pauli matrices.  Its
lower band has a Chern number, computed here in two independent ways:

* `chern_fhs`: the Fukui-Hatsugai-Suzuki lattice field strength.  On an N x N
  grid each plaquette contributes the principal argument of a product of four
  link variables; the sum is 2 pi times an integer for every N (the links
  cancel in pairs), and for N large compared with the inverse gap it equals
  the Chern number.
* `chern_degree`: the degree of d / |d| : T^2 -> S^2, the sum of signed solid
  angles of the image triangles divided by 4 pi (Van Oosterom-Strackee).

Both are integers up to floating-point rounding; `chern` rounds, and reports
the distance to the nearest integer and whether the two methods agree.  The
methods are standard; neither is formalised in this repository (see
`sovereign/Sovereign/Metamaterial/ChernNumber.lean` for the Lean side).

Dependency-free (math and builtin complex), MicroPython-compatible.
"""

import math


def qwz(m):
    """Qi-Wu-Zhang model: d = (sin kx, sin ky, m + cos kx + cos ky)."""
    def d(kx, ky):
        return (math.sin(kx), math.sin(ky), m + math.cos(kx) + math.cos(ky))
    return d


def qwz_winding(m, q):
    """Higher-winding variant: (d_x + i d_y) = (sin kx + i sin ky)^q."""
    def d(kx, ky):
        z = complex(math.sin(kx), math.sin(ky)) ** q
        return (z.real, z.imag, m + math.cos(kx) + math.cos(ky))
    return d


def lower_state(d):
    """A normalised lower-band eigenvector of d . sigma (gauge chosen per point)."""
    dx, dy, dz = d
    r = math.sqrt(dx * dx + dy * dy + dz * dz)
    if r == 0:
        raise ValueError("gap closes: d = 0")
    u1 = (complex(dx, -dy), complex(-(dz + r), 0))
    u2 = (complex(dz - r, 0), complex(dx, dy))
    n1 = abs(u1[0]) ** 2 + abs(u1[1]) ** 2
    n2 = abs(u2[0]) ** 2 + abs(u2[1]) ** 2
    u, nn = (u1, n1) if n1 >= n2 else (u2, n2)
    s = math.sqrt(nn)
    return (u[0] / s, u[1] / s)


def _link(u, v):
    z = (complex(u[0].real, -u[0].imag) * v[0]
         + complex(u[1].real, -u[1].imag) * v[1])
    a = abs(z)
    if a == 0:
        raise ValueError("link variable vanishes: refine the grid")
    return z / a


def _arg(z):
    return math.atan2(z.imag, z.real)


def chern_fhs(d, n=48):
    states = [[lower_state(d(2 * math.pi * i / n, 2 * math.pi * j / n)) for j in range(n)]
              for i in range(n)]
    total = 0.0
    min_gap = None
    for i in range(n):
        for j in range(n):
            u00 = states[i][j]
            u10 = states[(i + 1) % n][j]
            u11 = states[(i + 1) % n][(j + 1) % n]
            u01 = states[i][(j + 1) % n]
            prod = _link(u00, u10) * _link(u10, u11) * _link(u11, u01) * _link(u01, u00)
            total += _arg(prod)
    return total / (2 * math.pi)


def _solid_angle(a, b, c):
    """Signed solid angle of the spherical triangle with unit vertices a, b, c."""
    def dot(x, y):
        return x[0] * y[0] + x[1] * y[1] + x[2] * y[2]
    triple = (a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
              + a[2] * (b[0] * c[1] - b[1] * c[0]))
    den = 1 + dot(a, b) + dot(b, c) + dot(c, a)
    return 2 * math.atan2(triple, den)


def chern_degree(d, n=48):
    def unit(v):
        r = math.sqrt(v[0] ** 2 + v[1] ** 2 + v[2] ** 2)
        return (v[0] / r, v[1] / r, v[2] / r)
    pts = [[unit(d(2 * math.pi * i / n, 2 * math.pi * j / n)) for j in range(n)] for i in range(n)]
    total = 0.0
    for i in range(n):
        for j in range(n):
            p00, p10 = pts[i][j], pts[(i + 1) % n][j]
            p11, p01 = pts[(i + 1) % n][(j + 1) % n], pts[i][(j + 1) % n]
            total += _solid_angle(p00, p10, p11) + _solid_angle(p00, p11, p01)
    return total / (4 * math.pi)


def chern(d, n=48):
    """Both Chern numbers of the two-band model, as integers, with diagnostics.

    'degree'      degree of d/|d| = (1/4 pi) sum of solid angles: the convention of
                  `chernNumber` in `sovereign/Sovereign/Metamaterial/ChernNumber.lean`
                  (QWZ: -1 for 0 < m < 2, +1 for -2 < m < 0, 0 for |m| > 2, proved there)
    'berry_lower' FHS lattice Berry-curvature Chern number of the lower band; equals
                  -degree (as stated in that file)
    'agree'       berry_lower == -degree after rounding
    'rounding'    distance of the raw sums from the integers
    """
    f = chern_fhs(d, n)
    g = chern_degree(d, n)
    cf, cg = int(round(f)), int(round(g))
    return {"degree": cg, "berry_lower": cf, "agree": cf == -cg,
            "rounding": max(abs(f - cf), abs(g - cg)), "fhs_raw": f, "degree_raw": g}


def phase_diagram(model, masses, n=48):
    """[(m, degree)] for a family of models indexed by m."""
    return [(m, chern(model(m), n)["degree"]) for m in masses]
