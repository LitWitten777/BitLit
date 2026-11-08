"""The merkaba and its controls.

The cube's 8 vertices are bit triples x in {0,1}^3 (drawn at c = 1 - 2x in
{+-1}^3).  The merkaba is the pair of tetrahedra of even-weight and odd-weight
vertices.  Controls (Lean `MCtl`, `QBX/Formal/Engine/Controls.lean`; the cube
symmetry (v, pi) acts by x'_i = x_{pi^-1 i} xor v_i):

  turnX, turnY, turnZ   quarter turns about the three axes   (swap the tetrahedra)
  diag                  120 deg turn about the 000-111 diagonal (keeps them)
  invert                central inversion                       (swaps them)
  spin                  counter-rotation: the even tetrahedron turns by `diag`,
                        the odd one the other way (keeps them)

Proved in Lean and re-checked here (`checks`):

  MCtl.swap_spec            each control keeps/swaps the tetrahedra as listed
  MCtl.order                orders 4, 4, 4, 3, 2
  MCtl.isometry             rigid controls keep every cube distance
  counterSpin_parity/order  spin keeps both tetrahedra and has order 3
  counterSpin_not_isometry  spin is not a rigid motion of the cube
  counterSpin_unreachable   no sequence of rigid controls produces spin

The last fact is why `spin` is a control of its own: the rigid controls generate
exactly the 48 symmetries of the cube (computed below), and spin is not one of
them.
"""

import math

VERTS = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
IDX = {v: i for i, v in enumerate(VERTS)}


def weight(x):
    return sum(x)


def coords(x):
    return tuple(1 - 2 * b for b in x)


def hamming(x, y):
    return sum(a != b for a, b in zip(x, y))


def _cube_sym(v, pinv):
    """x'_i = x[pinv[i]] xor v[i]."""
    return lambda x: tuple(x[pinv[i]] ^ v[i] for i in range(3))


RIGID = {
    "turnX": _cube_sym((0, 1, 0), (0, 2, 1)),
    "turnY": _cube_sym((0, 0, 1), (2, 1, 0)),
    "turnZ": _cube_sym((1, 0, 0), (1, 0, 2)),
    "diag": _cube_sym((0, 0, 0), (2, 0, 1)),
    "invert": _cube_sym((1, 1, 1), (0, 1, 2)),
}
SWAPS = {"turnX": True, "turnY": True, "turnZ": True, "diag": False, "invert": True,
         "spin": False}


def spin(x):
    d = RIGID["diag"]
    return d(x) if weight(x) % 2 == 0 else d(d(x))


CONTROLS = dict(RIGID, spin=spin)

# 3 x 3 matrices of the rigid controls on the drawing coordinates c = 1 - 2x
# (used by the UI for smooth animation; `matrix_check` verifies them).
MATRIX = {
    "turnX": ((1, 0, 0), (0, 0, -1), (0, 1, 0)),
    "turnY": ((0, 0, 1), (0, 1, 0), (-1, 0, 0)),
    "turnZ": ((0, -1, 0), (1, 0, 0), (0, 0, 1)),
    "diag": ((0, 0, 1), (1, 0, 0), (0, 1, 0)),
    "invert": ((-1, 0, 0), (0, -1, 0), (0, 0, -1)),
}


def _as_perm(f):
    return tuple(IDX[f(v)] for v in VERTS)


def _compose(p, q):
    """First q then p (as vertex-index permutations)."""
    return tuple(p[q[i]] for i in range(8))


def rigid_group():
    """All vertex permutations reachable by rigid controls (BFS closure)."""
    gens = [_as_perm(f) for f in RIGID.values()]
    ident = tuple(range(8))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = _compose(s, g)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return seen


class Merkaba:
    """Merkaba state: the vertex map accumulated from the controls applied so far."""

    def __init__(self):
        self.perm = tuple(range(8))
        self.history = []

    def apply(self, control):
        if control not in CONTROLS:
            raise ValueError("unknown merkaba control %r (known: %s)" % (control, ", ".join(CONTROLS)))
        self.perm = _compose(_as_perm(CONTROLS[control]), self.perm)
        self.history.append(control)
        return self

    def run(self, controls):
        for c in controls:
            self.apply(c)
        return self

    def position(self, v):
        return VERTS[self.perm[IDX[v]]]

    def swapped(self):
        """True if the even-labelled tetrahedron now sits on the odd vertices."""
        return weight(self.position((0, 0, 0))) % 2 == 1

    def swap_count(self):
        return sum(1 for c in self.history if SWAPS[c])

    def is_rigid(self):
        return all(hamming(self.position(x), self.position(y)) == hamming(x, y)
                   for x in VERTS for y in VERTS)

    def tetrahedra(self):
        even = [coords(self.position(v)) for v in VERTS if weight(v) % 2 == 0]
        odd = [coords(self.position(v)) for v in VERTS if weight(v) % 2 == 1]
        return {"even": even, "odd": odd}

    def as_dict(self):
        return {"history": list(self.history), "swapped": self.swapped(),
                "swap_count": self.swap_count(), "rigid": self.is_rigid(),
                "tetrahedra": self.tetrahedra(),
                "vertex_map": {"".join(map(str, v)): "".join(map(str, self.position(v)))
                               for v in VERTS}}


def _iterate(f, k, x):
    for _ in range(k):
        x = f(x)
    return x


def matrix_check():
    ok = True
    for name, A in MATRIX.items():
        for x in VERTS:
            c = coords(x)
            Ac = tuple(sum(A[i][j] * c[j] for j in range(3)) for i in range(3))
            if Ac != coords(RIGID[name](x)):
                ok = False
    return ok


def checks():
    ok = {}
    ok["swap_spec"] = all((weight(f(x)) - weight(x)) % 2 == (1 if SWAPS[n] else 0)
                          for n, f in CONTROLS.items() for x in VERTS)
    orders = {"turnX": 4, "turnY": 4, "turnZ": 4, "diag": 3, "invert": 2, "spin": 3}
    ok["orders"] = all(
        all(_iterate(CONTROLS[n], k, x) == x for x in VERTS) and
        all(any(_iterate(CONTROLS[n], j, x) != x for x in VERTS) for j in range(1, k))
        for n, k in orders.items())
    ok["rigid_isometry"] = all(hamming(f(x), f(y)) == hamming(x, y)
                               for f in RIGID.values() for x in VERTS for y in VERTS)
    ok["spin_not_isometry"] = any(hamming(spin(x), spin(y)) != hamming(x, y)
                                  for x in VERTS for y in VERTS)
    G = rigid_group()
    ok["rigid_group_order_48"] = len(G) == 48
    ok["spin_unreachable"] = _as_perm(spin) not in G
    ok["matrices"] = matrix_check()
    return ok


def svg(state=None, size=360, title="Merkaba"):
    """A static figure of the merkaba in its current orientation, with the control legend."""
    state = state or Merkaba()
    tet = state.tetrahedra()
    az, el = math.radians(35), math.radians(25)

    def proj(c):
        x, y, z = c
        X = x * math.cos(az) - y * math.sin(az)
        Y = x * math.sin(az) + y * math.cos(az)
        Z = z * math.cos(el) - Y * math.sin(el)
        s = size * 0.28
        return (size / 2 + s * X, size / 2 - s * Z)

    parts = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" '
             'viewBox="0 0 %d %d" font-family="sans-serif">' % (size, size + 90, size, size + 90),
             '<rect width="100%" height="100%" fill="#0d1117"/>',
             '<text x="12" y="22" fill="#e6edf3" font-size="15">%s</text>' % title]
    for v in VERTS:
        for w in VERTS:
            if v < w and hamming(v, w) == 1:
                (x1, y1), (x2, y2) = proj(coords(v)), proj(coords(w))
                parts.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#30363d" '
                             'stroke-dasharray="3,3"/>' % (x1, y1, x2, y2))
    for key, colour in (("even", "#e8a33d"), ("odd", "#3d7be8")):
        pts = tet[key]
        for i in range(4):
            for j in range(i + 1, 4):
                (x1, y1), (x2, y2) = proj(pts[i]), proj(pts[j])
                parts.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" '
                             'stroke-width="2.5"/>' % (x1, y1, x2, y2, colour))
        for p in pts:
            x, y = proj(p)
            parts.append('<circle cx="%.1f" cy="%.1f" r="4" fill="%s"/>' % (x, y, colour))
    legend = ["history: " + (" ".join(state.history[-6:]) or "(none)"),
              "swapped: %s   swaps so far: %d" % (state.swapped(), state.swap_count()),
              "rigid motion of the cube: %s" % state.is_rigid()]
    for i, line in enumerate(legend):
        parts.append('<text x="12" y="%d" fill="#8b949e" font-size="11">%s</text>'
                     % (size + 25 + 18 * i, line))
    parts.append("</svg>")
    return "\n".join(parts)


def controls_figure(size=240):
    """Figure: the merkaba at rest and after each single control, side by side."""
    panels = [("start", [])] + [(c, [c]) for c in CONTROLS]
    cols = 4
    rows = (len(panels) + cols - 1) // cols
    ph = size + 90
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d">' % (cols * size, rows * ph),
           '<rect width="100%" height="100%" fill="#0d1117"/>']
    for i, (name, ctl) in enumerate(panels):
        inner = svg(Merkaba().run(ctl), size=size, title=name)
        inner = inner.replace("<svg ", '<svg x="%d" y="%d" ' % ((i % cols) * size, (i // cols) * ph), 1)
        out.append(inner)
    out.append("</svg>")
    return "\n".join(out)
