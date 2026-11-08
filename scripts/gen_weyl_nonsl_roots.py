#!/usr/bin/env python3
"""Positive roots (simple-root coordinates) for B3, B4, B5, F4, G2, H3, H4.

Convention (matches `QBX/Formal/Streams/WeylCartan.lean`):
  s_i(v) = v - (sum_b C[i][b] v_b) e_i,  C[i][i] = 2.
Entries of H3/H4 live in Z[phi] (phi^2 = phi + 1), written as pairs (a, b) = a + b*phi.
Nothing here is trusted: Lean re-checks every property by `decide +kernel`.
Usage: python3 gen_weyl_nonsl_roots.py  (prints the Lean root lists)
"""

def add(x, y): return (x[0] + y[0], x[1] + y[1])
def mul(x, y): return (x[0] * y[0] + x[1] * y[1], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])
def neg(x): return (-x[0], -x[1])
Z = (0, 0); ONE = (1, 0); PHI = (0, 1)

def cartan(n, edges):
    C = [[Z] * n for _ in range(n)]
    for i in range(n): C[i][i] = (2, 0)
    for (i, j, cij, cji) in edges:
        C[i][j] = cij; C[j][i] = cji
    return C

def refl(C, i, v):
    n = len(v)
    s = Z
    for b in range(n): s = add(s, mul(C[i][b], v[b]))
    w = list(v); w[i] = add(w[i], neg(s))
    return tuple(w)

def nonneg(v): return all(x[0] >= 0 and x[1] >= 0 for x in v)

def pos_roots(C):
    n = len(C)
    simple = [tuple(ONE if a == i else Z for a in range(n)) for i in range(n)]
    roots = list(simple); seen = set(roots); frontier = list(simple)
    while frontier:
        new = []
        for r in frontier:
            for i in range(n):
                if r == simple[i]: continue
                w = refl(C, i, r)
                assert nonneg(w), (r, i, w)
                if w not in seen:
                    seen.add(w); roots.append(w); new.append(w)
        frontier = new
    return roots

m1 = (-1, 0); m2 = (-2, 0); m3 = (-3, 0); mphi = (0, -1)
TYPES = {
    'b3': cartan(3, [(0, 1, m1, m1), (1, 2, m2, m1)]),
    'b4': cartan(4, [(0, 1, m1, m1), (1, 2, m1, m1), (2, 3, m2, m1)]),
    'b5': cartan(5, [(0, 1, m1, m1), (1, 2, m1, m1), (2, 3, m1, m1), (3, 4, m2, m1)]),
    'f4': cartan(4, [(0, 1, m1, m1), (1, 2, m2, m1), (2, 3, m1, m1)]),
    'g2': cartan(2, [(0, 1, m3, m1)]),
    'h3': cartan(3, [(0, 1, m1, m1), (1, 2, mphi, mphi)]),
    'h4': cartan(4, [(0, 1, m1, m1), (1, 2, m1, m1), (2, 3, mphi, mphi)]),
}
EXPECT = {'b3': 9, 'b4': 16, 'b5': 25, 'f4': 24, 'g2': 6, 'h3': 15, 'h4': 60}

def fmt(x, zphi):
    if not zphi: return str(x[0])
    return f"mk {x[0]} {x[1]}" if x[1] else (f"mk {x[0]} 0")

if __name__ == '__main__':
    for name, C in TYPES.items():
        R = pos_roots(C)
        assert len(R) == EXPECT[name], (name, len(R))
        zphi = name.startswith('h')
        assert zphi or all(x[1] == 0 for r in R for x in r)
        body = ",\n  ".join("![" + ", ".join(fmt(x, zphi) for x in r) + "]" for r in R)
        print(f"-- {name}: {len(R)} positive roots")
        print(f"def {name}PosRoots : List (Fin {len(C)} → {'ZPhi' if zphi else 'ℤ'}) := [\n  {body}]\n")
