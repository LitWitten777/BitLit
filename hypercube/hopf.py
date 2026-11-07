"""Hopf fibrations of the hypercube Q6 (finite-field analogue of S^1 -> S^3 -> S^2).

The 64 cells (6-bit numbers, XOR = addition) are read as the field GF(64) = GF(2)[x]/(x^6+x+1).
For each subfield K of GF(64) -- GF(2), GF(4), GF(8), GF(64) -- the Hopf projection sends a
non-zero cell to the K-line it spans; in logarithmic coordinates it is  v -> dlog(v) mod m,
m = 63/(|K|-1) = 63, 21, 9, 1.  The fibre is the unit group K^x.

Proved counterparts (Lean): RequestProject/HypercubeHopf.lean (namespace HypercubeHopf).
Standard library only.
"""

POLY = 0b1000011  # x^6 + x + 1 (primitive)
FIELDS = {"GF2": 63, "GF4": 21, "GF8": 9, "GF64": 1}  # field -> number of base points


def xtime(a):
    a <<= 1
    return a ^ POLY if a & 64 else a


def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a, b = xtime(a), b >> 1
    return r


GPOW = [1]
for _ in range(62):
    GPOW.append(xtime(GPOW[-1]))
DLOG = {v: k for k, v in enumerate(GPOW)}

F8 = [0] + [GPOW[9 * j] for j in range(7)]
F4 = [0] + [GPOW[21 * j] for j in range(3)]


def hopf(m, v):
    """Base point of cell v (v != 0) under the projection with m base points."""
    return DLOG[v] % m


def fiber(m, r):
    return sorted(v for v in range(1, 64) if hopf(m, v) == r)


def weight(v):
    return bin(v).count("1")


def f8_coords(v):
    """(a, b) in GF(8)^2 with v = a + b*x."""
    return next((a, b) for a in F8 for b in F8 if a ^ gmul(b, 2) == v)


def base_point_PG18(v):
    """Point [a:b] of PG(1,8) as an affine coordinate t = b/a in GF(8), or 'inf'."""
    a, b = f8_coords(v)
    if a == 0:
        return "inf"
    inv_a = next(c for c in F8 if gmul(a, c) == 1)
    return gmul(b, inv_a)


def edge_matrix(m=9):
    M = [[0] * m for _ in range(m)]
    for u in range(1, 64):
        for i in range(6):
            w = u ^ (1 << i)
            if w:
                M[hopf(m, u)][hopf(m, w)] += 1
    return M


def cell_table():
    rows = []
    for v in range(64):
        row = {"cell": v, "bits": format(v, "06b"), "weight": weight(v)}
        if v:
            row.update({"dlog": DLOG[v], "GF4_line": hopf(21, v), "GF8_line": hopf(9, v),
                        "GF8_phase": DLOG[v] % 7, "PG18_point": base_point_PG18(v)})
        rows.append(row)
    return rows


def report():
    M = edge_matrix(9)
    internal = sum(M[r][r] for r in range(9)) // 2
    between = sum(M[r][s] for r in range(9) for s in range(9) if r != s) // 2
    return {
        "field": "GF(64) = GF(2)[x]/(x^6+x+1), generator x = cell 2",
        "fibrations": {k: {"base_points": m, "fiber_size": 63 // m} for k, m in FIELDS.items()},
        "GF8_fibers": {r: {"cells": fiber(9, r), "weights": [weight(v) for v in fiber(9, r)],
                           "PG18_point": base_point_PG18(fiber(9, r)[0])} for r in range(9)},
        "GF4_fibers": {r: fiber(21, r) for r in range(21)},
        "GF8_quotient_edge_matrix": M,
        "Q6_edges": {"at_zero": 6, "inside_GF8_fibers": internal,
                     "between_GF8_fibers": between, "total": 6 + internal + between},
        "transition_function": "s0(t) = t * s_inf(1/t) on GF(8)^x: clutching map t -> t",
        "cells": cell_table(),
    }


def selfcheck():
    assert len(set(GPOW)) == 63 and xtime(GPOW[-1]) == 1
    assert all(len(fiber(9, r)) == 7 for r in range(9))
    assert all(len(fiber(21, r)) == 3 for r in range(21))
    for r in range(9):  # fibres are subspaces
        W = set(fiber(9, r)) | {0}
        assert all(a ^ b in W for a in W for b in W)
    for r in range(9):  # linking: any two fibres are complementary
        for s in range(9):
            if r != s:
                A, B = set(fiber(9, r)) | {0}, set(fiber(9, s)) | {0}
                assert len({a ^ b for a in A for b in B}) == 64
    seen = {(hopf(21, v), hopf(9, v)) for v in range(1, 64)}
    assert len(seen) == 63
    r = report()["Q6_edges"]
    assert (r["inside_GF8_fibers"], r["between_GF8_fibers"], r["total"]) == (18, 168, 192)
    for t in F8[1:]:  # transition function
        u = next(c for c in F8 if gmul(t, c) == 1)
        assert gmul(t, u ^ 2) == 1 ^ gmul(t, 2)
    return True


if __name__ == "__main__":
    import json
    selfcheck()
    print(json.dumps(report(), indent=1, default=str))
