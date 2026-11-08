"""Print the Burau / Alexander test vectors of ``Formal/BraidBurauCert.lean``.

Each vector is ``(n, word, exp_min, width, coefficients, alexander, k, ε)``: the
certificate fields of :func:`qbx_ir.burau_ledger.burau_values`, plus the witnesses
``k``, ``ε`` with ``alexander(t) · (1 + ⋯ + t^{n-1}) = ε t^k det(I - ρ̄(B))``.
Run from ``QBX/`` with ``PYTHONPATH=src``.
"""

from qbx_ir.algebra.laurent import Laurent, det
from qbx_ir.algebra.polynomial_invariants import burau_matrix
from qbx_ir.burau_ledger import burau_values
from qbx_ir.core.braid import Braid

VECTORS = [
    (1, []),
    (2, []),
    (2, [1]),
    (2, [-1]),
    (2, [1, 1, 1]),
    (2, [-1, -1, -1]),
    (3, [1, 2, 1]),
    (3, [2, 1, 2]),
    (3, [1, -2, 1, -2]),
    (3, [1, -1]),
    (3, [1, -2]),
    (3, [1, 2]),
    (3, [-1, -2]),
    (3, [1, 1, 2, 2, -1, -1, -2, -2]),
    (4, [1, 2, 3]),
    (4, [1, -2, 3, -2]),
    (4, [1, 3, -2, 2]),
]


def witnesses(n, w):
    if n == 1:
        return 0, 1
    b = burau_matrix(Braid.from_short_form(n, w))
    m = n - 1
    d = det([[(Laurent.const(1) if r == c else Laurent()) - b[r][c] for c in range(m)]
             for r in range(m)])
    if d.is_zero():
        return 0, 1
    q = d.divmod_exact(Laurent({k: 1 for k in range(n)}))
    lo = q.min_degree()
    sign = 1 if q.coeffs[lo] > 0 else -1
    return -lo, sign


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def main():
    rows = []
    for n, w in VECTORS:
        v = burau_values(n, w)
        k, e = witnesses(n, w)
        rows.append(f"({n}, {lean_list(w)}, {v.exp_min}, {v.width}, {lean_list(v.coefficients)}, "
                    f"{lean_list(v.alexander)}, {k}, {e})")
    print("[" + ",\n ".join(rows) + "]")


if __name__ == "__main__":
    main()
