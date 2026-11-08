"""Print the Kauffman bracket / Jones test vectors of ``Formal/KauffmanBracket/Vectors``.

Each vector is ``(n, word, bracket_exp_min, bracket_width, bracket_coefficients,
jones_exp_min, jones_width, jones_coefficients)``: the certificate fields of
:func:`qbx_ir.jones_ledger.jones_values` (Jones polynomial in the variable ``A``).
Run from ``QBX/`` with ``PYTHONPATH=src``.
"""

from qbx_ir.algebra.polynomial_invariants import kauffman_bracket, kauffman_bracket_state_sum
from qbx_ir.core.braid import Braid
from qbx_ir.jones_ledger import jones_values

VECTORS = [
    (1, []),
    (2, []),
    (2, [1]),
    (2, [-1]),
    (2, [1, 1]),
    (2, [1, 1, 1]),
    (2, [-1, -1, -1]),
    (3, []),
    (3, [1, 2]),
    (3, [1, -2, 1, -2]),
    (3, [1, 1, 2, 2, -1, -1, -2, -2]),
    (4, [1, 2, 3]),
    (4, [1, -2, 3, -2]),
]


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def main():
    rows = []
    for n, w in VECTORS:
        b = Braid.from_short_form(n, w)
        assert kauffman_bracket(b) == kauffman_bracket_state_sum(b)
        v = jones_values(n, w)
        rows.append(f"({n}, {lean_list(w)}, {v.bracket_exp_min}, {v.bracket_width}, "
                    f"{lean_list(v.bracket_coefficients)}, {v.jones_exp_min}, {v.jones_width}, "
                    f"{lean_list(v.jones_coefficients)})")
    print("[" + ",\n ".join(rows) + "]")


if __name__ == "__main__":
    main()
