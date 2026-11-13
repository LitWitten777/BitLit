"""
Computational Analysis & Falsification of the 2-Generated Subalgebra Theorem (OP-008, HYP-113).

Analyzes whether every 2-generated subalgebra in a Cayley-Dickson algebra is associative
(the Artin-style theorem for the Cayley-Dickson tower).

Mathematical Reality:
1. Basis Generation:
   For any two basis vectors e_a, e_b in any dimension D = 2^n, the index span {0, a, b, a ^ b}
   generates an associative subalgebra isomorphic to R, C, or H (TowerAlternative.lean).
2. General Linear Combinations:
   Artin's Theorem states that an algebra is alternative IF AND ONLY IF every 2-generated
   subalgebra is associative.
3. Non-Alternativity Obstruction:
   Since all Cayley-Dickson algebras of dimension D = 2^n >= 16 are strictly non-alternative,
   there exist elements x, y whose generated subalgebra Alg(x, y) is NON-ASSOCIATIVE.
4. Concrete Integer Witness:
   In dimension 16 (and canonically embedded in all D >= 16):
       x_wit = e_1 + e_10
       y_wit = e_4
   We have:
       x^2 = -2 * e_0
       x^2 * y = -2 * e_4
       x * (x * y) = -2 * e_4 - 2 * e_15
   The associator is strictly non-zero:
       [x, x, y] = (x^2)*y - x*(x*y) = 2 * e_15 != 0.
   Therefore, Alg(x, y) contains elements x, x^2, y, x*y, x*(x*y) that do not associate,
   formally FALSIFYING the 2-generated subalgebra conjecture for all D >= 16.
"""

from __future__ import annotations

from typing import Any
import numpy as np

from sedenion.cd_algebra import build_cd_multiplication_table


def cd_multiply(a: np.ndarray, b: np.ndarray, signs: np.ndarray, idxs: np.ndarray) -> np.ndarray:
    """Exact Cayley-Dickson multiplication of two vectors."""
    dim = len(a)
    c = np.zeros(dim, dtype=int if np.issubdtype(a.dtype, np.integer) else float)
    for i in range(dim):
        if a[i] == 0:
            continue
        for j in range(dim):
            if b[j] == 0:
                continue
            k = idxs[i, j]
            s = signs[i, j]
            c[k] += a[i] * b[j] * s
    return c


def cd_associator(
    x: np.ndarray, y: np.ndarray, z: np.ndarray, signs: np.ndarray, idxs: np.ndarray
) -> np.ndarray:
    """Computes the associator [x, y, z] = (x * y) * z - x * (y * z)."""
    xy = cd_multiply(x, y, signs, idxs)
    xy_z = cd_multiply(xy, z, signs, idxs)
    yz = cd_multiply(y, z, signs, idxs)
    x_yz = cd_multiply(x, yz, signs, idxs)
    return xy_z - x_yz


def get_canonical_falsification_witness(dim: int = 16) -> dict[str, Any]:
    """
    Constructs the exact integer witness x = e_1 + e_10, y = e_4 in dimension `dim >= 16`.
    Returns evaluation certificate demonstrating non-associativity of Alg(x, y).
    """
    if not (dim >= 16 and (dim & (dim - 1)) == 0):
        raise ValueError(f"dim must be a power of 2 >= 16, got {dim}")

    signs, idxs = build_cd_multiplication_table(dim)

    x = np.zeros(dim, dtype=int)
    x[1] = 1
    x[10] = 1

    y = np.zeros(dim, dtype=int)
    y[4] = 1

    x2 = cd_multiply(x, x, signs, idxs)
    x2_y = cd_multiply(x2, y, signs, idxs)
    xy = cd_multiply(x, y, signs, idxs)
    x_xy = cd_multiply(x, xy, signs, idxs)

    assoc_xxy = x2_y - x_xy

    # Expected value: 2 * e_15
    expected_assoc = np.zeros(dim, dtype=int)
    expected_assoc[15] = 2

    is_exact_match = bool(np.array_equal(assoc_xxy, expected_assoc))
    is_non_associative = bool(np.any(assoc_xxy != 0))

    return {
        "dim": dim,
        "x": x,
        "y": y,
        "x_squared": x2,
        "x2_y": x2_y,
        "x_xy": x_xy,
        "associator_xxy": assoc_xxy,
        "is_non_zero_associator": is_non_associative,
        "matches_2_e15": is_exact_match,
        "subalgebra_is_associative": not is_non_associative,
        "is_falsified": is_non_associative,
    }


def verify_basis_subalgebra_associativity(dim: int = 16) -> dict[str, Any]:
    """
    Verifies that ANY two single basis vectors e_a, e_b generate an associative subalgebra.
    """
    signs, idxs = build_cd_multiplication_table(dim)
    all_basis_associate = True

    # Test sample of basis pairs
    for a in range(dim):
        ea = np.zeros(dim, dtype=int)
        ea[a] = 1
        for b in range(dim):
            eb = np.zeros(dim, dtype=int)
            eb[b] = 1
            eab = cd_multiply(ea, eb, signs, idxs)

            # Check generators self-alternativity: [ea, ea, eb] == 0, [ea, eb, eb] == 0
            if np.any(cd_associator(ea, ea, eb, signs, idxs) != 0):
                all_basis_associate = False
                break
            if np.any(cd_associator(ea, eb, eb, signs, idxs) != 0):
                all_basis_associate = False
                break
            if np.any(cd_associator(ea, eb, ea, signs, idxs) != 0):
                all_basis_associate = False
                break
            if np.any(cd_associator(ea, eb, eab, signs, idxs) != 0):
                all_basis_associate = False
                break
        if not all_basis_associate:
            break

    return {
        "dim": dim,
        "basis_subalgebras_all_associative": all_basis_associate,
    }
