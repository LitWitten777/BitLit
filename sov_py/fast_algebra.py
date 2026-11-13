"""
Fast Bit-Vectorized Cayley-Dickson Algebra Engine.

Exploits the fundamental bitwise XOR group structure of Cayley-Dickson basis multiplication:
    e_i * e_j = omega(i, j) * e_{i ^ j}
where omega(i, j) in {+1, -1} is precomputed into a static 16x16 table.

Also implements the XOR charge conservation law:
    u * w = 0  ==>  u.i ^ u.j == w.i ^ w.j
which partitions the zero-divisor space into 7 charge sectors chi in {1..7}.
"""

from .algebra import Sedenion


def _build_sedenion_sign_table() -> tuple[tuple[int, ...], ...]:
    """Generates the exact 16x16 sign matrix omega(i, j) using the canonical CD engine."""
    table = []
    for i in range(16):
        row = []
        ei = Sedenion.basis(i)
        for j in range(16):
            ej = Sedenion.basis(j)
            prod = ei * ej
            target_idx = i ^ j
            sign = prod.coords[target_idx]
            row.append(sign)
        table.append(tuple(row))
    return tuple(table)


# Precomputed static sign lookup table (16x16)
SEDENION_SIGN_TABLE: tuple[tuple[int, ...], ...] = _build_sedenion_sign_table()


def fast_basis_mult(i: int, j: int) -> tuple[int, int]:
    """
    Computes e_i * e_j in O(1) bitwise operations.
    Returns (sign, product_index) such that e_i * e_j = sign * e_{product_index}.
    """
    return SEDENION_SIGN_TABLE[i][j], i ^ j


def fast_is_cross_octet_zd(i: int, j: int) -> bool:
    """
    Tests whether cross-octet vector (+/- e_i +/- e_{8+j}) is a zero divisor in O(1).
    Theorem: Zero divisor <=> i != 0 and j != 0 and i != j.
    """
    return i != 0 and j != 0 and i != j


def fast_xor_charge(i: int, j: int) -> int:
    """
    Computes the conserved XOR charge chi = i ^ j in {1..7}.
    Determines which of the 7 Ramanujan components the zero divisor belongs to.
    """
    return i ^ j


def fast_annihilate_cross_octet(
    u_i: int, u_j: int, u_s1: int, u_s2: int, w_k: int, w_m: int, w_t1: int, w_t2: int
) -> bool:
    """
    Evaluates mutual annihilation u * w = 0 in O(1) integer operations.
    u = u_s1 * e_{u_i} + u_s2 * e_{8+u_j}
    w = w_t1 * e_{w_k} + w_t2 * e_{8+w_m}
    """
    # Conservation law: charges must match
    if (u_i ^ u_j) != (w_k ^ w_m):
        return False

    # Low octet cancellation: s1*t1*omega(i, k) + s2*t2*omega(8+j, 8+m) == 0
    sign_low = (
        u_s1 * w_t1 * SEDENION_SIGN_TABLE[u_i][w_k]
        + u_s2 * w_t2 * SEDENION_SIGN_TABLE[8 + u_j][8 + w_m]
    )
    if sign_low != 0:
        return False

    # High octet cancellation: s1*t2*omega(i, 8+m) + s2*t1*omega(8+j, k) == 0
    sign_high = (
        u_s1 * w_t2 * SEDENION_SIGN_TABLE[u_i][8 + w_m]
        + u_s2 * w_t1 * SEDENION_SIGN_TABLE[8 + u_j][w_k]
    )
    return sign_high == 0


def fast_bipartite_color(i: int, j: int, s1: int, s2: int) -> int:
    """
    Computes the bipartite 2-coloring sign (+1 or -1) of a zero divisor:
        Color(u) = s1 * s2 * omega(i, j)
    where omega(i, j) is the Cayley-Dickson multiplication sign.
    Theorem: u and w can annihilate only if fast_bipartite_color(u) == -fast_bipartite_color(w).
    """
    return s1 * s2 * SEDENION_SIGN_TABLE[i][j]
