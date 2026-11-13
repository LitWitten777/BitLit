"""Non-Associative Hydrodynamics, Fano 7D Cross-Product & Sedenion Lamb Cancellation.

Implements the algebraic foundations of non-associative fluid mechanics:
1. 7D octonionic cross-product governed by Fano plane structure constants.
2. The non-associative Jacobi identity defect and its exact relation to the octonionic associator.
3. 16D sedenion commutator cross-product.
4. Lamb vector vanishing criterion and convective stabilization on the 672 zero-divisor annihilation edges.
"""

from __future__ import annotations

import functools
from typing import Any

import numpy as np

from sedenion.cd_algebra import build_cd_multiplication_table
from sedenion.graph import get_cached_annihilation_graph


class NonAssociativeHydroError(ValueError):
    """Raised for dimensional or algebraic errors in non-associative fluids."""


@functools.lru_cache(maxsize=1)
def fano_structure_constants() -> np.ndarray:
    """Compute the 7x7x7 totally antisymmetric structure constant tensor c_{ijk}.

    The indices 0..6 correspond to imaginary octonion units e_1, ..., e_7.
    c_{ijk} = +1 if (i+1, j+1, k+1) is an oriented line in the Fano plane,
    -1 if anti-oriented, and 0 otherwise.
    """
    sign, idx = build_cd_multiplication_table(8)
    c = np.zeros((7, 7, 7), dtype=np.float64)
    for i in range(1, 8):
        for j in range(1, 8):
            k = int(idx[i, j])
            s = float(sign[i, j])
            if k > 0 and i != j:
                # e_i * e_j = s * e_k
                c[i - 1, j - 1, k - 1] = s
    return c


@functools.lru_cache(maxsize=1)
def fano_plane_lines() -> list[tuple[int, int, int]]:
    """Return the 7 oriented Fano lines in 1-based indexing (e_1..e_7).

    Each triple (a, b, c) satisfies e_a * e_b = +e_c under the canonical
    Cayley-Dickson multiplication table.
    """
    sign, idx = build_cd_multiplication_table(8)
    lines: list[tuple[int, int, int]] = []
    seen = set()

    for i in range(1, 8):
        for j in range(1, 8):
            if i == j:
                continue
            k = int(idx[i, j])
            s = int(sign[i, j])
            sorted_line = tuple(sorted([i, j, k]))
            if sorted_line not in seen and s == 1:
                seen.add(sorted_line)
                lines.append((i, j, k))

    return lines


def fano_cross_product_7d(u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """Compute the 7-dimensional cross-product u x_7 v.

    Defined on R^7 = Im(O) by:
        (u x_7 v)_k = sum_{i, j} c_{ijk} u_i v_j
    satisfying:
        1. Anticommutativity: u x_7 v = - (v x_7 u)
        2. Orthogonality: <u x_7 v, u> = 0 and <u x_7 v, v> = 0
        3. Norm identity: ||u x_7 v||^2 = ||u||^2 ||v||^2 - <u, v>^2

    Args:
        u: 7-dimensional vector.
        v: 7-dimensional vector.

    Returns:
        7-dimensional cross-product vector.
    """
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    if u.shape != (7,) or v.shape != (7,):
        raise NonAssociativeHydroError(
            f"Vectors must have dimension 7, got shapes {u.shape} and {v.shape}"
        )

    c = fano_structure_constants()
    # Contract c_{ijk} with u_i and v_j:
    # res_k = sum_{i, j} u_i * v_j * c[i, j, k]
    return np.asarray(np.einsum("ijk,i,j->k", c, u, v), dtype=np.float64)


def octonionic_product(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Multiply two 8-dimensional octonions a, b in O = R + Im(O).

    Args:
        a: 8-vector [a_0, a_1, ..., a_7] where a_0 is real.
        b: 8-vector [b_0, b_1, ..., b_7].

    Returns:
        8-vector product a * b.
    """
    a = np.asarray(a, dtype=np.float64)
    b = np.asarray(b, dtype=np.float64)
    if a.shape != (8,) or b.shape != (8,):
        raise NonAssociativeHydroError("Octonions must have dimension 8")

    sign, idx = build_cd_multiplication_table(8)
    res = np.zeros(8, dtype=np.float64)
    for i in range(8):
        if a[i] == 0.0:
            continue
        for j in range(8):
            if b[j] == 0.0:
                continue
            k = idx[i, j]
            s = sign[i, j]
            res[k] += a[i] * b[j] * s
    return res


def octonionic_associator(u: np.ndarray, v: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Compute the octonionic associator [u, v, w] = (u * v) * w - u * (v * w).

    For pure imaginary octonions u, v, w in R^7, the associator is pure imaginary,
    returned as a 7-vector.
    """
    u = np.asarray(u, dtype=np.float64)
    v = np.asarray(v, dtype=np.float64)
    w = np.asarray(w, dtype=np.float64)
    if u.shape != (7,) or v.shape != (7,) or w.shape != (7,):
        raise NonAssociativeHydroError("Inputs to associator must be 7-dimensional vectors")

    u8 = np.zeros(8, dtype=np.float64)
    v8 = np.zeros(8, dtype=np.float64)
    w8 = np.zeros(8, dtype=np.float64)
    u8[1:] = u
    v8[1:] = v
    w8[1:] = w

    uv = octonionic_product(u8, v8)
    uv_w = octonionic_product(uv, w8)

    vw = octonionic_product(v8, w8)
    u_vw = octonionic_product(u8, vw)

    assoc8 = uv_w - u_vw
    return np.asarray(assoc8[1:], dtype=np.float64)


def jacobi_defect_7d(u: np.ndarray, v: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Compute the Jacobi identity defect tensor in 7 dimensions.

    J(u, v, w) = u x_7 (v x_7 w) + v x_7 (w x_7 u) + w x_7 (u x_7 v).

    In Lie algebras (e.g. 3D curl), J = 0.
    In 7D non-associative hydrodynamics, J(u, v, w) is non-zero and satisfies
    the exact theorem:
        J(u, v, w) = -3/2 * [u, v, w]
    where [u, v, w] is the octonionic associator (u*v)*w - u*(v*w).
    """
    term1 = fano_cross_product_7d(u, fano_cross_product_7d(v, w))
    term2 = fano_cross_product_7d(v, fano_cross_product_7d(w, u))
    term3 = fano_cross_product_7d(w, fano_cross_product_7d(u, v))
    return np.asarray(term1 + term2 + term3, dtype=np.float64)


def sedenion_product(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Multiply two 16-dimensional sedenions a, b in S."""
    a = np.asarray(a, dtype=np.float64)
    b = np.asarray(b, dtype=np.float64)
    if a.shape != (16,) or b.shape != (16,):
        raise NonAssociativeHydroError("Sedenions must have dimension 16")

    sign, idx = build_cd_multiplication_table(16)
    res = np.zeros(16, dtype=np.float64)
    for i in range(16):
        if a[i] == 0.0:
            continue
        for j in range(16):
            if b[j] == 0.0:
                continue
            k = idx[i, j]
            s = sign[i, j]
            res[k] += a[i] * b[j] * s
    return res


def sedenion_cross_product_16d(u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """Compute the 16-dimensional sedenion commutator cross-product:

        u x_{16} v = (1/2) * (u * v - v * u)

    Anticommutative on all sedenions and vanishes identically whenever
    u and v commute or mutually annihilate.
    """
    uv = sedenion_product(u, v)
    vu = sedenion_product(v, u)
    return np.asarray(0.5 * (uv - vu), dtype=np.float64)


def lamb_vector_7d(u: np.ndarray, omega: np.ndarray) -> np.ndarray:
    """Compute the 7D Lamb vector L_7 = omega x_7 u."""
    return fano_cross_product_7d(omega, u)


def lamb_vector_16d(u: np.ndarray, omega: np.ndarray) -> np.ndarray:
    """Compute the 16D Lamb vector L_{16} = omega x_{16} u."""
    return sedenion_cross_product_16d(omega, u)


def verify_zero_divisor_lamb_annihilation() -> dict[str, Any]:
    """Exhaustively verify that L = omega x_{16} u = 0 for ALL 672 zero-divisor pairs.

    For every edge (u, v) in the 168-vertex sedenion zero-divisor annihilation graph
    (which has 672 undirected edges, representing 1344 directed annihilating pairs):
        u * v = 0 implies u x_{16} v = (1/2) * (u*v - v*u) = 0.

    Returns:
        Dictionary reporting total edges tested, verification status, and maximum residual norm.
    """
    ag = get_cached_annihilation_graph()
    edges = list(ag.nx_graph.edges())

    max_cross_norm = 0.0
    max_prod_norm = 0.0
    pairs_tested = 0

    for u_id, v_id in edges:
        u_zd = ag.id_to_zd[u_id]
        v_zd = ag.id_to_zd[v_id]

        u_vec = np.array(u_zd.sedenion.coords, dtype=np.float64)
        v_vec = np.array(v_zd.sedenion.coords, dtype=np.float64)

        # Test both directions (u, v) and (v, u)
        for a, b in [(u_vec, v_vec), (v_vec, u_vec)]:
            pairs_tested += 1
            prod = sedenion_product(a, b)
            cross = sedenion_cross_product_16d(a, b)

            prod_norm = float(np.linalg.norm(prod))
            cross_norm = float(np.linalg.norm(cross))

            if prod_norm > max_prod_norm:
                max_prod_norm = prod_norm
            if cross_norm > max_cross_norm:
                max_cross_norm = cross_norm

    return {
        "all_vanished": (max_cross_norm < 1e-12) and (max_prod_norm < 1e-12),
        "num_edges": len(edges),
        "directed_pairs_tested": pairs_tested,
        "max_cross_product_norm": max_cross_norm,
        "max_sedenion_product_norm": max_prod_norm,
    }


class NonAssociativeFluid:
    """Non-associative hydrodynamic engine in 7 and 16 dimensions."""

    def __init__(self, dimension: int = 7) -> None:
        """Initialize fluid with spatial dimension 7 or 16."""
        if dimension not in (7, 16):
            raise NonAssociativeHydroError(f"Dimension must be 7 or 16, got {dimension}")
        self.dimension = dimension

    def cross_product(self, u: np.ndarray, v: np.ndarray) -> np.ndarray:
        """Evaluate the dimension-appropriate cross-product."""
        if self.dimension == 7:
            return fano_cross_product_7d(u, v)
        return sedenion_cross_product_16d(u, v)

    def lamb_vector(self, u: np.ndarray, omega: np.ndarray) -> np.ndarray:
        """Evaluate the dimension-appropriate Lamb vector L = omega x u."""
        return self.cross_product(omega, u)

    def convective_acceleration_decomposition(
        self, u: np.ndarray, omega: np.ndarray, grad_kinetic: np.ndarray
    ) -> np.ndarray:
        """Compute (u . grad)u = (1/2) grad(|u|^2) + omega x u."""
        lamb = self.lamb_vector(u, omega)
        return np.asarray(grad_kinetic + lamb, dtype=np.float64)
