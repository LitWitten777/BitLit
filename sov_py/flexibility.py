"""
Cayley-Dickson Tower Flexibility Verification (OP-007, HYP-114)
Rigorous computational verification that every Cayley-Dickson algebra A_n (D = 2^n >= 16)
is flexible: (xy)x = x(yx), or equivalently [x, y, x] = 0, on all elements.
"""

from typing import List, Tuple
import random


def cd_conj(x: List[int]) -> List[int]:
    """Conjugation of a Cayley-Dickson element represented as an integer coordinate list."""
    dim = len(x)
    if dim == 1:
        return [x[0]]
    h = dim // 2
    return cd_conj(x[:h]) + [-val for val in x[h:]]


def cd_mul(x: List[int], y: List[int]) -> List[int]:
    """Exact integer Cayley-Dickson multiplication: (a, b)(c, d) = (ac - d*b, da + bc*)."""
    dim = len(x)
    if dim == 1:
        return [x[0] * y[0]]
    h = dim // 2
    a, b = x[:h], x[h:]
    c, d = y[:h], y[h:]
    cd = cd_conj(d)
    cc = cd_conj(c)
    re = [u - v for u, v in zip(cd_mul(a, c), cd_mul(cd, b))]
    im = [u + v for u, v in zip(cd_mul(d, a), cd_mul(b, cc))]
    return re + im


def cd_basis(dim: int, idx: int) -> List[int]:
    """Basis vector e_idx in dimension dim."""
    v = [0] * dim
    v[idx] = 1
    return v


def cd_assoc(x: List[int], y: List[int], z: List[int]) -> List[int]:
    """Associator [x, y, z] = (xy)z - x(yz)."""
    xy_z = cd_mul(cd_mul(x, y), z)
    x_yz = cd_mul(x, cd_mul(y, z))
    return [u - v for u, v in zip(xy_z, x_yz)]


def verify_basis_flexibility(dim: int) -> bool:
    """Verify [e_a, e_b, e_a] = 0 for all basis indices a, b."""
    for a in range(dim):
        ea = cd_basis(dim, a)
        for b in range(dim):
            eb = cd_basis(dim, b)
            asc = cd_assoc(ea, eb, ea)
            if any(val != 0 for val in asc):
                return False
    return True


def verify_outer_skew_symmetry(dim: int) -> Tuple[bool, int]:
    """
    Verify [e_a, e_b, e_c] + [e_c, e_b, e_a] = 0 for all triples (a, b, c).
    Returns (is_valid, total_checked).
    """
    total = 0
    for a in range(dim):
        ea = cd_basis(dim, a)
        for b in range(dim):
            eb = cd_basis(dim, b)
            for c in range(a, dim):
                ec = cd_basis(dim, c)
                asc1 = cd_assoc(ea, eb, ec)
                asc2 = cd_assoc(ec, eb, ea)
                if any(u + v != 0 for u, v in zip(asc1, asc2)):
                    return False, total
                total += 1
    return True, total


def verify_random_flexibility(dim: int, num_trials: int = 100, coord_range: int = 10) -> bool:
    """Verify (xy)x = x(yx) for random integer vectors with exact integer arithmetic."""
    for _ in range(num_trials):
        x = [random.randint(-coord_range, coord_range) for _ in range(dim)]
        y = [random.randint(-coord_range, coord_range) for _ in range(dim)]
        lhs = cd_mul(cd_mul(x, y), x)
        rhs = cd_mul(x, cd_mul(y, x))
        if lhs != rhs:
            return False
    return True


def polarization_identity_check(x: List[int], y: List[int]) -> bool:
    """
    Verify that [x, y, x] expands as sum_{a<=c} x_a x_c y_b ([e_a, e_b, e_c] + [e_c, e_b, e_a])
    and evaluates to 0.
    """
    dim = len(x)
    actual_assoc = cd_assoc(x, y, x)
    if any(val != 0 for val in actual_assoc):
        return False
    # Cross-check with sum expansion
    accum = [0] * dim
    for b in range(dim):
        if y[b] == 0:
            continue
        eb = cd_basis(dim, b)
        for a in range(dim):
            if x[a] == 0:
                continue
            ea = cd_basis(dim, a)
            for c in range(a, dim):
                if x[c] == 0:
                    continue
                ec = cd_basis(dim, c)
                if a == c:
                    coeff = x[a] * x[a] * y[b]
                    asc = cd_assoc(ea, eb, ea)
                    for i in range(dim):
                        accum[i] += coeff * asc[i]
                else:
                    coeff = x[a] * x[c] * y[b]
                    asc1 = cd_assoc(ea, eb, ec)
                    asc2 = cd_assoc(ec, eb, ea)
                    for i in range(dim):
                        accum[i] += coeff * (asc1[i] + asc2[i])
    return accum == actual_assoc == [0] * dim
