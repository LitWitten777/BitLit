"""
Exact Cayley-Dickson Algebra Engine.

Provides recursive construction and vector representations for:
- Reals / Integers (dim 1)
- Complex (dim 2)
- Quaternions (dim 4)
- Octonions (dim 8)
- Sedenions (dim 16)
"""

from typing import Any, Self


def cd_add(x: Any, y: Any) -> Any:
    """Componentwise addition for CD elements or integers."""
    if isinstance(x, (int, float)):
        return x + y
    return tuple(cd_add(a, b) for a, b in zip(x, y, strict=True))


def cd_sub(x: Any, y: Any) -> Any:
    """Componentwise subtraction."""
    if isinstance(x, (int, float)):
        return x - y
    return tuple(cd_sub(a, b) for a, b in zip(x, y, strict=True))


def cd_smul(n: int, x: Any) -> Any:
    """Scalar multiplication by an integer."""
    if isinstance(x, (int, float)):
        return n * x
    return tuple(cd_smul(n, c) for c in x)


def cd_conjugate(x: Any, dim: int = 16) -> Any:
    """
    Conjugation involution at specified dimension.
    dim=1: identity
    dim=2: (a, b)* = (a, -b)
    dim=4: (a, b)* = (a*, -b)
    dim=8: (a, b)* = (a*, -b)
    dim=16: (a, b)* = (a*, -b)
    """
    if dim <= 1 or isinstance(x, (int, float)):
        return x
    a, b = x
    sub_dim = dim // 2
    return (cd_conjugate(a, sub_dim), cd_smul(-1, b))


def cd_multiply(x: Any, y: Any, dim: int = 16) -> Any:
    """
    Cayley-Dickson canonical multiplication:
    (a, b)(c, d) = (ac - d* b, da + bc*)
    where * is conjugation in the sub-algebra.
    """
    if dim <= 1 or isinstance(x, (int, float)):
        return x * y

    a, b = x
    c, d = y
    sub_dim = dim // 2

    # ac
    ac = cd_multiply(a, c, sub_dim)
    # d*
    d_star = cd_conjugate(d, sub_dim)
    # d* b
    d_star_b = cd_multiply(d_star, b, sub_dim)
    # re = ac - d*b
    re = cd_sub(ac, d_star_b)

    # da
    da = cd_multiply(d, a, sub_dim)
    # c*
    c_star = cd_conjugate(c, sub_dim)
    # b c*
    b_c_star = cd_multiply(b, c_star, sub_dim)
    # im = da + b c*
    im = cd_add(da, b_c_star)

    return (re, im)


def cd_is_zero(x: Any) -> bool:
    """Recursively checks if all components are zero."""
    if isinstance(x, (int, float)):
        return x == 0
    return all(cd_is_zero(c) for c in x)


def flatten_cd(x: Any) -> tuple[int, ...]:
    """Flattens a nested CD tree to a 1D tuple of integers."""
    if isinstance(x, (int, float)):
        return (int(x),)
    res: list[int] = []
    for item in x:
        res.extend(flatten_cd(item))
    return tuple(res)


def unflatten_cd(coords: tuple[int, ...], dim: int = 16) -> Any:
    """Reconstructs nested CD tree from a 1D coordinate tuple."""
    if dim == 1:
        return coords[0]
    half = dim // 2
    left = unflatten_cd(coords[:half], half)
    right = unflatten_cd(coords[half:], half)
    return (left, right)


def get_basis_element(i: int, dim: int = 16) -> Any:
    """Constructs the standard basis element e_i for given dimension."""
    coords = tuple(1 if idx == i else 0 for idx in range(dim))
    return unflatten_cd(coords, dim)


class CDElement:
    """Wrapper class providing vector operations for Cayley-Dickson elements."""

    dim: int = 16

    def __init__(self, data: Any):
        if hasattr(data, "tolist"):
            data = data.tolist()
        if (
            isinstance(data, (list, tuple))
            and len(data) == self.dim
            and all(isinstance(x, (int, float)) for x in data)
        ):
            self.tree = unflatten_cd(tuple(data), self.dim)
            self.coords = tuple(int(x) for x in data)
        else:
            self.tree = data
            self.coords = flatten_cd(data)
            if len(self.coords) != self.dim:
                raise ValueError(f"Expected dimension {self.dim}, got {len(self.coords)}")

    def __add__(self, other: "CDElement") -> "CDElement":
        return self.__class__(cd_add(self.tree, other.tree))

    def __sub__(self, other: "CDElement") -> "CDElement":
        return self.__class__(cd_sub(self.tree, other.tree))

    def __mul__(self, other: "CDElement") -> "CDElement":
        return self.__class__(cd_multiply(self.tree, other.tree, self.dim))

    def __rmul__(self, scalar: int) -> "CDElement":
        return self.__class__(cd_smul(scalar, self.tree))

    def __neg__(self) -> "CDElement":
        return self.__class__(cd_smul(-1, self.tree))

    def conjugate(self) -> "CDElement":
        return self.__class__(cd_conjugate(self.tree, self.dim))

    def is_zero(self) -> bool:
        return cd_is_zero(self.tree)

    def norm_sq(self) -> int:
        return sum(c * c for c in self.coords)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CDElement):
            return False
        return self.coords == other.coords

    def __hash__(self) -> int:
        return hash(self.coords)

    def __repr__(self) -> str:
        active = [
            f"{c if c != 1 else ''}e_{i}" if c != -1 else f"-e_{i}"
            for i, c in enumerate(self.coords)
            if c != 0
        ]
        return " + ".join(active) if active else "0"

    @classmethod
    def zero(cls) -> Self:
        """Returns the zero element of this algebra."""
        return cls(tuple(0 for _ in range(cls.dim)))

    @classmethod
    def basis(cls, i: int) -> Self:
        """Returns standard basis vector e_i."""
        return cls(get_basis_element(i, cls.dim))


class Quaternion(CDElement):
    dim = 4


class Octonion(CDElement):
    dim = 8


class Sedenion(CDElement):
    dim = 16
