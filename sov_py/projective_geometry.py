"""
Projective Geometry PG(3, F_2) and the Klein Quadric Q+(5, 2) in D=32 Cayley-Dickson Algebra.

Models the 15 non-zero XOR charge sectors of D=32 as points of PG(3, F_2),
the 35 projective lines as isotropic points on the Klein quadric Q+(5, 2) via
6-dimensional Plücker coordinates, and establishes the exact duality between
the 7 biregular sectors (HYP-023) and the disjoint alpha-plane and beta-plane generators.
"""

from __future__ import annotations

from typing import Any


class ProjectiveGeometry3D:
    """
    Projective geometry PG(3, F_2) and the Klein quadric Q+(5, 2) embedding.

    Properties:
    - 15 points (non-zero vectors in F_2^4), corresponding to XOR charges chi in {1..15}.
    - 35 lines (2-dimensional subspaces in F_2^4), each containing 3 collinear points.
    - Klein quadric Q+(5, 2) in PG(5, F_2) defined by p01*p23 ^ p02*p13 ^ p03*p12 = 0.
    - Two disjoint maximal totally isotropic 2-plane generators:
        * Alpha-plane (Pole generator): 7 lines incident to pole 8 (p01=p02=p12=0).
        * Beta-plane (Fano generator): 7 lines in Fano hyperplane (p03=p13=p23=0).
    - 21 skew lines disjoint from pole 8 and not lying in the Fano hyperplane.
    """

    POLE_POINT: int = 8  # 1000_2

    @staticmethod
    def points() -> list[int]:
        """Returns all 15 points of PG(3, F_2) as integers 1..15."""
        return list(range(1, 16))

    @staticmethod
    def to_bits(p: int) -> tuple[int, int, int, int]:
        """Returns 4-bit binary coordinates (x0, x1, x2, x3) for a point p in F_2^4."""
        if not (1 <= p <= 15):
            raise ValueError(f"Point must be in 1..15, got {p}")
        return ((p >> 0) & 1, (p >> 1) & 1, (p >> 2) & 1, (p >> 3) & 1)

    @classmethod
    def lines(cls) -> list[tuple[int, int, int]]:
        """
        Returns all 35 projective lines in PG(3, F_2).
        Each line is represented as a sorted 3-tuple (p1, p2, p3) satisfying p1 ^ p2 ^ p3 = 0.
        """
        pts = cls.points()
        all_lines: set[tuple[int, int, int]] = set()

        for i in range(len(pts)):
            for j in range(i + 1, len(pts)):
                p1 = pts[i]
                p2 = pts[j]
                p3 = p1 ^ p2
                line = tuple(sorted((p1, p2, p3)))
                all_lines.add(line)  # type: ignore[arg-type]

        sorted_lines = sorted(all_lines)
        if len(sorted_lines) != 35:
            raise RuntimeError(f"Expected 35 lines, got {len(sorted_lines)}")
        return sorted_lines

    @classmethod
    def plucker_coordinates(cls, u: int, v: int) -> tuple[int, int, int, int, int, int]:
        """
        Computes the 6-component Plücker coordinate vector (p01, p02, p03, p12, p13, p23)
        over F_2 for the line spanned by distinct points u and v.
        """
        if u == v or u == 0 or v == 0:
            raise ValueError(f"Line requires two distinct non-zero points, got u={u}, v={v}")

        u_bits = cls.to_bits(u)
        v_bits = cls.to_bits(v)

        p01 = (u_bits[0] * v_bits[1] ^ u_bits[1] * v_bits[0]) & 1
        p02 = (u_bits[0] * v_bits[2] ^ u_bits[2] * v_bits[0]) & 1
        p03 = (u_bits[0] * v_bits[3] ^ u_bits[3] * v_bits[0]) & 1
        p12 = (u_bits[1] * v_bits[2] ^ u_bits[2] * v_bits[1]) & 1
        p13 = (u_bits[1] * v_bits[3] ^ u_bits[3] * v_bits[1]) & 1
        p23 = (u_bits[2] * v_bits[3] ^ u_bits[3] * v_bits[2]) & 1

        return (p01, p02, p03, p12, p13, p23)

    @classmethod
    def line_plucker(cls, line: tuple[int, int, int]) -> tuple[int, int, int, int, int, int]:
        """
        Computes the invariant Plücker coordinate vector for a line.
        Verifies that any pair of points on the line yields the exact same Plücker vector over F_2.
        """
        p1, p2, p3 = line
        vec1 = cls.plucker_coordinates(p1, p2)
        vec2 = cls.plucker_coordinates(p1, p3)
        vec3 = cls.plucker_coordinates(p2, p3)

        if not (vec1 == vec2 == vec3):
            raise ValueError(f"Plücker coordinate invariance violated on line {line}")
        return vec1

    @staticmethod
    def klein_quadric_evaluate(p: tuple[int, int, int, int, int, int]) -> int:
        """
        Evaluates the hyperbolic Klein quadric quadratic form:
        Q(p) = p01*p23 ^ p02*p13 ^ p03*p12 (mod 2).
        For all lines in PG(3, F_2), Q(p) == 0.
        """
        p01, p02, p03, p12, p13, p23 = p
        return ((p01 * p23) ^ (p02 * p13) ^ (p03 * p12)) & 1

    @classmethod
    def line_partition(cls) -> dict[str, list[tuple[int, int, int]]]:
        """
        Partitions the 35 lines of PG(3, F_2) into three geometric classes:
        1. 'pole_lines' (7 lines): incident to pole 8, of the form (f, 8, f ^ 8).
        2. 'fano_lines' (7 lines): contained in the Fano hyperplane x3 = 0 (all points < 8).
        3. 'skew_lines' (21 lines): disjoint from pole 8 and not in the Fano hyperplane.
        """
        all_lines = cls.lines()
        pole_lines: list[tuple[int, int, int]] = []
        fano_lines: list[tuple[int, int, int]] = []
        skew_lines: list[tuple[int, int, int]] = []

        for line in all_lines:
            if cls.POLE_POINT in line:
                pole_lines.append(line)
            elif all(pt < cls.POLE_POINT for pt in line):
                fano_lines.append(line)
            else:
                skew_lines.append(line)

        return {
            "pole_lines": pole_lines,
            "fano_lines": fano_lines,
            "skew_lines": skew_lines,
        }

    @classmethod
    def generators(cls) -> dict[str, list[tuple[int, int, int, int, int, int]]]:
        """
        Returns the two disjoint maximal totally isotropic 2-plane generators on Q+(5, 2):
        1. 'alpha_plane_pole': 7 Plücker points for pole lines (p01 = p02 = p12 = 0).
        2. 'beta_plane_fano': 7 Plücker points for Fano lines (p03 = p13 = p23 = 0).
        """
        part = cls.line_partition()
        alpha_plane = [cls.line_plucker(line) for line in part["pole_lines"]]
        beta_plane = [cls.line_plucker(line) for line in part["fano_lines"]]

        return {
            "alpha_plane_pole": alpha_plane,
            "beta_plane_fano": beta_plane,
        }

    @classmethod
    def biregular_fano_correspondence(cls) -> list[dict[str, Any]]:
        """
        Constructs the exact bijection between the 7 Fano charges f in {1..7},
        the 7 biregular sectors chi = f ^ 8 in {9..15} of D=32, the 7 pole lines,
        and the alpha-plane generator on the Klein quadric.
        """
        records: list[dict[str, Any]] = []
        for f in range(1, 8):
            bireg_chi = f ^ cls.POLE_POINT
            line = tuple(sorted((f, cls.POLE_POINT, bireg_chi)))
            plk = cls.plucker_coordinates(f, cls.POLE_POINT)
            f_bits = (f & 1, (f >> 1) & 1, (f >> 2) & 1)

            # Verify Plücker coordinate structure (0, 0, f0, 0, f1, f2)
            if plk != (0, 0, f_bits[0], 0, f_bits[1], f_bits[2]):
                raise RuntimeError(f"Plücker coordinate mismatch for Fano charge {f}: {plk}")

            records.append(
                {
                    "fano_charge": f,
                    "biregular_charge": bireg_chi,
                    "line": line,
                    "plucker_vector": plk,
                    "fano_binary": f_bits,
                }
            )

        return records
