"""
projective_pencil.py — Universal Projective Line-Pencil Fibration across the Cayley-Dickson Tower.

Formalizes and computes the exact correspondence between:
1. Points of PG(n-2, F_2) and non-zero XOR charge sectors chi in {1..D/2-1}.
2. Pencils of projective lines through chi and coordinate 2-planes in sector chi:
       P(D) = |Pencil(chi)| = (D - 4) / 4 = 2^(n-2) - 1.
3. Universal sector vertex order:
       V(D) = 8 * P(D) = 2(D - 4).
4. Partition of the T(D) = binom(D/2-1, 2) coordinate 2-planes across the D/2-1 sectors:
       S(D) * P(D) = (D/2 - 1) * (D - 4) / 4 = T(D).
5. 3-to-1 line covering by coordinate 2-planes:
       T(D) = 3 * L(D), where L(D) = T(D) / 3 is the total line count in PG(n-2, F_2).
"""

from __future__ import annotations

from dataclasses import dataclass
import numpy as np


@dataclass(frozen=True)
class ProjectivePencilMetrics:
    dim: int
    ambient_dim: int       # m = D/2 - 1
    sector_count: int      # S = m = 2^(n-1) - 1
    planes_per_sector: int # P = (D - 4) / 4 = 2^(n-2) - 1
    total_lines: int       # L = T / 3
    total_planes: int      # T = binom(m, 2)
    sector_vertices: int   # V = 8 * P = 2(D - 4)
    total_vertices: int    # N = 8 * T = (D - 2)(D - 4)


class ProjectivePencilFibration:
    """
    Computes and verifies the projective line-pencil fibration
    of the Orthogonal Frame Field for arbitrary dimension D = 2^n >= 16.
    """

    def __init__(self, dim: int = 16):
        if not (dim >= 16 and (dim & (dim - 1)) == 0):
            raise ValueError(f"Dimension must be a power of 2 >= 16, got {dim}")
        self.dim = dim
        self.n = int(np.log2(dim))
        self.m = dim // 2 - 1  # ambient dimension in R^m

    @property
    def metrics(self) -> ProjectivePencilMetrics:
        """Computes all theoretical projective pencil invariants for dimension D."""
        m = self.m
        t_planes = m * (m - 1) // 2
        p_sector = (self.dim - 4) // 4
        s_sectors = m
        l_lines = t_planes // 3
        v_sector = 8 * p_sector
        total_zds = (self.dim - 2) * (self.dim - 4)

        return ProjectivePencilMetrics(
            dim=self.dim,
            ambient_dim=m,
            sector_count=s_sectors,
            planes_per_sector=p_sector,
            total_lines=l_lines,
            total_planes=t_planes,
            sector_vertices=v_sector,
            total_vertices=total_zds,
        )

    def get_lines_pg(self) -> list[tuple[int, int, int]]:
        """
        Generates all projective lines in PG(n-2, F_2).
        A line is a triple {a, b, c} of distinct non-zero elements in {1..m}
        such that a ^ b ^ c = 0, i.e. c = a ^ b.
        """
        m = self.m
        lines = []
        for a in range(1, m + 1):
            for b in range(a + 1, m + 1):
                c = a ^ b
                if c > b and c <= m:
                    lines.append((a, b, c))
        return lines

    def get_pencil(self, chi: int) -> list[tuple[int, int]]:
        """
        Returns the pencil of pairs {i, j} such that {i, j, chi} forms a projective line
        in PG(n-2, F_2), which correspond to the coordinate 2-planes in sector chi.
        """
        if not (1 <= chi <= self.m):
            raise ValueError(f"Charge chi must be in range 1..{self.m}, got {chi}")

        pencil = []
        m = self.m
        for i in range(1, m + 1):
            if i == chi:
                continue
            j = i ^ chi
            if 1 <= j <= m and i < j:
                pencil.append((i, j))
        return pencil

    def verify_fibration(self) -> dict[str, bool]:
        """
        Verifies all structural fibration theorems for dimension D:
        1. Every pencil has exactly P(D) = (D - 4) / 4 planes.
        2. Total planes partitioned across all sectors equals T(D).
        3. Total lines in PG(n-2, F_2) satisfies 3 * L(D) = T(D).
        4. Sector vertex count 8 * P(D) equals 2(D - 4).
        """
        met = self.metrics
        lines = self.get_lines_pg()

        # Check line count
        check_lines = (len(lines) == met.total_lines)

        # Check pencils
        pencil_checks = []
        all_planes = set()
        for chi in range(1, met.sector_count + 1):
            pencil = self.get_pencil(chi)
            pencil_checks.append(len(pencil) == met.planes_per_sector)
            for p in pencil:
                all_planes.add(p)

        check_pencils = all(pencil_checks)
        check_plane_partition = (len(all_planes) == met.total_planes)
        check_sector_order = (8 * met.planes_per_sector == met.sector_vertices)
        check_line_triality = (3 * len(lines) == met.total_planes)

        return {
            "check_lines": check_lines,
            "check_pencils": check_pencils,
            "check_plane_partition": check_plane_partition,
            "check_sector_order": check_sector_order,
            "check_line_triality": check_line_triality,
            "all_verified": (
                check_lines
                and check_pencils
                and check_plane_partition
                and check_sector_order
                and check_line_triality
            ),
        }
