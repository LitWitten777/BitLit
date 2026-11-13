"""
Group Action and Orbit-Stabilizer Analysis.

Analyzes the action of PSL(2,7) and extended symmetry groups on the
168 sedenion cross-octet zero divisors.
"""

from .fano import PSL2_7
from .stratification import CrossOctetVector, stratify_cross_octet


class OrbitDecomposition:
    """Computes orbits and stabilizers of zero divisors under group actions."""

    def __init__(
        self, zero_divisors: list[CrossOctetVector] | None = None, psl: PSL2_7 | None = None
    ):
        if zero_divisors is None:
            zd, _, _ = stratify_cross_octet()
            self.zero_divisors = zd
        else:
            self.zero_divisors = zero_divisors

        self.psl = psl or PSL2_7()

    def act_psl_on_vector(self, g: tuple[int, ...], v: CrossOctetVector) -> CrossOctetVector:
        """
        Action of g ∈ PSL(2,7) by permuting imaginary basis indices {1..7} (mapped from 0..6).
        Basis element e_0 is left fixed as the identity.
        For index > 0, i' = g[i-1] + 1.
        """

        def map_idx(idx: int) -> int:
            if idx == 0:
                return 0
            return g[idx - 1] + 1

        new_i = map_idx(v.i)
        new_j = map_idx(v.j)
        # Signs s1 and s2 are preserved under pure index permutations
        # Find corresponding vector from zero_divisors set
        key = (new_i, new_j, v.s1, v.s2)
        for zd in self.zero_divisors:
            if zd.key == key:
                return zd
        raise ValueError(f"Vector {key} not found in zero divisor set!")

    def compute_psl_orbits(self) -> list[list[CrossOctetVector]]:
        """
        Computes the orbit decomposition of the 168 zero divisors under PSL(2,7).
        """
        visited: set[CrossOctetVector] = set()
        orbits: list[list[CrossOctetVector]] = []

        for v in self.zero_divisors:
            if v in visited:
                continue
            current_orbit: set[CrossOctetVector] = set()
            for g in self.psl.elements:
                gv = self.act_psl_on_vector(g, v)
                current_orbit.add(gv)
            visited.update(current_orbit)
            orbits.append(list(current_orbit))

        return orbits

    def compute_stabilizer(self, v: CrossOctetVector) -> list[tuple[int, ...]]:
        """Computes the stabilizer subgroup Stab(v) = {g ∈ PSL(2,7) | g · v = v}."""
        stab = []
        for g in self.psl.elements:
            if self.act_psl_on_vector(g, v) == v:
                stab.append(g)
        return stab
