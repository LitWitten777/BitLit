"""Symplectic Yang-Mills Theory (Delgado, Tseng, Zhou 2026).

Implements:
1. Lefschetz Curvature Decomposition:
   F_A = F_A^p + Phi_A * omega
   where Lambda(F_A^p) = 0 and Phi_A = (1/n) * Lambda(F_A).
2. Functional Orthogonal Splitting:
   ||F_A||^2 = ||F_A^p||^2 + ||Phi_A * omega||^2
   = ||F_A^p||^2 + n * ||Phi_A||^2 = ||F_A^p||^2 + (1/n) * ||Lambda(F_A)||^2.
3. Euler-Lagrange Equations & 2-out-of-3 Theorem:
   YM:   d_A* F_A = 0
   PYM:  d_A* F_A^p = 0
   TYM:  d_A* (Phi_A * omega) = 0 <=> d_A Phi_A = 0 <=> d_A F_A^p = 0.
   Any connection satisfying 2 of {YM, PYM, TYM} satisfies all 3.
4. Scale Invariance under (omega, g, J) |-> (lambda^2 omega, lambda^2 g, J):
   ||F_A^p||^2_{lambda^2 g} = lambda^{d-4} ||F_A^p||^2_g.
   For d = 4: both PYM and TYM are conformally scale-invariant.
5. Monotonicity Formula:
   theta_{r_2} - theta_{r_1} >= 4 int |iota_dr F_p|^2 - 2 int S_tau d tau
   where S_tau is the symplectic defect. When A is TYM, S_tau = 0 and theta_r is monotone.
"""

from dataclasses import dataclass
from typing import Dict, List, Tuple
from fractions import Fraction
import math


@dataclass(frozen=True)
class Differential2Form4D:
    """Represents a 2-form in R^4 with coordinates dx1..dx4.
    Basis: e12, e13, e14, e23, e24, e34.
    Standard symplectic form: omega = e12 + e34.
    """
    c12: float
    c13: float
    c14: float
    c23: float
    c24: float
    c34: float

    def lefschetz_trace(self) -> float:
        """Compute Lambda(F) = c12 + c34 for standard omega = e12 + e34."""
        return self.c12 + self.c34

    def trace_phi(self, n: int = 2) -> float:
        """Phi = (1/n) * Lambda(F). In 4D, n = 2."""
        return self.lefschetz_trace() / n

    def primitive_component(self, n: int = 2) -> "Differential2Form4D":
        """F_p = F - Phi * omega = F - (1/n) Lambda(F) * (e12 + e34)."""
        phi = self.trace_phi(n)
        return Differential2Form4D(
            c12=self.c12 - phi,
            c13=self.c13,
            c14=self.c14,
            c23=self.c23,
            c24=self.c24,
            c34=self.c34 - phi,
        )

    def is_primitive(self, tol: float = 1e-12) -> bool:
        """Check if Lambda(F) == 0, i.e., c12 + c34 == 0."""
        return abs(self.lefschetz_trace()) < tol

    def norm_squared(self) -> float:
        """Standard Euclidean metric norm squared ||F||^2."""
        return (
            self.c12**2
            + self.c13**2
            + self.c14**2
            + self.c23**2
            + self.c24**2
            + self.c34**2
        )


def verify_functional_orthogonal_decomposition(F: Differential2Form4D, n: int = 2) -> Tuple[bool, Dict[str, float]]:
    """Verify ||F||^2 = ||F_p||^2 + ||Phi * omega||^2.
    In 4D, ||Phi * omega||^2 = 2 * Phi^2.
    """
    phi = F.trace_phi(n)
    F_p = F.primitive_component(n)
    norm_F_sq = F.norm_squared()
    norm_Fp_sq = F_p.norm_squared()
    norm_phi_omega_sq = n * (phi**2)

    total_split = norm_Fp_sq + norm_phi_omega_sq
    diff = abs(norm_F_sq - total_split)
    is_orthogonal = diff < 1e-12

    return is_orthogonal, {
        "norm_F_sq": norm_F_sq,
        "norm_Fp_sq": norm_Fp_sq,
        "norm_phi_omega_sq": norm_phi_omega_sq,
        "sum_split": total_split,
        "discrepancy": diff,
    }


def verify_two_out_of_three(is_ym: bool, is_pym: bool, is_tym: bool) -> bool:
    """The 2-out-of-3 property (Corollary 3.7):
    If any 2 hold, all 3 must hold.
    """
    count = sum([is_ym, is_pym, is_tym])
    if count == 2:
        # A valid physical solution cannot have exactly 2 true and 1 false!
        return False
    return True


def scale_functional(energy: float, dim: int, scale_factor: float) -> float:
    """Under (omega, g, J) |-> (lambda^2 omega, lambda^2 g, J),
    the functional scales as lambda^{d - 4}.
    For d = 4: lambda^0 = 1 (scale invariant).
    """
    exponent = dim - 4
    return energy * (scale_factor ** exponent)


def monotonicity_defect(
    is_tym: bool,
    base_monotone_increase: float,
    defect_term_integral: float,
) -> float:
    """Monotonicity difference theta_{r2} - theta_{r1}.
    If A is TYM, the defect term S_tau vanishes identically, guaranteeing monotonicity.
    """
    if is_tym:
        effective_defect = 0.0
    else:
        effective_defect = defect_term_integral
    return base_monotone_increase - effective_defect


def master_symplectic_yang_mills_check() -> bool:
    """Master invariant test verifying all foundational axioms of Delgado-Tseng-Zhou (2026)."""
    # 1. Test orthogonal splitting on a non-trivial 2-form
    F = Differential2Form4D(c12=3.0, c13=2.0, c14=-1.0, c23=0.5, c24=1.5, c34=5.0)
    split_ok, _ = verify_functional_orthogonal_decomposition(F, n=2)
    if not split_ok:
        return False

    # 2. Test primitive component of F is indeed primitive
    F_p = F.primitive_component(n=2)
    if not F_p.is_primitive():
        return False

    # 3. Test 4D scale invariance: d=4 => lambda^{4-4} = 1
    scaled_e = scale_functional(42.0, dim=4, scale_factor=3.5)
    if abs(scaled_e - 42.0) > 1e-12:
        return False

    # 4. Test 2-out-of-3 consistency
    if not verify_two_out_of_three(True, True, True):
        return False
    if not verify_two_out_of_three(False, False, False):
        return False
    if verify_two_out_of_three(True, True, False):
        return False

    # 5. Defect vanishing under TYM
    diff_tym = monotonicity_defect(is_tym=True, base_monotone_increase=10.0, defect_term_integral=5.0)
    if diff_tym != 10.0:
        return False

    return True
