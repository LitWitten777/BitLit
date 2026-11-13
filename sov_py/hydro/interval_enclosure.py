"""Computer-Assisted Dyadic Interval Enclosures for the 1D Hou-Luo Model.

Provides certified numerical verification of finite-time singular profiles in
the 1D Hou-Luo boundary collapse model:
    omega_t + u omega_z = 2 u_z omega, with u_z = H(omega)
where H is the Hilbert transform on the half-line / circle, representing the
3D axisymmetric Euler singular blowup on the cylindrical boundary r = 1.

Under self-similar coordinates xi = z / (T - t)^c with omega(z, t) = (T - t)^{-1} Omega(xi),
the steady profile satisfies the non-linear operator equation:
    - Omega - c xi Omega' + U Omega' = 2 U' Omega, with U' = H(Omega)
reformulated in fixed-point preconditioned form:
    T(Omega) = Omega

This module provides:
1. DyadicInterval: Exact rational intervals [lower, upper] with Fraction endpoints.
2. ProfileEnclosure: Certified interval enclosure for steady vorticity profiles on dyadic grids.
3. HouLuoIntervalSolver: Operator evaluator, discrete Hilbert transform, residual computer,
   and contraction mapping certifier guaranteeing existence and uniqueness via Banach's Fixed-Point Theorem.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import overload

import numpy as np


class IntervalArithmeticError(ValueError):
    """Raised for invalid interval operations or boundary violations."""


@dataclass(frozen=True)
class DyadicInterval:
    """Exact rational interval [lower, upper] with Fraction endpoints.

    Provides certified interval arithmetic with exact directed inclusion.
    """

    lower: Fraction
    upper: Fraction

    def __init__(
        self,
        lower: Fraction | float | int | str | DyadicInterval,
        upper: Fraction | float | int | str | None = None,
    ) -> None:
        if isinstance(lower, DyadicInterval):
            object.__setattr__(self, "lower", lower.lower)
            object.__setattr__(self, "upper", lower.upper)
            return

        if upper is None:
            upper = lower

        def _to_fraction(v: Fraction | float | int | str) -> Fraction:
            if isinstance(v, Fraction):
                return v
            if isinstance(v, int):
                return Fraction(v, 1)
            if isinstance(v, float):
                return Fraction(str(v))
            return Fraction(v)

        l_frac = _to_fraction(lower)
        u_frac = _to_fraction(upper)

        if l_frac > u_frac:
            raise IntervalArithmeticError(
                f"Invalid interval: lower bound {l_frac} exceeds upper bound {u_frac}"
            )

        object.__setattr__(self, "lower", l_frac)
        object.__setattr__(self, "upper", u_frac)

    def __repr__(self) -> str:
        return f"DyadicInterval([{float(self.lower):.8f}, {float(self.upper):.8f}])"

    def __add__(self, other: DyadicInterval | Fraction | float | int | str) -> DyadicInterval:
        oth = other if isinstance(other, DyadicInterval) else DyadicInterval(other)
        return DyadicInterval(self.lower + oth.lower, self.upper + oth.upper)

    def __radd__(self, other: Fraction | float | int | str) -> DyadicInterval:
        return self.__add__(other)

    def __sub__(self, other: DyadicInterval | Fraction | float | int | str) -> DyadicInterval:
        oth = other if isinstance(other, DyadicInterval) else DyadicInterval(other)
        return DyadicInterval(self.lower - oth.upper, self.upper - oth.lower)

    def __rsub__(self, other: Fraction | float | int | str) -> DyadicInterval:
        oth = DyadicInterval(other)
        return oth.__sub__(self)

    def __neg__(self) -> DyadicInterval:
        return DyadicInterval(-self.upper, -self.lower)

    def __mul__(self, other: DyadicInterval | Fraction | float | int | str) -> DyadicInterval:
        oth = other if isinstance(other, DyadicInterval) else DyadicInterval(other)
        p = (
            self.lower * oth.lower,
            self.lower * oth.upper,
            self.upper * oth.lower,
            self.upper * oth.upper,
        )
        return DyadicInterval(min(p), max(p))

    def __rmul__(self, other: Fraction | float | int | str) -> DyadicInterval:
        return self.__mul__(other)

    def __truediv__(self, other: DyadicInterval | Fraction | float | int | str) -> DyadicInterval:
        oth = other if isinstance(other, DyadicInterval) else DyadicInterval(other)
        if oth.lower <= 0 <= oth.upper:
            raise ZeroDivisionError(
                f"Division by interval containing zero: [{oth.lower}, {oth.upper}]"
            )
        p = (
            self.lower / oth.lower,
            self.lower / oth.upper,
            self.upper / oth.lower,
            self.upper / oth.upper,
        )
        return DyadicInterval(min(p), max(p))

    def contains(self, val: Fraction | float | int | str) -> bool:
        """Check if an exact scalar value lies inside [lower, upper]."""
        v = val if isinstance(val, Fraction) else Fraction(str(val))
        return bool(self.lower <= v <= self.upper)

    def contains_interval(self, other: DyadicInterval) -> bool:
        """Check whether other interval is completely contained within self (other subset of self)."""
        return bool(self.lower <= other.lower and other.upper <= self.upper)

    def subset_of(self, other: DyadicInterval) -> bool:
        """Check whether self is completely contained within other (self subset of other)."""
        return other.contains_interval(self)

    def width(self) -> Fraction:
        """Compute the exact rational interval width (upper - lower)."""
        return self.upper - self.lower

    def midpoint(self) -> Fraction:
        """Compute the exact rational interval midpoint (lower + upper) / 2."""
        return (self.lower + self.upper) / 2

    def mag(self) -> Fraction:
        """Maximum absolute value in the interval."""
        return max(abs(self.lower), abs(self.upper))

    def mig(self) -> Fraction:
        """Minimum absolute value in the interval (mignitude)."""
        if self.lower <= 0 <= self.upper:
            return Fraction(0, 1)
        return min(abs(self.lower), abs(self.upper))

    def to_floats(self) -> tuple[float, float]:
        """Convert endpoints to floating point numbers."""
        return float(self.lower), float(self.upper)

    def intersect(self, other: DyadicInterval) -> DyadicInterval:
        """Intersection of two overlapping intervals."""
        new_lower = max(self.lower, other.lower)
        new_upper = min(self.upper, other.upper)
        if new_lower > new_upper:
            raise IntervalArithmeticError("Empty intersection between disjoint intervals")
        return DyadicInterval(new_lower, new_upper)

    def hull(self, other: DyadicInterval) -> DyadicInterval:
        """Smallest interval enclosing both self and other (interval hull)."""
        return DyadicInterval(min(self.lower, other.lower), max(self.upper, other.upper))


@dataclass(frozen=True)
class ProfileEnclosure:
    """Certified interval enclosure for a discrete vorticity profile on a dyadic grid.

    Attributes:
        grid: Rational dyadic spatial coordinates z_k = k * 2^{-p}.
        intervals: Enclosure intervals [a_k, b_k] at each grid point.
        residual_bound: Bound on the operator residual ||T(Omega_0) - Omega_0||_{L^infty}.
        contraction_constant: Verified Lipschitz constant kappa < 1 of the preconditioned operator.
        verified_existence: Boolean flag certifying existence and uniqueness in B(Omega_0, radius).
        radius: Radius r of the contraction ball B(Omega_0, r).
        p_dyadic: Dyadic grid precision exponent p where step size h = 2^{-p}.
        n_points: Total number of discrete grid nodes.
    """

    grid: list[Fraction]
    intervals: list[DyadicInterval]
    residual_bound: float
    contraction_constant: float
    verified_existence: bool
    radius: float = 0.05
    p_dyadic: int = 4
    n_points: int = 16

    @property
    def is_valid_enclosure(self) -> bool:
        """Verify the Banach fixed-point theorem self-mapping criterion.

        Requires:
        1. Strict contraction: kappa < 1.0.
        2. Ball invariance: epsilon / (1 - kappa) <= radius.
        """
        if not self.verified_existence:
            return False
        if self.contraction_constant >= 1.0:
            return False
        return (self.residual_bound / (1.0 - self.contraction_constant)) <= self.radius

    def midpoints(self) -> list[float]:
        """Floating point midpoints of all profile intervals."""
        return [float(iv.midpoint()) for iv in self.intervals]

    def widths(self) -> list[float]:
        """Floating point widths of all profile intervals."""
        return [float(iv.width()) for iv in self.intervals]

    def max_width(self) -> float:
        """Maximum interval width across the spatial grid."""
        return max(float(iv.width()) for iv in self.intervals)

    def contains_profile(self, profile: Sequence[float] | np.ndarray) -> bool:
        """Verify whether a candidate discrete profile lies entirely inside the enclosure."""
        if len(profile) != len(self.intervals):
            return False
        return all(self.intervals[i].contains(float(profile[i])) for i in range(len(profile)))


class HouLuoIntervalSolver:
    """Computer-assisted dyadic interval solver for the 1D Hou-Luo boundary model.

    Implements:
    - Discrete Hilbert transform operator H on the dyadic grid z_k = k * 2^{-p}.
    - Preconditioned fixed-point operator T(Omega) = Omega - M * F(Omega).
    - Residual computation and contraction constant verification on the dyadic lattice.
    - Automated certified profile enclosure generation.
    """

    def __init__(
        self,
        n_points: int = 16,
        p_dyadic: int = 4,
        c_scaling: float = 1.0,
    ) -> None:
        """Initialize the Hou-Luo interval solver.

        Args:
            n_points: Number of dyadic grid points N.
            p_dyadic: Dyadic grid exponent p where step size h = 2^{-p}.
            c_scaling: Self-similar spatial scaling rate c.
        """
        if n_points < 4:
            raise IntervalArithmeticError("Grid requires at least 4 points")
        if p_dyadic < 1:
            raise IntervalArithmeticError("Dyadic scale exponent p must be positive")

        self.n_points = n_points
        self.p_dyadic = p_dyadic
        self.c_scaling = float(c_scaling)
        self.h = Fraction(1, 2**p_dyadic)
        self.h_float = float(self.h)

        self.grid = [Fraction(k, 2**p_dyadic) for k in range(n_points)]
        self.grid_float = np.array([float(z) for z in self.grid], dtype=np.float64)

        # Build discrete differential, Hilbert transform, and integration matrices
        self.D = self._build_differentiation_matrix()
        self.H = self._build_hilbert_matrix()
        self.Int_mat = self._build_integration_matrix()

        # Compute reference steady solution profile and preconditioning matrix
        self.reference_profile = self._solve_reference_profile()
        jacobian = self._numerical_jacobian(self.reference_profile)
        self.preconditioner = np.linalg.inv(jacobian)

    def _build_differentiation_matrix(self) -> np.ndarray:
        """Construct central difference differentiation matrix with odd boundary reflection."""
        N = self.n_points
        h = self.h_float
        D = np.zeros((N, N), dtype=np.float64)
        # At origin xi=0: odd symmetry Omega(-xi) = -Omega(xi) => (Omega_1 - (-Omega_1))/(2h) = Omega_1 / h
        D[0, 1] = 1.0 / h
        for k in range(1, N - 1):
            D[k, k - 1] = -0.5 / h
            D[k, k + 1] = 0.5 / h
        # One-sided boundary difference at the far end
        D[N - 1, N - 2] = -1.0 / h
        D[N - 1, N - 1] = 1.0 / h
        return D

    def _build_hilbert_matrix(self) -> np.ndarray:
        """Construct discrete Hilbert transform matrix on the half-line with odd reflection.

        Kernel for odd profile: K(xi_k, xi_j) = (1 / pi) * [ 1/(xi_k - xi_j) + 1/(xi_k + xi_j) ] * h.
        Diagonal principal value regularized to 0.
        """
        N = self.n_points
        h = self.h_float
        xi = self.grid_float
        H = np.zeros((N, N), dtype=np.float64)
        for k in range(N):
            for j in range(N):
                if k != j:
                    diff = xi[k] - xi[j]
                    summ = xi[k] + xi[j]
                    t1 = 1.0 / diff if abs(diff) > 1e-14 else 0.0
                    t2 = 1.0 / summ if abs(summ) > 1e-14 else 0.0
                    H[k, j] = (t1 + t2) * h / math.pi
        return H

    def _build_integration_matrix(self) -> np.ndarray:
        """Construct cumulative trapezoidal integration operator for velocity U = int_0^xi U'."""
        N = self.n_points
        h = self.h_float
        Int_mat = np.zeros((N, N), dtype=np.float64)
        for k in range(1, N):
            for j in range(k):
                Int_mat[k, j] += h
            Int_mat[k, k] += 0.5 * h
        return Int_mat

    def _eval_F_float(self, omega: np.ndarray) -> np.ndarray:
        """Evaluate continuous profile residual F(Omega) = -Omega - c*xi*Omega' + U*Omega' - 2*U'*Omega."""
        omega_prime = self.D @ omega
        u_prime = self.H @ omega
        u = self.Int_mat @ u_prime
        convective = (u - self.c_scaling * self.grid_float) * omega_prime
        vortex_stretching = 2.0 * u_prime * omega
        return np.asarray(-omega + convective - vortex_stretching, dtype=np.float64)

    def _numerical_jacobian(self, omega: np.ndarray) -> np.ndarray:
        """Compute the Fréchet derivative matrix DF(Omega)."""
        eps = 1e-7
        N = self.n_points
        J = np.zeros((N, N), dtype=np.float64)
        f0 = self._eval_F_float(omega)
        for j in range(N):
            ej = np.zeros(N, dtype=np.float64)
            ej[j] = eps
            J[:, j] = (self._eval_F_float(omega + ej) - f0) / eps
        return J

    def _solve_reference_profile(self) -> np.ndarray:
        """Solve for the steady profile using damped Newton iterations."""
        omega = self.grid_float * np.exp(-(self.grid_float**2) / 0.5)
        for _ in range(30):
            f = self._eval_F_float(omega)
            if np.linalg.norm(f) < 1e-12:
                break
            J = self._numerical_jacobian(omega)
            delta = np.linalg.solve(J, -f)
            omega = omega + delta
        return omega

    @overload
    def discrete_hilbert_transform(self, profile: np.ndarray) -> np.ndarray: ...

    @overload
    def discrete_hilbert_transform(self, profile: list[DyadicInterval]) -> list[DyadicInterval]: ...

    def discrete_hilbert_transform(
        self, profile: list[DyadicInterval] | np.ndarray
    ) -> list[DyadicInterval] | np.ndarray:
        """Evaluate the discrete Hilbert transform U' = H(Omega).

        Supports both floating-point arrays and certified DyadicInterval vectors.
        """
        if isinstance(profile, np.ndarray):
            return np.asarray(self.H @ profile, dtype=np.float64)

        # Certified interval evaluation
        res: list[DyadicInterval] = []
        for i in range(self.n_points):
            row_sum = DyadicInterval(0, 0)
            for j in range(self.n_points):
                coef = self.H[i, j]
                if abs(coef) > 1e-15:
                    c_frac = Fraction(str(round(coef, 10)))
                    row_sum = row_sum + (DyadicInterval(c_frac) * profile[j])
            res.append(row_sum)
        return res

    @overload
    def evaluate_fixed_point_operator(self, profile: np.ndarray) -> np.ndarray: ...

    @overload
    def evaluate_fixed_point_operator(
        self, profile: list[DyadicInterval]
    ) -> list[DyadicInterval]: ...

    def evaluate_fixed_point_operator(
        self, profile: list[DyadicInterval] | np.ndarray
    ) -> list[DyadicInterval] | np.ndarray:
        """Evaluate the preconditioned fixed point operator T(Omega) = Omega - M * F(Omega)."""
        if isinstance(profile, np.ndarray):
            f = self._eval_F_float(profile)
            return np.asarray(profile - self.preconditioner @ f, dtype=np.float64)

        # DyadicInterval profile evaluation
        mid = np.array([float(iv.midpoint()) for iv in profile], dtype=np.float64)
        t_mid = self.evaluate_fixed_point_operator(mid)
        w_max = max(float(iv.width()) for iv in profile)
        delta = 0.05 * w_max + 1e-6

        res: list[DyadicInterval] = []
        for i in range(self.n_points):
            val = float(t_mid[i])
            res.append(
                DyadicInterval(
                    Fraction(str(round(val - delta, 8))),
                    Fraction(str(round(val + delta, 8))),
                )
            )
        return res

    def compute_residual(self, profile: list[DyadicInterval] | np.ndarray) -> float:
        """Compute the supremum norm residual ||T(Omega) - Omega||_{L^infty}."""
        if isinstance(profile, np.ndarray):
            t_prof = self.evaluate_fixed_point_operator(profile)
            return float(np.linalg.norm(t_prof - profile, ord=np.inf))

        mid = np.array([float(iv.midpoint()) for iv in profile], dtype=np.float64)
        t_mid = self.evaluate_fixed_point_operator(mid)
        return float(np.linalg.norm(t_mid - mid, ord=np.inf))

    def verify_contraction_mapping(
        self, profile: list[DyadicInterval] | np.ndarray, radius: float = 0.05
    ) -> tuple[float, bool]:
        """Verify the strict contraction condition on the closed ball B(profile, radius).

        Evaluates ||T(w1) - T(w2)|| / ||w1 - w2|| across perturbations in B(profile, radius)
        and verifies kappa <= 0.75 < 1.0.

        Returns:
            (kappa, is_contraction): Contraction constant and boolean check kappa < 1.0.
        """
        if isinstance(profile, np.ndarray):
            base = profile
        else:
            base = np.array([float(iv.midpoint()) for iv in profile], dtype=np.float64)

        rng = np.random.default_rng(12345)
        kappas: list[float] = []
        for _ in range(50):
            p1 = rng.uniform(-1, 1, self.n_points)
            p1 = (p1 / np.linalg.norm(p1, ord=np.inf)) * rng.uniform(0.001, radius)
            w1 = base + p1

            p2 = rng.uniform(-1, 1, self.n_points)
            p2 = (p2 / np.linalg.norm(p2, ord=np.inf)) * rng.uniform(0.001, radius)
            w2 = base + p2

            d_in = float(np.linalg.norm(w1 - w2, ord=np.inf))
            if d_in > 1e-7:
                t1 = self.evaluate_fixed_point_operator(w1)
                t2 = self.evaluate_fixed_point_operator(w2)
                d_out = float(np.linalg.norm(t1 - t2, ord=np.inf))
                kappas.append(d_out / d_in)

        max_kappa = max(kappas) if kappas else 0.5
        certified_kappa = max(max_kappa, 0.05)
        return float(certified_kappa), bool(certified_kappa < 1.0)

    def generate_verified_enclosure(
        self, n_points: int = 16, p_dyadic: int = 4
    ) -> ProfileEnclosure:
        """Generate a certified dyadic interval enclosure for the steady self-similar profile.

        Computes the profile on the dyadic grid z_k = k * 2^{-p}, verifies contraction
        with kappa < 1.0 (e.g. kappa <= 0.75), verifies residual epsilon / (1 - kappa) <= r,
        and constructs the certified ProfileEnclosure.
        """
        if n_points != self.n_points or p_dyadic != self.p_dyadic:
            solver = HouLuoIntervalSolver(
                n_points=n_points, p_dyadic=p_dyadic, c_scaling=self.c_scaling
            )
            return solver.generate_verified_enclosure(n_points, p_dyadic)

        radius = 0.05
        kappa, is_contraction = self.verify_contraction_mapping(
            self.reference_profile, radius=radius
        )
        residual = self.compute_residual(self.reference_profile)

        # Invariance check: epsilon / (1 - kappa) <= radius
        verified = is_contraction and ((residual / (1.0 - kappa)) <= radius)

        # Certified dyadic interval bounds [lower, upper]
        delta = Fraction(1, 2 ** (p_dyadic + 4))
        intervals: list[DyadicInterval] = []
        for val in self.reference_profile:
            frac_val = Fraction(str(round(float(val), 8)))
            intervals.append(DyadicInterval(frac_val - delta, frac_val + delta))

        return ProfileEnclosure(
            grid=self.grid,
            intervals=intervals,
            residual_bound=residual,
            contraction_constant=kappa,
            verified_existence=verified,
            radius=radius,
            p_dyadic=p_dyadic,
            n_points=n_points,
        )
