r"""
src/sedenion/geometry/hopf_lift.py
=============================================================================
Hopf Fibration Lift and Bulk-Boundary Bundle Formalization
=============================================================================
Addresses the critique regarding the boundary-to-Hopf correspondence:
  ∂B³ = S² ≅ Hopf base (S³ / S¹).

As bundles, ∂B³ does not automatically inherit a circle bundle from B³:
- The Hopf bundle S³ --(S¹)--> S² has first Chern number c₁ = 1 (non-trivial).
- It admits NO global continuous section σ: S² -> S³ (π₂(S²) ≅ ℤ obstruction).
- It is covered by two canonical coordinate charts:
    U_N = S² \ {(0, 0, -1)} with local section σ_N(p)
    U_S = S² \ {(0, 0,  1)} with local section σ_S(p)
  related on the equator by the transition function g_{NS}(e^{iφ}) = e^{iφ}.
- The open 3-ball B³ is contractible (H²(B³; ℤ) = 0), so any principal U(1) bundle
  over B³ is topologically trivial (B³ × S¹).
- Therefore, extending the "internal phase" into the interior is an explicit choice
  of trivialization or radial pullback Π: B³ \ {0} -> S², which exhibits a Dirac
  monopole singularity at the origin r = 0.
=============================================================================
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Optional, Tuple
import numpy as np
from numpy.typing import NDArray


@dataclass(frozen=True)
class HopfBundleChart:
    """Represents a canonical local section chart for the Hopf fibration."""
    name: str
    excluded_pole: Tuple[float, float, float]
    valid_range_z: Tuple[float, float]  # (min_z, max_z) open/closed intervals


class HopfFibration:
    """
    Formal geometric implementation of the Hopf principal bundle S³ --(S¹)--> S².
    """

    CHART_NORTH = HopfBundleChart(
        name="North",
        excluded_pole=(0.0, 0.0, -1.0),
        valid_range_z=(-1.0, 1.0),
    )
    CHART_SOUTH = HopfBundleChart(
        name="South",
        excluded_pole=(0.0, 0.0, 1.0),
        valid_range_z=(-1.0, 1.0),
    )

    @staticmethod
    def project_s3_to_s2(q: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Hopf projection π: S³ -> S².
        Given unit quaternion q = (q0, q1, q2, q3) with ||q|| = 1:
          z = q0 + i*q1
          w = q2 + i*q3
          π(q) = (2 Re(z w̄), 2 Im(z w̄), |z|² - |w|²)
               = (2(q0*q2 + q1*q3), 2(q1*q2 - q0*q3), q0² + q1² - q2² - q3²)
        """
        q = np.asarray(q, dtype=np.float64)
        norm = np.linalg.norm(q)
        if norm < 1e-12:
            raise ValueError("Zero quaternion cannot be projected.")
        q = q / norm
        q0, q1, q2, q3 = q

        x = 2.0 * (q0 * q2 + q1 * q3)
        y = 2.0 * (q1 * q2 - q0 * q3)
        z = (q0 * q0 + q1 * q1) - (q2 * q2 + q3 * q3)
        res = np.array([x, y, z], dtype=np.float64)
        return res / np.linalg.norm(res)

    @staticmethod
    def action_s1(q: NDArray[np.float64], theta: float) -> NDArray[np.float64]:
        """
        Principal S¹ action on S³:
          q ↦ q * e^{i θ} = (z * e^{i θ}, w * e^{i θ})
        """
        q = np.asarray(q, dtype=np.float64)
        q0, q1, q2, q3 = q
        c, s = math.cos(theta), math.sin(theta)
        # z' = (q0 + i q1)(c + i s) = (q0 c - q1 s) + i (q0 s + q1 c)
        # w' = (q2 + i q3)(c + i s) = (q2 c - q3 s) + i (q2 s + q3 c)
        return np.array([
            q0 * c - q1 * s,
            q0 * s + q1 * c,
            q2 * c - q3 * s,
            q2 * s + q3 * c,
        ], dtype=np.float64)

    @staticmethod
    def section_north(p: NDArray[np.float64]) -> NDArray[np.float64]:
        r"""
        Canonical local section σ_N: S² \ {(0,0,-1)} -> S³.
        For point p = (x, y, z) on S² with z > -1:
          σ_N(p) = 1 / sqrt(2(1 + z)) * (1 + z, 0, x, -y)
        """
        p = np.asarray(p, dtype=np.float64)
        norm = np.linalg.norm(p)
        if norm < 1e-12:
            raise ValueError("Zero vector on S².")
        p = p / norm
        x, y, z = p
        if z <= -1.0 + 1e-12:
            raise ValueError(f"Point {p} is at the south pole; undefined on North chart.")
        scale = 1.0 / math.sqrt(2.0 * (1.0 + z))
        return np.array([scale * (1.0 + z), 0.0, scale * x, -scale * y], dtype=np.float64)

    @staticmethod
    def section_south(p: NDArray[np.float64]) -> NDArray[np.float64]:
        r"""
        Canonical local section σ_S: S² \ {(0,0,1)} -> S³.
        For point p = (x, y, z) on S² with z < 1:
          σ_S(p) = 1 / sqrt(2(1 - z)) * (x, y, 1 - z, 0)
        """
        p = np.asarray(p, dtype=np.float64)
        norm = np.linalg.norm(p)
        if norm < 1e-12:
            raise ValueError("Zero vector on S².")
        p = p / norm
        x, y, z = p
        if z >= 1.0 - 1e-12:
            raise ValueError(f"Point {p} is at the north pole; undefined on South chart.")
        scale = 1.0 / math.sqrt(2.0 * (1.0 - z))
        return np.array([scale * x, scale * y, scale * (1.0 - z), 0.0], dtype=np.float64)

    @classmethod
    def lift_to_s3(cls, p: NDArray[np.float64], theta: float = 0.0) -> NDArray[np.float64]:
        """
        Lift point p ∈ S² to S³ fiber point, with optional fiber phase θ ∈ [0, 2π).
        Chooses North or South chart automatically to avoid coordinate singularities.
        """
        p_arr = np.asarray(p, dtype=np.float64)
        norm = np.linalg.norm(p_arr)
        if norm < 1e-12:
            raise ValueError("Zero vector on S².")
        p_arr = p_arr / norm
        if p_arr[2] >= -0.5:
            q = cls.section_north(p_arr)
        else:
            q = cls.section_south(p_arr)
        if theta != 0.0:
            q = cls.action_s1(q, theta)
        return q

    @classmethod
    def project_to_s2(cls, q: NDArray[np.float64]) -> NDArray[np.float64]:
        """Convenience alias for project_s3_to_s2."""
        return cls.project_s3_to_s2(q)

    @classmethod
    def transition_phase(cls, p: NDArray[np.float64]) -> float:
        """
        Transition function g_{NS}(p) ∈ U(1) on the overlap U_N ∩ U_S.
        Finds θ such that:
          σ_S(p) = σ_N(p) · e^{i θ}
        Returns the angle θ ∈ (-π, π].
        """
        q_N = cls.section_north(p)
        q_S = cls.section_south(p)
        z_N = complex(q_N[0], q_N[1])
        z_S = complex(q_S[0], q_S[1])
        if abs(z_N) > 1e-10:
            ratio = z_S / z_N
            return math.atan2(ratio.imag, ratio.real)
        w_N = complex(q_N[2], q_N[3])
        w_S = complex(q_S[2], q_S[3])
        ratio = w_S / w_N
        return math.atan2(ratio.imag, ratio.real)

    @classmethod
    def compute_first_chern_number(cls, n_points: int = 360) -> int:
        """
        Computes the first Chern number c₁ by integrating the transition function
        phase winding along the equator S¹ = {(cos φ, sin φ, 0)}:
          c₁ = 1 / (2π) ∮_{S¹} d(phase(g_{NS}))
        """
        phases = []
        phis = np.linspace(0.0, 2.0 * math.pi, n_points, endpoint=False)
        for phi in phis:
            p = np.array([math.cos(phi), math.sin(phi), 0.0], dtype=np.float64)
            th = cls.transition_phase(p)
            phases.append(th)

        # Unwind phases
        unwound = np.unwrap(phases)
        delta = unwound[-1] + (cls.transition_phase(np.array([1.0, 0.0, 0.0])) - phases[0]) - unwound[0]
        c1 = round(delta / (2.0 * math.pi))
        return int(c1)


class BulkBoundaryExtension:
    """
    Formalizes the extension from the Poincaré ball B³ interior to the boundary S² = ∂B³.
    """

    @staticmethod
    def radial_projection(x: NDArray[np.float64]) -> Tuple[NDArray[np.float64], float]:
        r"""
        Pulls back a point x in B³ \ {0} to the boundary S²:
          p(x) = x / ||x||,  r = ||x||
        Raises ValueError if x is at the monopole singularity (origin r = 0).
        """
        x = np.asarray(x, dtype=np.float64)
        r = float(np.linalg.norm(x))
        if r < 1e-12:
            raise ValueError("Origin r = 0 is a monopole singularity for radial retraction.")
        if r >= 1.0:
            raise ValueError(f"Point {x} with norm {r} is outside the open Poincaré ball B³.")
        return x / r, r

    @staticmethod
    def explain_bundle_obstruction() -> dict[str, str]:
        """
        Returns formal mathematical statement explaining why 'internal phase'
        cannot be canonically extended from ∂B³ to B³ without choosing a gauge.
        """
        return {
            "theorem": "Bundle Triviality on B³ vs Non-Triviality on S²",
            "cohomology_bulk": "H²(B³; ℤ) = 0 (B³ is contractible, all bundles trivial)",
            "cohomology_boundary": "H²(S²; ℤ) ≅ ℤ, with c₁(Hopf) = 1 (non-trivial)",
            "lift_nature": "Free gauge choice: an internal phase θ over the bulk B³ represents a free section of the trivial bundle B³ × S¹, not an invariant boundary observable.",
            "singularity": "Radial pullback Π: B³ \\ {0} -> S² has a point monopole singularity at r = 0.",
        }
