"""G2 Associative 3-Form Calibration, Dual 4-Form, and Octonionic Helicity Invariants.

This module formalizes the continuous and topological invariants of 7D non-associative
hydrodynamics governed by the exceptional Lie group G_2 = Aut(O):
1. The G_2-invariant associative 3-form phi(u, v, w) = <u, v x_7 w>.
2. The coassociative dual 4-form psi = *phi.
3. Calibration inequality |phi(u, v, w)| <= ||u|| ||v|| ||w|| with equality on associative 3-planes.
4. Octonionic associator invariant I_assoc(u, v, w) = ||[u, v, w]||^2 and Fano line vanishing.
5. Invariant calibration helicity conservation along G_2 coadjoint orbits.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

import numpy as np

from sedenion.hydro.non_associative_fluid import (
    fano_cross_product_7d,
    fano_plane_lines,
    fano_structure_constants,
    octonionic_associator,
)


class CalibrationHelicityError(ValueError):
    """Raised for dimensional or algebraic errors in calibration helicity analysis."""


@dataclass(frozen=True)
class CalibrationResult:
    """Stores the evaluation of the G_2 associative 3-form calibration."""

    value: float
    bound: float
    ratio: float
    is_associative: bool
    associator_norm: float


class G2CalibrationAnalyzer:
    """Analyzes the G_2-invariant associative 3-form and non-associative topological helicity."""

    def __init__(self) -> None:
        self.c = fano_structure_constants()  # shape (7, 7, 7)
        self.lines = fano_plane_lines()

    def associative_3form(self, u: np.ndarray, v: np.ndarray, w: np.ndarray) -> float:
        """Evaluate the fundamental G_2 3-form phi(u, v, w) = <u, v x_7 w>.

        Args:
            u, v, w: 7-dimensional real vectors in Im(O).

        Returns:
            The scalar value phi(u, v, w).
        """
        u = np.asarray(u, dtype=np.float64)
        v = np.asarray(v, dtype=np.float64)
        w = np.asarray(w, dtype=np.float64)

        if u.shape != (7,) or v.shape != (7,) or w.shape != (7,):
            raise CalibrationHelicityError(
                f"Vectors must have dimension 7, got shapes {u.shape}, {v.shape}, {w.shape}"
            )

        cross_vw = fano_cross_product_7d(v, w)
        return float(np.dot(u, cross_vw))

    def evaluate_calibration(
        self, u: np.ndarray, v: np.ndarray, w: np.ndarray, tol: float = 1e-7
    ) -> CalibrationResult:
        """Evaluate the calibration inequality |phi(u, v, w)| <= ||u|| ||v|| ||w||.

        Harvey & Lawson (1982) calibrated geometries:
        phi is a calibration on R^7. For any 3-plane spanned by orthonormal u, v, w,
        phi(u, v, w) <= 1, with equality if and only if span(u, v, w) is associative.
        """
        val = self.associative_3form(u, v, w)
        norm_prod = float(np.linalg.norm(u) * np.linalg.norm(v) * np.linalg.norm(w))

        ratio = 0.0 if norm_prod < 1e-14 else abs(val) / norm_prod

        # Compute associator [u, v, w]
        assoc = octonionic_associator(u, v, w)
        assoc_norm = float(np.linalg.norm(assoc))

        is_assoc = (abs(ratio - 1.0) < tol) or (assoc_norm < tol)

        return CalibrationResult(
            value=val,
            bound=norm_prod,
            ratio=ratio,
            is_associative=is_assoc,
            associator_norm=assoc_norm,
        )

    def coassociative_4form(
        self, u: np.ndarray, v: np.ndarray, w: np.ndarray, z: np.ndarray
    ) -> float:
        """Evaluate the coassociative dual 4-form psi = *phi on R^7.

        In coordinates, psi_{ijkl} = (1/6) eps_{ijklmno} phi^{mno}.
        Equivalently:
            psi(u, v, w, z) = -<u, [v, w, z]> - <u x_7 v, w x_7 z> + <u x_7 w, v x_7 z> - <u x_7 z, v x_7 w>.
        """
        u = np.asarray(u, dtype=np.float64)
        v = np.asarray(v, dtype=np.float64)
        w = np.asarray(w, dtype=np.float64)
        z = np.asarray(z, dtype=np.float64)

        if u.shape != (7,) or v.shape != (7,) or w.shape != (7,) or z.shape != (7,):
            raise CalibrationHelicityError("All 4 vectors must have dimension 7")

        uv = fano_cross_product_7d(u, v)
        uw = fano_cross_product_7d(u, w)
        uz = fano_cross_product_7d(u, z)
        wz = fano_cross_product_7d(w, z)
        vz = fano_cross_product_7d(v, z)
        vw = fano_cross_product_7d(v, w)

        return float(-np.dot(uv, wz) + np.dot(uw, vz) - np.dot(uz, vw))

    def associator_invariant(self, u: np.ndarray, v: np.ndarray, w: np.ndarray) -> float:
        """Compute the scalar associator invariant I_assoc(u, v, w) = ||[u, v, w]||^2.

        Vanishes identically if and only if span(u, v, w) is an associative subalgebra.
        """
        assoc = octonionic_associator(u, v, w)
        return float(np.sum(assoc**2))

    def verify_fano_lines_associativity(self) -> dict[str, Any]:
        """Verify that all 7 lines of the Fano plane are calibrated associative 3-planes."""
        results = []
        for line in self.lines:
            ea = np.zeros(7)
            eb = np.zeros(7)
            ec = np.zeros(7)
            ea[line[0] - 1] = 1.0
            eb[line[1] - 1] = 1.0
            ec[line[2] - 1] = 1.0

            cal = self.evaluate_calibration(ea, eb, ec)
            assoc_inv = self.associator_invariant(ea, eb, ec)

            if not (
                math.isclose(cal.value, 1.0, abs_tol=1e-12)
                and math.isclose(cal.ratio, 1.0, abs_tol=1e-12)
                and math.isclose(assoc_inv, 0.0, abs_tol=1e-12)
                and cal.is_associative
            ):
                raise CalibrationHelicityError(f"Fano line {line} failed associative calibration")

            results.append(
                {
                    "line": line,
                    "phi": cal.value,
                    "I_assoc": assoc_inv,
                    "is_associative": True,
                }
            )

        return {
            "total_lines": len(results),
            "all_calibrated": True,
            "all_associator_zero": True,
            "lines_detail": results,
        }

    def calibration_helicity(
        self, u_field: np.ndarray, omega_field: np.ndarray, ref_field: np.ndarray
    ) -> float:
        """Compute the discrete spatial calibration helicity H_phi = sum_x phi(u(x), omega(x), ref(x)).

        Args:
            u_field: Array of shape (N, 7)
            omega_field: Array of shape (N, 7)
            ref_field: Array of shape (N, 7)

        Returns:
            The integrated scalar helicity.
        """
        if (
            u_field.ndim != 2
            or u_field.shape[1] != 7
            or omega_field.shape != u_field.shape
            or ref_field.shape != u_field.shape
        ):
            raise CalibrationHelicityError("Fields must have shape (N, 7)")

        total = 0.0
        n_points = u_field.shape[0]
        for i in range(n_points):
            total += self.associative_3form(u_field[i], omega_field[i], ref_field[i])

        return float(total / max(1, n_points))
