"""
Protein Fold Sedenion Bridge: Dihedral Angle Frames on Stiefel Manifold V₂(ℝ⁷).

Mathematical & Biophysical Foundations:
1. Backbone Polypeptide Geometry:
   Each amino acid residue i is parameterized by Ramachandran dihedral angles (ϕ_i, ψ_i) ∈ [-π, π]².
   Canonical secondary motifs:
   - α-helix: (ϕ ≈ -57°, ψ ≈ -47°)
   - β-sheet: (ϕ ≈ -139°, ψ ≈ +135°)
2. Stiefel Orthonormal 2-Frame Embedding on V₂(ℝ⁷) ≅ G₂/SU(2):
   P_i = [u_i, v_i] ∈ ℝ⁷ˣ² where:
   u_i = (cos ϕ_i, sin ϕ_i, 0, 0, 0, 0, 0)
   v_i = (0, 0, cos ψ_i, sin ψ_i, 0, 0, 0)
   Because u_i · v_i = 0 and ||u_i|| = ||v_i|| = 1, P_i is an exact orthonormal 2-frame on V₂(ℝ⁷).
3. Zero-Divisor Interaction Energy & Native Fold Stability:
   Residue contacts (i, j) with high secondary structure coherence map to mutually orthogonal
   2-frames (P_iᵀ P_j ≈ 0₂ₓ₂), minimizing the non-associative zero-divisor collision potential
   along geodesic valleys of the Stiefel manifold.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np


@dataclass
class ResidueFrame:
    residue_index: int
    amino_acid: str
    phi_rad: float
    psi_rad: float
    frame_u: np.ndarray  # 7D vector
    frame_v: np.ndarray  # 7D vector
    secondary_motif: str  # "ALPHA_HELIX", "BETA_SHEET", "COIL"


@dataclass
class FoldEnergyReport:
    sequence_length: int
    num_contacts: int
    total_zd_repulsion: float
    mean_frame_orthogonality: float
    is_geodesic_valley_stable: bool


class ProteinFoldSedenionBridge:
    """
    Bridges protein backbone geometry with Stiefel manifold 2-frames and sedenion zero-divisor geodesics.
    """

    # Canonical Ramachandran centers (in degrees)
    ALPHA_HELIX_CENTER = (-57.0, -47.0)
    BETA_SHEET_CENTER = (-139.0, 135.0)

    def __init__(self, alpha_tolerance_deg: float = 35.0, beta_tolerance_deg: float = 45.0) -> None:
        self.alpha_tolerance_deg = alpha_tolerance_deg
        self.beta_tolerance_deg = beta_tolerance_deg
        self.alpha_center = self.ALPHA_HELIX_CENTER
        self.beta_center = self.BETA_SHEET_CENTER

    @classmethod
    def classify_secondary_structure(cls, phi_deg: float, psi_deg: float) -> str:
        """Classifies secondary structure motif from Ramachandran angles."""
        d_alpha = math.hypot(phi_deg - cls.ALPHA_HELIX_CENTER[0], psi_deg - cls.ALPHA_HELIX_CENTER[1])
        d_beta = math.hypot(phi_deg - cls.BETA_SHEET_CENTER[0], psi_deg - cls.BETA_SHEET_CENTER[1])

        if d_alpha < 35.0:
            return "ALPHA_HELIX"
        elif d_beta < 45.0:
            return "BETA_SHEET"
        else:
            return "COIL"

    def embed_residue_frame(
        self,
        index: int,
        amino_acid: str,
        phi_rad: float,
        psi_rad: float,
        backbone_twist_rad: float = 0.0,
    ) -> ResidueFrame:
        """Constructs an exact orthonormal 2-frame on V₂(ℝ⁷) from (ϕ, ψ) and backbone twist."""
        u = np.zeros(7, dtype=np.float64)
        v = np.zeros(7, dtype=np.float64)

        cos_t = math.cos(backbone_twist_rad)
        sin_t = math.sin(backbone_twist_rad)

        # Coordinate embedding preserving u · v = 0 and ||u|| = ||v|| = 1 identically
        u[0] = math.cos(phi_rad) * cos_t
        u[1] = math.sin(phi_rad) * cos_t
        u[4] = sin_t

        v[2] = math.cos(psi_rad) * cos_t
        v[3] = math.sin(psi_rad) * cos_t
        v[5] = sin_t

        phi_deg = math.degrees(phi_rad)
        psi_deg = math.degrees(psi_rad)
        motif = self.classify_secondary_structure(phi_deg, psi_deg)

        return ResidueFrame(
            residue_index=index,
            amino_acid=amino_acid,
            phi_rad=phi_rad,
            psi_rad=psi_rad,
            frame_u=u,
            frame_v=v,
            secondary_motif=motif,
        )

    def build_synthetic_helix(self, sequence: str) -> List[ResidueFrame]:
        """Generates canonical α-helical frames with 100° helical rotation per residue."""
        phi = math.radians(-57.0)
        psi = math.radians(-47.0)
        twist_step = 2.0 * math.pi / 3.6  # 100° in radians
        return [
            self.embed_residue_frame(i + 1, aa, phi, psi, backbone_twist_rad=i * twist_step)
            for i, aa in enumerate(sequence)
        ]

    def build_synthetic_sheet(self, sequence: str) -> List[ResidueFrame]:
        """Generates canonical β-sheet frames with 180° alternating pleating."""
        phi = math.radians(-139.0)
        psi = math.radians(135.0)
        twist_step = math.pi  # 180° alternating pleat
        return [
            self.embed_residue_frame(i + 1, aa, phi, psi, backbone_twist_rad=i * twist_step)
            for i, aa in enumerate(sequence)
        ]

    def build_from_dihedrals(
        self,
        sequence: str,
        dihedral_angles: Sequence[Tuple[float, float]],
        backbone_twists: Optional[Sequence[float]] = None,
    ) -> List[ResidueFrame]:
        """
        Constructs residue frames from an explicit sequence of (phi, psi) dihedral angles (in degrees or radians).
        Supports integration with real-world PDB/AlphaFold backbone trajectories.
        """
        frames = []
        n = min(len(sequence), len(dihedral_angles))
        for i in range(n):
            aa = sequence[i]
            phi_val, psi_val = dihedral_angles[i]
            # Convert degrees to radians if values exceed [-pi, pi]
            phi_rad = math.radians(phi_val) if abs(phi_val) > math.pi else phi_val
            psi_rad = math.radians(psi_val) if abs(psi_val) > math.pi else psi_val
            twist = backbone_twists[i] if (backbone_twists and i < len(backbone_twists)) else 0.0
            frames.append(self.embed_residue_frame(i + 1, aa, phi_rad, psi_rad, backbone_twist_rad=twist))
        return frames

    def compute_fold_energy(self, frames: List[ResidueFrame]) -> FoldEnergyReport:
        """
        Computes zero-divisor interaction energy across all residue contact pairs (|i - j| ≥ 3).
        """
        n = len(frames)
        num_contacts = 0
        total_zd_repulsion = 0.0
        ortho_deviations = []

        for i in range(n):
            for j in range(i + 3, n):
                f1 = frames[i]
                f2 = frames[j]
                num_contacts += 1

                # Frame overlap matrix: P_iᵀ P_j ∈ ℝ²ˣ²
                dot_uu = float(np.dot(f1.frame_u, f2.frame_u))
                dot_uv = float(np.dot(f1.frame_u, f2.frame_v))
                dot_vu = float(np.dot(f1.frame_v, f2.frame_u))
                dot_vv = float(np.dot(f1.frame_v, f2.frame_v))

                overlap_norm_sq = dot_uu**2 + dot_uv**2 + dot_vu**2 + dot_vv**2
                ortho_deviations.append(overlap_norm_sq)

                # Annihilation potential: when overlap is minimal, zero-divisor repulsion vanishes
                repulsion = overlap_norm_sq * (1.0 / math.sqrt(j - i))
                total_zd_repulsion += repulsion

        mean_overlap = float(np.mean(ortho_deviations)) if ortho_deviations else 0.0
        mean_repulsion = (total_zd_repulsion / max(num_contacts, 1))
        # Normalized orthogonality in [0, 1]
        normalized_orthogonality = max(0.0, 1.0 - (mean_overlap / 2.0))
        is_stable = bool(mean_repulsion < 0.75)

        return FoldEnergyReport(
            sequence_length=n,
            num_contacts=num_contacts,
            total_zd_repulsion=total_zd_repulsion,
            mean_frame_orthogonality=normalized_orthogonality,
            is_geodesic_valley_stable=is_stable,
        )
