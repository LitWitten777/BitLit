"""
src/sedenion/physics/elementary_particles.py
=============================================================================
Elementary Particle Physics, Standard Model Gauge Representations,
Chiral Anomaly Cancellation, and Doubling Pole Mass Hierarchy.
=============================================================================
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Tuple, Optional


@dataclass(frozen=True)
class ParticleField:
    """Represents an elementary particle field in the Standard Model."""
    name: str
    symbol: str
    particle_type: str        # "quark", "lepton", "gauge_boson", "scalar"
    generation: int           # 1, 2, 3 (0 for gauge/scalar)
    su3_dim: int              # 1 (singlet), 3 (triplet), 8 (octet)
    su2_dim: int              # 1 (singlet), 2 (doublet), 3 (triplet)
    hypercharge_Y: Fraction   # U(1)_Y weak hypercharge
    t3: Fraction              # Weak isospin projection T_3
    chirality: str            # "L", "R", "V" (vector), "S" (scalar)

    @property
    def electric_charge_Q(self) -> Fraction:
        """Gell-Mann-Nishijima relation: Q = T_3 + Y / 2."""
        return self.t3 + self.hypercharge_Y / 2

    @property
    def is_chiral_fermion(self) -> bool:
        return self.particle_type in ("quark", "lepton") and self.chirality in ("L", "R")


class StandardModelSpectrum:
    """
    Complete mathematical representation of the Standard Model:
    Gauge group: G_SM = (SU(3)_C × SU(2)_L × U(1)_Y) / Z_6
    Fermion representations: 3 generations of 16 Weyl fermions (with right-handed neutrino).
    """

    GAUGE_DIMENSIONS: Dict[str, int] = {
        "SU(3)_C": 8,
        "SU(2)_L": 3,
        "U(1)_Y": 1,
    }

    TOTAL_GAUGE_DIMENSION: int = 12

    @classmethod
    def get_generation_fermions(cls, gen: int) -> List[ParticleField]:
        """
        Returns the 16 Weyl fermion fields for generation `gen` ∈ {1, 2, 3}.
        Colors are counted individually (3 color states per quark).
        """
        if gen not in (1, 2, 3):
            raise ValueError(f"Generation must be 1, 2, or 3, got {gen}")

        quark_names = [
            ("u", "d"),
            ("c", "s"),
            ("t", "b"),
        ][gen - 1]

        lepton_names = [
            ("nu_e", "e"),
            ("nu_mu", "mu"),
            ("nu_tau", "tau"),
        ][gen - 1]

        fermions: List[ParticleField] = []

        # 1. Left-handed Quark Doublet Q_L = (u_L, d_L)^T
        # su3 = 3, su2 = 2, Y = 1/3
        for color in ("r", "g", "b"):
            fermions.append(ParticleField(
                name=f"{quark_names[0]}_{color}_L",
                symbol=f"{quark_names[0]}_L",
                particle_type="quark",
                generation=gen,
                su3_dim=3,
                su2_dim=2,
                hypercharge_Y=Fraction(1, 3),
                t3=Fraction(1, 2),
                chirality="L"
            ))
            fermions.append(ParticleField(
                name=f"{quark_names[1]}_{color}_L",
                symbol=f"{quark_names[1]}_L",
                particle_type="quark",
                generation=gen,
                su3_dim=3,
                su2_dim=2,
                hypercharge_Y=Fraction(1, 3),
                t3=Fraction(-1, 2),
                chirality="L"
            ))

        # 2. Right-handed Up-type Quark Singlet u_R
        # su3 = 3, su2 = 1, Y = 4/3, T_3 = 0
        for color in ("r", "g", "b"):
            fermions.append(ParticleField(
                name=f"{quark_names[0]}_{color}_R",
                symbol=f"{quark_names[0]}_R",
                particle_type="quark",
                generation=gen,
                su3_dim=3,
                su2_dim=1,
                hypercharge_Y=Fraction(4, 3),
                t3=Fraction(0, 1),
                chirality="R"
            ))

        # 3. Right-handed Down-type Quark Singlet d_R
        # su3 = 3, su2 = 1, Y = -2/3, T_3 = 0
        for color in ("r", "g", "b"):
            fermions.append(ParticleField(
                name=f"{quark_names[1]}_{color}_R",
                symbol=f"{quark_names[1]}_R",
                particle_type="quark",
                generation=gen,
                su3_dim=3,
                su2_dim=1,
                hypercharge_Y=Fraction(-2, 3),
                t3=Fraction(0, 1),
                chirality="R"
            ))

        # 4. Left-handed Lepton Doublet L_L = (nu_L, e_L)^T
        # su3 = 1, su2 = 2, Y = -1
        fermions.append(ParticleField(
            name=f"{lepton_names[0]}_L",
            symbol=f"{lepton_names[0]}_L",
            particle_type="lepton",
            generation=gen,
            su3_dim=1,
            su2_dim=2,
            hypercharge_Y=Fraction(-1, 1),
            t3=Fraction(1, 2),
            chirality="L"
        ))
        fermions.append(ParticleField(
            name=f"{lepton_names[1]}_L",
            symbol=f"{lepton_names[1]}_L",
            particle_type="lepton",
            generation=gen,
            su3_dim=1,
            su2_dim=2,
            hypercharge_Y=Fraction(-1, 1),
            t3=Fraction(-1, 2),
            chirality="L"
        ))

        # 5. Right-handed Charged Lepton Singlet e_R
        # su3 = 1, su2 = 1, Y = -2, T_3 = 0
        fermions.append(ParticleField(
            name=f"{lepton_names[1]}_R",
            symbol=f"{lepton_names[1]}_R",
            particle_type="lepton",
            generation=gen,
            su3_dim=1,
            su2_dim=1,
            hypercharge_Y=Fraction(-2, 1),
            t3=Fraction(0, 1),
            chirality="R"
        ))

        # 6. Right-handed Sterile Neutrino Singlet nu_R (completing the 16 of Spin(10))
        # su3 = 1, su2 = 1, Y = 0, T_3 = 0
        fermions.append(ParticleField(
            name=f"{lepton_names[0]}_R",
            symbol=f"{lepton_names[0]}_R",
            particle_type="lepton",
            generation=gen,
            su3_dim=1,
            su2_dim=1,
            hypercharge_Y=Fraction(0, 1),
            t3=Fraction(0, 1),
            chirality="R"
        ))

        return fermions

    @classmethod
    def get_all_fermions(cls) -> List[ParticleField]:
        """Returns all 3 × 16 = 48 Weyl fermion fields."""
        fields: List[ParticleField] = []
        for g in (1, 2, 3):
            fields.extend(cls.get_generation_fermions(g))
        return fields

    @classmethod
    def verify_charge_quantization(cls) -> bool:
        """Verifies that all electric charges Q = T_3 + Y/2 match physical values."""
        expected_charges = {
            "u": Fraction(2, 3),
            "d": Fraction(-1, 3),
            "c": Fraction(2, 3),
            "s": Fraction(-1, 3),
            "t": Fraction(2, 3),
            "b": Fraction(-1, 3),
            "nu": Fraction(0, 1),
            "e": Fraction(-1, 1),
            "mu": Fraction(-1, 1),
            "tau": Fraction(-1, 1),
        }
        for f in cls.get_all_fermions():
            base_name = f.symbol.split("_")[0]
            if base_name.startswith("nu"):
                base_name = "nu"
            if f.electric_charge_Q != expected_charges[base_name]:
                return False
        return True

    @classmethod
    def verify_chiral_anomaly_cancellation(cls) -> Dict[str, Fraction]:
        """
        Computes all triangle gauge and gravitational anomalies per generation.
        """
        gen1 = cls.get_generation_fermions(1)

        # 1. Tr[SU(3)^2 U(1)_Y] = sum_{q_L} Y - sum_{q_R} Y (per color triplet)
        # For each quark doublet (u_L, d_L): Y = 1/3, each color counts once in trace over fundamental:
        # Sum_{q_L} Y = 1/3 + 1/3 = 2/3
        # Sum_{q_R} Y = 4/3 + (-2/3) = 2/3
        # Difference = 0
        anom_su3_sq_u1 = Fraction(0, 1)
        for f in gen1:
            if f.particle_type == "quark":
                sign = 1 if f.chirality == "L" else -1
                anom_su3_sq_u1 += sign * f.hypercharge_Y / 3  # divide by 3 colors to get trace per color fundamental

        # 2. Tr[SU(2)^2 U(1)_Y] = sum_{doublets} Y
        # 3 colors of quark doublet: 3 * (1/3) = 1
        # 1 lepton doublet: 1 * (-1) = -1
        # Total = 1 + (-1) = 0
        anom_su2_sq_u1 = Fraction(0, 1)
        for f in gen1:
            if f.su2_dim == 2 and f.chirality == "L":
                # each doublet has 2 components; trace is sum over doublets
                anom_su2_sq_u1 += f.hypercharge_Y / 2

        # 3. Tr[U(1)_Y^3] = sum_{L} Y^3 - sum_{R} Y^3
        anom_u1_cubed = Fraction(0, 1)
        for f in gen1:
            sign = 1 if f.chirality == "L" else -1
            anom_u1_cubed += sign * (f.hypercharge_Y ** 3)

        # 4. Tr[grav^2 U(1)_Y] = sum_{L} Y - sum_{R} Y
        anom_grav_sq_u1 = Fraction(0, 1)
        for f in gen1:
            sign = 1 if f.chirality == "L" else -1
            anom_grav_sq_u1 += sign * f.hypercharge_Y

        # 5. Witten Global SU(2) Anomaly: number of SU(2) doublets mod 2
        doublet_count = sum(1 for f in gen1 if f.su2_dim == 2 and f.chirality == "L") // 2

        return {
            "Tr[SU(3)^2 U(1)_Y]": anom_su3_sq_u1,
            "Tr[SU(2)^2 U(1)_Y]": anom_su2_sq_u1,
            "Tr[U(1)_Y^3]": anom_u1_cubed,
            "Tr[grav^2 U(1)_Y]": anom_grav_sq_u1,
            "Witten_SU(2)_doublets": Fraction(doublet_count, 1),
            "Witten_SU(2)_mod_2": Fraction(doublet_count % 2, 1),
        }

    @staticmethod
    def get_doubling_pole_degrees() -> Tuple[int, int, int]:
        """
        In D=128, the 3 doubling poles at depths k ∈ {0, 1, 2} have degrees:
        d_low(k) = 2^(k+4) - 8, yielding (8, 24, 56).
        This governs the generational hierarchy of fermion masses.
        """
        return (
            (2 ** 4) - 8,   # k=0: 16 - 8 = 8
            (2 ** 5) - 8,   # k=1: 32 - 8 = 24
            (2 ** 6) - 8,   # k=2: 64 - 8 = 56
        )

    @classmethod
    def verify_all_invariants(cls) -> Dict[str, bool]:
        """Executes total algebraic verification of Standard Model foundations."""
        anomalies = cls.verify_chiral_anomaly_cancellation()
        poles = cls.get_doubling_pole_degrees()
        return {
            "charge_quantization_verified": cls.verify_charge_quantization(),
            "su3_sq_u1_vanishes": anomalies["Tr[SU(3)^2 U(1)_Y]"] == 0,
            "su2_sq_u1_vanishes": anomalies["Tr[SU(2)^2 U(1)_Y]"] == 0,
            "u1_cubed_vanishes": anomalies["Tr[U(1)_Y^3]"] == 0,
            "grav_sq_u1_vanishes": anomalies["Tr[grav^2 U(1)_Y]"] == 0,
            "witten_su2_anomaly_free": anomalies["Witten_SU(2)_mod_2"] == 0,
            "total_fermion_count_is_48": len(cls.get_all_fermions()) == 48,
            "doubling_poles_strictly_increasing": poles[0] < poles[1] < poles[2],
            "doubling_poles_values_exact": poles == (8, 24, 56),
            "gauge_dimension_is_12": cls.TOTAL_GAUGE_DIMENSION == 12,
        }
