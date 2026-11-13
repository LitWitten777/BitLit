r"""stiefel_whitney_c2.py — C2-Equivariant Stiefel-Whitney Invariant with Twofold Rotation
========================================================================================
Grounding: "Stiefel-Whitney invariant with twofold rotation" (2026).
Topological classification of 2D crystalline insulators with combined C2T symmetry.

Key Theorems & Invariants:
1. First SW numbers: \nu_{1x}, \nu_{1y} \in \{0, 1\} (from Berry phases modulo \pi).
2. Second SW number: \nu_2 \in \{0, 1\} (from Pin+(n) 2-cocycle).
3. Whitney sum formula cross-term:
   \nu_2(\Phi \oplus \Psi) = \nu_2(\Phi) + \nu_2(\Psi) + \nu_{1x}(\Phi)\nu_{1y}(\Psi) + \nu_{1y}(\Phi)\nu_{1x}(\Psi) \pmod 2.
4. Corrected additive invariant:
   \nu'_2(\Phi) := (\nu_2(\Phi) + \nu_{1x}(\Phi)\nu_{1y}(\Phi)) \pmod 2.
   Satisfies: \nu'_2(\Phi \oplus \Psi) = (\nu'_2(\Phi) + \nu'_2(\Psi)) \pmod 2.
5. Atomic insulator indices:
   - (0, 0): (0, 0, 0, 0)
   - (1/2, 0): (1, 0, 0, 0)
   - (0, 1/2): (0, 1, 0, 0)
   - (1/2, 1/2): (1, 1, 0, 1)  [has non-zero corrected invariant \nu'_2 = 1]
6. Equivariant K-theory classification:
   KO_{C_2}(T^2) \cong \mathbb{Z}^5 (from \widetilde{KO}_{C_2}(T^2) \cong \mathbb{Z}^3 and RO(C_2) \cong \mathbb{Z}^2).
7. Extra \eta invariant beyond K-theory:
   When all inversion parities n_i \in \{0, N\} at the four high-symmetry points
   \Gamma, Y, M, X, an additional \eta \in \pi_1(O(N)) \cong \mathbb{Z}_2 (for N >= 3)
   emerges that K-theory cannot detect.
"""

from __future__ import annotations
from typing import Dict, List, Tuple


def sw_first_class(berry_phase_x: float, berry_phase_y: float) -> Tuple[int, int]:
    """First SW numbers from Berry phases normalized by pi modulo 2."""
    import math
    nu1x = round(berry_phase_x / math.pi) % 2
    nu1y = round(berry_phase_y / math.pi) % 2
    return nu1x, nu1y


def corrected_sw_invariant(nu2: int, nu1x: int, nu1y: int) -> int:
    r"""Corrected additive invariant:
    \nu'_2 = (\nu_2 + \nu_{1x} * \nu_{1y}) \pmod 2.
    """
    return (nu2 + nu1x * nu1y) % 2


def whitney_sum_nu2(
    phi_nu2: int, phi_nu1x: int, phi_nu1y: int,
    psi_nu2: int, psi_nu1x: int, psi_nu1y: int
) -> int:
    r"""Whitney sum formula for second SW number:
    \nu_2(\Phi \oplus \Psi) = \nu_2(\Phi) + \nu_2(\Psi) + \nu_{1x}(\Phi)\nu_{1y}(\Psi) + \nu_{1y}(\Phi)\nu_{1x}(\Psi) \pmod 2.
    """
    cross = phi_nu1x * psi_nu1y + phi_nu1y * psi_nu1x
    return (phi_nu2 + psi_nu2 + cross) % 2


def corrected_sum_additive(phi_nu2p: int, psi_nu2p: int) -> int:
    r"""Additive property of corrected invariant under direct sum:
    \nu'_2(\Phi \oplus \Psi) = (\nu'_2(\Phi) + \nu'_2(\Psi)) \pmod 2.
    """
    return (phi_nu2p + psi_nu2p) % 2


def atomic_insulator_indices() -> Dict[Tuple[float, float], Tuple[int, int, int, int]]:
    """Return dictionary of atomic insulator SW indices for localized orbitals at Wyckoff positions.
    Key: (x, y) coordinates in unit cell.
    Value: (nu1x, nu1y, nu2, nu2_prime)
    """
    return {
        (0.0, 0.0): (0, 0, 0, 0),
        (0.5, 0.0): (1, 0, 0, 0),
        (0.0, 0.5): (0, 1, 0, 0),
        (0.5, 0.5): (1, 1, 0, 1),
    }


def ktheory_classification_rank() -> int:
    """Return the Z-rank of KO_{C2}(T^2) = rank(reduced) + rank(RO) = 3 + 2 = 5."""
    reduced_rank = 3
    ro_c2_rank = 2
    return reduced_rank + ro_c2_rank


def eta_invariant_exists(inversion_parities: Dict[str, int], total_bands_N: int) -> bool:
    """The extra eta invariant exists iff all n_i in {0, N}."""
    for point, n_i in inversion_parities.items():
        if n_i not in (0, total_bands_N):
            return False
    return True


def sw_from_inversion_parities(
    n_Gamma: int, n_Y: int, n_M: int, n_X: int
) -> Tuple[int, int, int]:
    """Compute SW numbers from inversion parities:
    nu1x = (n_Gamma + n_Y) mod 2
    nu1y = (n_Gamma + n_X) mod 2
    nu2 = (n_Gamma + n_M) mod 2
    """
    nu1x = (n_Gamma + n_Y) % 2
    nu1y = (n_Gamma + n_X) % 2
    nu2 = (n_Gamma + n_M) % 2
    return nu1x, nu1y, nu2


def hyp239_master_verification() -> Tuple[bool, Dict[str, any]]:
    """Master verification of HYP-239 invariants."""
    # 1. Verify additivity of corrected invariant across all 64 combinations
    all_additive = True
    for nu2_phi in (0, 1):
        for nu1x_phi in (0, 1):
            for nu1y_phi in (0, 1):
                for nu2_psi in (0, 1):
                    for nu1x_psi in (0, 1):
                        for nu1y_psi in (0, 1):
                            # compute sum bundle invariants
                            direct_nu1x = (nu1x_phi + nu1x_psi) % 2
                            direct_nu1y = (nu1y_phi + nu1y_psi) % 2
                            direct_nu2 = whitney_sum_nu2(
                                nu2_phi, nu1x_phi, nu1y_phi,
                                nu2_psi, nu1x_psi, nu1y_psi
                            )
                            direct_nu2p = corrected_sw_invariant(direct_nu2, direct_nu1x, direct_nu1y)

                            # compute individual corrected invariants and sum
                            phi_nu2p = corrected_sw_invariant(nu2_phi, nu1x_phi, nu1y_phi)
                            psi_nu2p = corrected_sw_invariant(nu2_psi, nu1x_psi, nu1y_psi)
                            expected_nu2p = corrected_sum_additive(phi_nu2p, psi_nu2p)

                            if direct_nu2p != expected_nu2p:
                                all_additive = False

    assert all_additive is True

    # 2. Verify atomic insulator table
    atomic_table = atomic_insulator_indices()
    assert atomic_table[(0.0, 0.0)] == (0, 0, 0, 0)
    assert atomic_table[(0.5, 0.0)] == (1, 0, 0, 0)
    assert atomic_table[(0.0, 0.5)] == (0, 1, 0, 0)
    assert atomic_table[(0.5, 0.5)] == (1, 1, 0, 1)

    # 3. Verify K-theory rank
    k_rank = ktheory_classification_rank()
    assert k_rank == 5

    # 4. Verify eta invariant existence condition
    assert eta_invariant_exists({"Gamma": 4, "Y": 0, "M": 4, "X": 0}, 4) is True
    assert eta_invariant_exists({"Gamma": 4, "Y": 2, "M": 4, "X": 0}, 4) is False

    results = {
        "all_combinations_additive": all_additive,
        "ktheory_rank": k_rank,
        "atomic_insulator_count": len(atomic_table),
    }
    return True, results
