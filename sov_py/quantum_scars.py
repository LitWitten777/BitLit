"""
Quantum Many-Body Scar Towers on Cayley-Dickson Annihilation Graphs.

Grounds CERN-TH-2026-209:
Joao Barata, Kiryl Pakrouski, Andrey V. Sadofyev (2026),
"Exact group invariant scar towers in two dimensional gauge theories".

Formalized in Lean 4: formal/TowerQuantumScars.lean (HYP-230).
"""

from typing import Tuple, List, Dict
import numpy as np


def build_twin_zero_sum_modes(D: int) -> Tuple[np.ndarray, int, int]:
    """
    Constructs the exact 3M orthonormal transverse zero-sum modes
    spanning the quantum scar subspace S_chi = ker(A_chi) in dimension D.

    Parameters:
        D: Cayley-Dickson dimension (D >= 16).

    Returns:
        (modes, N, dim_scar):
        - modes: (N, 3M) orthonormal matrix whose columns span ker(A_chi)
        - N: sector order 2(D - 4)
        - dim_scar: 3M = 3(D - 4)/2 (identically 75% of N)
    """
    N = 2 * (D - 4)
    M = (D - 4) // 2
    dim_scar = 3 * M

    modes = np.zeros((N, dim_scar), dtype=float)

    col_idx = 0
    for k in range(M):
        # 4 vertices in twin class k: indices 4*k, 4*k+1, 4*k+2, 4*k+3
        v0 = 4 * k
        v1 = 4 * k + 1
        v2 = 4 * k + 2
        v3 = 4 * k + 3

        # Mode 1: (v0 - v1) / sqrt(2)
        modes[v0, col_idx] = 1.0 / np.sqrt(2.0)
        modes[v1, col_idx] = -1.0 / np.sqrt(2.0)
        col_idx += 1

        # Mode 2: (v2 - v3) / sqrt(2)
        modes[v2, col_idx] = 1.0 / np.sqrt(2.0)
        modes[v3, col_idx] = -1.0 / np.sqrt(2.0)
        col_idx += 1

        # Mode 3: (v0 + v1 - v2 - v3) / 2
        modes[v0, col_idx] = 0.5
        modes[v1, col_idx] = 0.5
        modes[v2, col_idx] = -0.5
        modes[v3, col_idx] = -0.5
        col_idx += 1

    assert col_idx == dim_scar
    # Verify orthonormality
    assert np.allclose(modes.T @ modes, np.eye(dim_scar), atol=1e-14)
    return modes, N, dim_scar


def simulate_scar_wavepacket_revival(
    modes: np.ndarray,
    Delta: float = 1.5,
    m_revivals: int = 2
) -> Dict[str, float]:
    """
    Simulates the unitary time evolution of a coherent wavepacket inside the scar subspace.
    Measures fidelity at t = m * T_revival where T_revival = 2*pi / Delta.
    """
    dim_scar = modes.shape[1]
    T_revival = 2.0 * np.pi / Delta

    # Coherent Poissonian packet centered at n0 = dim_scar // 4
    n0 = dim_scar // 4
    c = np.exp(-0.5 * (np.arange(dim_scar) - n0)**2 / 2.0)
    c = c / np.linalg.norm(c)
    psi_0 = modes @ c

    # Energy eigenvalues: E_n = n * Delta
    energies = np.arange(dim_scar) * Delta

    results = {"T_revival": T_revival}
    for m in range(1, m_revivals + 1):
        t = m * T_revival
        phases = np.exp(-1j * energies * t)
        psi_t = modes @ (c * phases)
        fidelity = float(np.abs(np.vdot(psi_0, psi_t))**2)
        results[f"fidelity_m_{m}"] = fidelity

    return results


def compute_scar_bipartite_entropy(
    mode: np.ndarray,
    partition_A: List[int]
) -> float:
    """
    Computes the bipartite entanglement entropy S(V_A) of a normalized mode
    across subsystem V_A.
    """
    p_A = float(np.sum(np.abs(mode[partition_A])**2))
    p_B = 1.0 - p_A

    if p_A <= 1e-15 or p_B <= 1e-15:
        return 0.0

    return float(- p_A * np.log2(p_A) - p_B * np.log2(p_B))
