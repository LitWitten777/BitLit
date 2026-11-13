"""
Gram-Wishart-Stiefel Formulation & Zero-Divisor Annihilation Decoupling.

Grounds Badis Ydri (July 2026),
"Gram-Wishart-Stiefel formulation of the N=2, large-d gauge theory in 1D",
arXiv:2607.xxxxx.

Formalized in Lean 4: formal/TowerWishartGramStiefel.lean (HYP-229).
"""

from typing import Tuple, Optional
import numpy as np


def compute_stiefel_overlap_matrix(R_V: np.ndarray, R_W: np.ndarray) -> np.ndarray:
    """
    Computes the 2x2 Stiefel overlap matrix Omega = R_V^T R_W
    between two orthonormal 2-frames R_V, R_W in St(2, d) (R_V, R_W are d x 2).
    """
    assert R_V.shape == R_W.shape, "Shape mismatch between R_V and R_W"
    assert R_V.shape[1] == 2, "Expected 2-frames (p=2)"
    return R_V.T @ R_W


def compute_wishart_gram_blocks(
    R_V: np.ndarray,
    R_W: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    S: Optional[np.ndarray] = None
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Computes the d x d Gram blocks Q_V, Q_W, the cross-block Phi,
    and the 2d x 2d big Gram matrix Q_big = [[Q_W, Phi], [Phi^T, Q_V]].

    Parameters:
        R_V: (d, 2) orthonormal frame in St(2, d)
        R_W: (d, 2) orthonormal frame in St(2, d)
        v: (2,) non-negative Wishart eigenvalues (v1, v2)
        w: (2,) non-negative Wishart eigenvalues (w1, w2)
        S: (2, 2) relative rotation in O(2), default: I_2

    Returns:
        (Q_V, Q_W, Phi, Q_big)
    """
    d = R_V.shape[0]
    if S is None:
        S = np.eye(2)

    # Q_V = R_V diag(v) R_V^T (d x d)
    Q_V = R_V @ np.diag(v) @ R_V.T
    # Q_W = R_W diag(w) R_W^T (d x d)
    Q_W = R_W @ np.diag(w) @ R_W.T

    # Cross block Phi = R_W diag(sqrt(w)) S diag(sqrt(v)) R_V^T (d x d)
    Phi = R_W @ np.diag(np.sqrt(w)) @ S @ np.diag(np.sqrt(v)) @ R_V.T

    # Big Gram matrix Q_big in R^{2d x 2d}
    Q_big = np.block([
        [Q_W, Phi],
        [Phi.T, Q_V]
    ])
    return Q_V, Q_W, Phi, Q_big


def compute_holonomy_invariants(
    Q_V: np.ndarray,
    Q_W: np.ndarray,
    Phi: np.ndarray,
    Omega: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    S: Optional[np.ndarray] = None
) -> dict:
    """
    Computes all Gram/Wishart/Stiefel holonomy invariants from Ydri (2026):
    - Frobenius piece: Tr(Q_W Q_V)
    - Cross traces: Tr(Phi), Tr(Phi^2)
    - Minor sector: (Tr Phi)^2 - Tr(Phi^2) = 2 det(phi)
    - Effective 2x2 overlap: phi = sqrt(w) S sqrt(v) Omega^T
    """
    if S is None:
        S = np.eye(2)

    tr_QW_QV = float(np.trace(Q_W @ Q_V))
    tr_Phi = float(np.trace(Phi))
    Phi_sq = Phi @ Phi
    tr_Phi_sq = float(np.trace(Phi_sq))

    phi = np.diag(np.sqrt(w)) @ S @ np.diag(np.sqrt(v)) @ Omega.T
    det_phi = float(np.linalg.det(phi))

    minor_sector = (tr_Phi)**2 - tr_Phi_sq

    return {
        "tr_QW_QV": tr_QW_QV,
        "tr_Phi": tr_Phi,
        "tr_Phi_sq": tr_Phi_sq,
        "minor_sector": minor_sector,
        "det_phi": det_phi,
        "two_det_phi": 2.0 * det_phi,
        "phi": phi
    }


def verify_annihilation_decoupling(
    P_u: np.ndarray,
    P_w: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    tol: float = 1e-14
) -> dict:
    """
    Verifies HYP-229 on a zero-divisor annihilation 2-frame pair (P_u, P_w):
    - Omega = P_u^T P_w = 0
    - Tr(Q_W Q_V) = 0
    - Phi^2 = 0 (nilpotency)
    - Minor sector = 0
    - rank(Q_big) = 2 with eigenvalues w_i + v_i
    """
    Omega = compute_stiefel_overlap_matrix(P_u, P_w)
    Q_V, Q_W, Phi, Q_big = compute_wishart_gram_blocks(P_u, P_w, v, w)
    invariants = compute_holonomy_invariants(Q_V, Q_W, Phi, Omega, v, w)

    # Check rank of Q_big
    eigvals = np.linalg.eigvalsh(Q_big)
    nonzeros = [e for e in eigvals if e > 1e-10]
    expected_eigs = sorted(list(w + v))

    return {
        "omega_max_abs": float(np.max(np.abs(Omega))),
        "phi_sq_max_abs": float(np.max(np.abs(Phi @ Phi))),
        "tr_QW_QV": invariants["tr_QW_QV"],
        "minor_sector": invariants["minor_sector"],
        "rank_q_big": len(nonzeros),
        "actual_eigenvalues": sorted(nonzeros),
        "expected_eigenvalues": expected_eigs,
        "is_decoupled": (
            np.max(np.abs(Omega)) < tol and
            np.max(np.abs(Phi @ Phi)) < tol and
            abs(invariants["tr_QW_QV"]) < tol and
            abs(invariants["minor_sector"]) < tol and
            len(nonzeros) == 2 and
            np.allclose(sorted(nonzeros), expected_eigs, atol=tol)
        )
    }
