"""
Exact Algebraic 2-Frame Stiefel Skewon Update & G2 Quaternionic Lie Generation Invariants.

Grounds frontier literature:
1. Mikhail Solonko, Alexander Molozhavenko, Maxim Rakhuba (Aug 2026),
   "Muon on the Stiefel Manifold Admits an Exact Closed-Form Update", arXiv:2608.06218v1.
2. Santiago Pineda Montoya, Johan H. Rúa Muñoz, Borut Jurčič Zlobec (Sep 2026),
   "Quaternionic Reflections and Lie Generation in G2", arXiv:2609.15497v1.

Formalized in Lean 4: formal/TowerStiefelSkewonG2.lean (HYP-227).
"""

from typing import Tuple, Callable, Optional
import numpy as np


def algebraic_msign_4x4(Omega: np.ndarray, tol: float = 1e-14) -> np.ndarray:
    """
    Computes the exact matrix sign msign(Omega) = -U V^T of a 4x4 skew-symmetric matrix Omega in so(4)
    using the closed-form algebraic degree-2 characteristic polynomial with ZERO iterations.

    Parameters:
        Omega: (4, 4) real skew-symmetric matrix (Omega^T = -Omega).
        tol: numerical tolerance for zero singular values.

    Returns:
        (4, 4) skew-symmetric matrix sign with spectral norm <= 1.0.
    """
    assert Omega.shape == (4, 4), f"Expected 4x4 matrix, got {Omega.shape}"
    # Symmetrize skew part to eliminate any floating-point drift
    Omega_skew = 0.5 * (Omega - Omega.T)

    # K = -Omega^2 is symmetric positive semi-definite
    K = - Omega_skew @ Omega_skew
    s = 0.5 * np.trace(K)  # sigma1^2 + sigma2^2

    # Pfaffian of 4x4 skew matrix:
    # Pf(Omega) = a*f - b*e + c*d
    pf = (Omega_skew[0, 1] * Omega_skew[2, 3]
          - Omega_skew[0, 2] * Omega_skew[1, 3]
          + Omega_skew[0, 3] * Omega_skew[1, 2])
    d = pf**2  # sigma1^2 * sigma2^2

    disc = max(0.0, s**2 - 4.0 * d)
    sig1_sq = (s + np.sqrt(disc)) / 2.0
    sig2_sq = (s - np.sqrt(disc)) / 2.0
    sig1 = np.sqrt(max(0.0, sig1_sq))
    sig2 = np.sqrt(max(0.0, sig2_sq))

    if sig1 < tol:
        # Trivial zero operator
        return np.zeros((4, 4), dtype=Omega.dtype)

    if sig2 < tol:
        # Rank-2 case: only one pair of non-zero eigenvalues +/- i sig1
        # msign(Omega) = Omega / sig1
        Y = Omega_skew / sig1
    else:
        # Full rank-4 case:
        # Cayley-Hamilton inverse square root:
        # c1 * sig1^2 + c0 = 1/sig1
        # c1 * sig2^2 + c0 = 1/sig2
        c1 = -1.0 / (sig1 * sig2 * (sig1 + sig2))
        c0 = (sig1**2 + sig1 * sig2 + sig2**2) / (sig1 * sig2 * (sig1 + sig2))
        K_inv_half = c1 * K + c0 * np.eye(4)
        Y = Omega_skew @ K_inv_half

    # Symmetrize skew part
    return 0.5 * (Y - Y.T)


def skewon_stiefel_2frame(X: np.ndarray, M: np.ndarray, tol: float = 1e-14) -> np.ndarray:
    """
    Computes the exact closed-form Stiefel Muon update B* in T_X St(n, 2)
    minimizing <M, B> subject to ||B||_2 <= 1.

    Parameters:
        X: (n, 2) orthonormal 2-frame (X^T X = I_2).
        M: (n, 2) momentum / gradient direction matrix.
        tol: numerical tolerance.

    Returns:
        B*: (n, 2) optimal tangent matrix in T_X St(n, 2) with ||B*||_2 = 1 (if M != 0).
    """
    n, p = X.shape
    assert p == 2, f"Expected 2-frame (p=2), got p={p}"

    # 1. Thin QR of [-X, M] in R^{n x 4}
    XM = np.hstack([-X, M])
    Q, R = np.linalg.qr(XM)  # Q is (n, 4), R is (4, 4)

    # 2. Project to so(4): Omega_tilde = 0.5 * R @ J @ R^T
    J = np.array([
        [0, 0, 1, 0],
        [0, 0, 0, 1],
        [-1, 0, 0, 0],
        [0, -1, 0, 0]
    ], dtype=float)

    Omega_tilde = 0.5 * R @ J @ R.T
    Omega_tilde = 0.5 * (Omega_tilde - Omega_tilde.T)

    # 3. Exact algebraic 4x4 matrix sign
    Y_tilde = - algebraic_msign_4x4(Omega_tilde, tol=tol)

    # 4. Map back to Stiefel tangent space: B* = Q @ (Y_tilde @ (Q^T X))
    B_star = Q @ (Y_tilde @ (Q.T @ X))
    return B_star


def lie_generation_h8(A_plus: np.ndarray, A_minus: np.ndarray,
                      ip_fn: Optional[Callable[[np.ndarray, np.ndarray], float]] = None
                      ) -> Tuple[float, float, float]:
    """
    Computes the exact degree-8 Lie generation invariant H8(sigma, Z) from
    Montoya, Rua Munoz, Zlobec (2026), Theorem 6.4 and Lemma 6.3.

    H8 = det Gram(A_-, C_+) + det Gram(A_+, C_-)
       = ||A_-||^2 ||C_+||^2 + ||A_+||^2 ||C_-||^2 - 2 ||C||^4 >= 0.

    Vanishes (H8 = 0) if and only if dim Lie{Z, sigma Z} <= 3 (abelian or su(2)).

    Parameters:
        A_plus: even component (sigma A_+ = A_+).
        A_minus: odd component (sigma A_- = -A_-).
        ip_fn: invariant inner product on the Lie algebra (default: -0.5 * tr(X @ Y)).

    Returns:
        (H8, gram1, gram2)
    """
    if ip_fn is None:
        def ip_fn(X, Y):
            return -0.5 * float(np.trace(X @ Y))

    # Commutators:
    # C = [A_+, A_-] (odd)
    C = A_plus @ A_minus - A_minus @ A_plus
    # C_+ = [A_+, C] (odd)
    C_plus = A_plus @ C - C @ A_plus
    # C_- = [A_-, C] (even)
    C_minus = A_minus @ C - C @ A_minus

    norm_sq_A_minus = ip_fn(A_minus, A_minus)
    norm_sq_A_plus = ip_fn(A_plus, A_plus)
    norm_sq_C = ip_fn(C, C)
    norm_sq_C_plus = ip_fn(C_plus, C_plus)
    norm_sq_C_minus = ip_fn(C_minus, C_minus)

    ip_C_plus_A_minus = ip_fn(C_plus, A_minus)
    ip_C_minus_A_plus = ip_fn(C_minus, A_plus)

    # Gram determinants:
    gram1 = max(0.0, norm_sq_A_minus * norm_sq_C_plus - ip_C_plus_A_minus**2)
    gram2 = max(0.0, norm_sq_A_plus * norm_sq_C_minus - ip_C_minus_A_plus**2)

    H8 = gram1 + gram2
    return float(H8), float(gram1), float(gram2)


def stiefel_geodesic_retraction_2frame(X: np.ndarray, B: np.ndarray, t: float = 1.0) -> np.ndarray:
    """
    Computes the exact closed-form Stiefel retraction for 2-frames:
    R_X(t B) = (X + t B) (I_2 + t^2 B^T B)^{-1/2}.

    Preserves exact orthonormality X_new^T X_new = I_2 in O(n) operations.
    """
    XtB = X + t * B
    M2 = np.eye(2) + (t**2) * (B.T @ B)
    # Exact 2x2 inverse square root:
    # For a 2x2 symmetric positive definite matrix M2:
    w, V = np.linalg.eigh(M2)
    inv_sqrt_w = 1.0 / np.sqrt(np.maximum(w, 1e-14))
    M2_inv_sqrt = V @ np.diag(inv_sqrt_w) @ V.T
    return XtB @ M2_inv_sqrt


def newton_schulz_1step_retraction(X: np.ndarray, B: np.ndarray, eta: float = 1.0) -> np.ndarray:
    """
    Computes the 1-step Newton-Schulz retraction on St(n, p) from Su & Huang (2026):
    Psi(Z) = 0.5 * Z * (3 I_p - Z^T Z) where Z = X + eta * B.

    Exhibits 4th-order orthogonality error:
    Psi(Z)^T Psi(Z) - I_p = -0.75 * u^2 + 0.25 * u^3 where u = eta^2 * B^T B.
    """
    Z = X + eta * B
    p = X.shape[1]
    ZT_Z = Z.T @ Z
    return 0.5 * Z @ (3.0 * np.eye(p) - ZT_Z)


def cayley_inverse_retraction(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """
    Computes the exact closed-form inverse Cayley retraction (Riemannian logarithm)
    from Jensen & Zimmermann (2026), eq (2.8):
    R_X^{-1}(Y) = 2 X F(Y)^T + 2 Y F(Y) - 2 X where F(Y) = (I_p + X^T Y)^{-1}.

    Maps Y in St(n, p) to an exact tangent vector xi in T_X St(n, p).
    For mutually orthogonal frames X^T Y = 0, collapses to exact scalar doubling xi = 2 Y.
    """
    p = X.shape[1]
    F_Y = np.linalg.inv(np.eye(p) + X.T @ Y)
    xi = 2.0 * X @ F_Y.T + 2.0 * Y @ F_Y - 2.0 * X
    return xi


def cayley_forward_retraction(X: np.ndarray, xi: np.ndarray) -> np.ndarray:
    """
    Computes the exact closed-form forward Cayley retraction from Jensen & Zimmermann (2026):
    R_X(xi) = -X + (X_perp B + 2 X) (0.25 B^T B - 0.5 A + I_p)^{-1}
    where A = X^T xi in skew(p) and X_perp B = xi - X A.

    Maps tangent vector xi in T_X St(n, p) to an orthonormal frame in St(n, p).
    Satisfies R_X(R_X^{-1}(Y)) = Y identically.
    """
    p = X.shape[1]
    A = X.T @ xi
    A_skew = 0.5 * (A - A.T)
    X_perp_B = xi - X @ A_skew
    BT_B = X_perp_B.T @ X_perp_B

    M = 0.25 * BT_B - 0.5 * A_skew + np.eye(p)
    M_inv = np.linalg.inv(M)
    return -X + (X_perp_B + 2.0 * X) @ M_inv
