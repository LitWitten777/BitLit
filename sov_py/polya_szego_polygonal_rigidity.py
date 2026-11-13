"""
polya_szego_polygonal_rigidity.py

Computational verification of the Polya-Szego conjecture for convex polygons
with many sides (Cheng, Gui, Hu, Li 2026).

Key Mathematical Objects:
1. N-admissible atomic probability measures:
   mu = sum_{l=1}^M w_l delta_{theta_l},  M <= N,  sum w_l = 1,  w_l > 0.
   Fourier coefficients: hat{mu}(k) = sum_{l=1}^M w_l e^{-i k theta_l}.

2. Regular root measure:
   sigma_N = (1/N) sum_{j=0}^{N-1} delta_{2 pi j / N}.
   hat{sigma}_N(k) = 1 if N | k else 0.

3. Inverse-power atomic energy and defect:
   E_{at, p}(mu) = sum_{k=2}^infty |hat{mu}(k)|^2 / k^p  (assuming hat{mu}(1) = 0).
   For sigma_N: E_{at, p}(sigma_N) = zeta(p) / N^p.
   Defect: d_{p, N}(mu) = E_{at, p}(mu) - zeta(p) / N^p >= 0.

4. Poisson energy:
   P_{at, q}(mu) = sum_{k=1}^infty q^k |hat{mu}(k)|^2.
   For sigma_N: P_{at, q}(sigma_N) = q^N / (1 - q^N).
   Defect: G_N(q; mu) = P_{at, q}(mu) - q^N / (1 - q^N) >= 0.

5. Bessel-corrected disk Hessian coefficients via backward continued fraction:
   j = j_{0,1} approx 2.404825557695773...
   r_k = j^2 / (2(k + 1) - r_{k+1}), with 0 < r_k < 6/(k + 1).
   d_k = r_k / k^4
   beta_k = 1 + j * J'_k(j) / J_k(j) = k + 1 - r_k
   b_k = beta_k / k^4 = 1/k^3 + 1/k^4 - d_k.

6. Discrete Rigidity Certificate (Lemma 4.2):
   G_N(q; mu) >= A_N(q) * (sum_l w_l^2 - 1/N)
   where A_N(q) = (q^{-1} - q) N^2 q^N / (2 (1 - q^N)^2).
"""

from __future__ import annotations
import math
import cmath
from typing import List, Tuple, Dict, Any
import scipy.special as sp


J01_ZERO = 2.40482555769577276862169185257745  # first positive zero of J_0


def regular_root_measure(N: int) -> Tuple[List[float], List[float]]:
    """Return weights and angles for the regular N-gon."""
    weights = [1.0 / N] * N
    angles = [2.0 * math.pi * j / N for j in range(N)]
    return weights, angles


def atomic_fourier_coefficients(
    weights: List[float], angles: List[float], max_k: int
) -> Dict[int, complex]:
    """Compute hat{mu}(k) = sum_l w_l e^{-i k theta_l} for k = 0, ..., max_k."""
    coeffs = {}
    for k in range(max_k + 1):
        c = sum(w * cmath.exp(-1j * k * th) for w, th in zip(weights, angles))
        coeffs[k] = c
    return coeffs


def regular_fourier_coefficient(k: int, N: int) -> complex:
    """Exact Fourier coefficient for regular N-gon: 1 if N | k else 0."""
    return 1.0 if (k % N == 0) else 0.0


def inverse_power_energy(
    weights: List[float], angles: List[float], p: int, max_k: int = 5000, start_k: int = 2
) -> float:
    """Compute E_{at, p}(mu) = sum_{k=start_k}^max_k |hat{mu}(k)|^2 / k^p."""
    coeffs = atomic_fourier_coefficients(weights, angles, max_k)
    energy = sum(abs(coeffs[k]) ** 2 / (k**p) for k in range(start_k, max_k + 1))
    return energy


def regular_inverse_power_energy_exact(N: int, p: int) -> float:
    """Exact value: sum_{m=1}^infty 1 / (mN)^p = zeta(p) / N^p."""
    return float(sp.zeta(p) / (N**p))


def inverse_power_defect(
    weights: List[float], angles: List[float], N: int, p: int = 3, max_k: int = 5000
) -> float:
    """Compute d_{p, N}(mu) = E_{at, p}(mu) - zeta(p) / N^p."""
    computed = inverse_power_energy(weights, angles, p=p, max_k=max_k, start_k=2)
    exact_regular = regular_inverse_power_energy_exact(N, p)
    return computed - exact_regular


def poisson_energy(weights: List[float], angles: List[float], q: float, max_k: int = 500) -> float:
    """Compute P_{at, q}(mu) = sum_{k=1}^max_k q^k |hat{mu}(k)|^2."""
    coeffs = atomic_fourier_coefficients(weights, angles, max_k)
    return sum((q**k) * (abs(coeffs[k]) ** 2) for k in range(1, max_k + 1))


def regular_poisson_energy_exact(q: float, N: int) -> float:
    """Exact regular value: sum_{m=1}^infty q^{mN} = q^N / (1 - q^N)."""
    return (q**N) / (1.0 - (q**N))


def poisson_defect(weights: List[float], angles: List[float], N: int, q: float) -> float:
    """Compute G_N(q; mu) = P_{at, q}(mu) - q^N / (1 - q^N)."""
    return poisson_energy(weights, angles, q) - regular_poisson_energy_exact(q, N)


def compute_bessel_r_table(max_k: int, j: float = J01_ZERO) -> List[float]:
    """Compute r_k = j * J_{k+1}(j) / J_k(j) stably via backward continued fraction

    r_k = j^2 / (2(k + 1) - r_{k+1}).
    """
    buffer_len = max_k + 50
    r = [0.0] * (buffer_len + 1)
    j2 = j * j
    for k in range(buffer_len - 1, 0, -1):
        r[k] = j2 / (2.0 * (k + 1) - r[k + 1])
    return r[: max_k + 1]


def bessel_beta_k(k: int, r_table: List[float] | None = None, j: float = J01_ZERO) -> float:
    """Compute beta_k = k + 1 - r_k."""
    if r_table is not None and k < len(r_table):
        rk = r_table[k]
    else:
        r_tab = compute_bessel_r_table(k, j)
        rk = r_tab[k]
    return float(k + 1.0 - rk)


def bessel_b_k(k: int, r_table: List[float] | None = None, j: float = J01_ZERO) -> float:
    """Compute b_k = beta_k / k^4."""
    return float(bessel_beta_k(k, r_table, j) / (k**4))


def bessel_d_k(k: int, r_table: List[float] | None = None, j: float = J01_ZERO) -> float:
    """Compute d_k = r_k / k^4."""
    if r_table is not None and k < len(r_table):
        rk = r_table[k]
    else:
        r_tab = compute_bessel_r_table(k, j)
        rk = r_tab[k]
    return float(rk / (k**4))


def bessel_energy(
    weights: List[float], angles: List[float], max_k: int = 1000, j: float = J01_ZERO
) -> float:
    """Compute E_{at, b}(mu) = sum_{k=2}^max_k b_k |hat{mu}(k)|^2."""
    r_tab = compute_bessel_r_table(max_k, j)
    coeffs = atomic_fourier_coefficients(weights, angles, max_k)
    return sum(bessel_b_k(k, r_tab, j) * (abs(coeffs[k]) ** 2) for k in range(2, max_k + 1))


def regular_bessel_energy_exact(N: int, max_m: int = 200, j: float = J01_ZERO) -> float:
    """Compute E_{at, b}(sigma_N) = sum_{m=1}^max_m b_{mN}."""
    max_k = max_m * N
    r_tab = compute_bessel_r_table(max_k, j)
    return sum(bessel_b_k(m * N, r_tab, j) for m in range(1, max_m + 1))


def bessel_defect(
    weights: List[float], angles: List[float], N: int, max_k: int = 2000, j: float = J01_ZERO
) -> float:
    """Compute d_{B, N}(mu) = E_{at, b}(mu) - E_{at, b}(sigma_N)."""
    mu_energy = bessel_energy(weights, angles, max_k, j)
    sigma_energy = regular_bessel_energy_exact(N, max_k // N, j)
    return mu_energy - sigma_energy


def fejer_poisson_kernel_F(theta: float, N: int) -> float:
    """F_N(theta) = (sin(N theta / 2) / sin(theta / 2))^2 with F_N(0) = N^2."""
    th = theta % (2.0 * math.pi)
    if abs(th) < 1e-12 or abs(th - 2.0 * math.pi) < 1e-12:
        return float(N**2)
    s_half = math.sin(th / 2.0)
    if abs(s_half) < 1e-15:
        return float(N**2)
    s_Nhalf = math.sin(N * th / 2.0)
    return float((s_Nhalf / s_half) ** 2)


def fejer_poisson_A_N(q: float, N: int) -> float:
    """Compute A_N(q) = ((q^{-1} - q) / 2) * d
    where d = N^2 q^N / (1 - q^N)^2.
    """
    d = (N**2) * (q**N) / ((1.0 - q**N) ** 2)
    return float(0.5 * (1.0 / q - q) * d)


def fejer_poisson_c_k_coeffs(q: float, N: int) -> List[float]:
    """Compute the Fourier coefficients c_k of the interpolation polynomial h(u(theta))

    from Lemma 4.2 for 1 <= k <= N - 2.
    Using formula (4.6): A_{N,k}(q) = (q^{-1} - q) c_k,
    where A_{N,k}(q) / q^k = (1 - q^{2n} - n (q^{-1} - q) q^n) / (1 - q^N)^2
    with n = N - k.
    """
    coeffs = [0.0] * (N - 1)
    denom = (1.0 - q**N) ** 2
    factor = 1.0 / (1.0 / q - q)
    for k in range(1, N - 1):
        n = N - k
        # A_{N,k}
        num = 1.0 - (q ** (2 * n)) - n * (1.0 / q - q) * (q**n)
        A_k = (q**k) * num / denom
        coeffs[k] = A_k * factor
    return coeffs


def principal_cubic_tensor_T_N(
    weights: List[float], angles: List[float], max_sum: int = 200
) -> complex:
    """Compute T_N(mu) = sum_{a,b >= 1, a+b <= max_sum} hat{mu}(a) hat{mu}(b) hat{mu}(a+b) / (a b (a+b)^2)."""
    coeffs = atomic_fourier_coefficients(weights, angles, max_sum)
    total = 0.0 + 0.0j
    for a in range(1, max_sum):
        for b in range(1, max_sum - a + 1):
            s = a + b
            term = (coeffs[a] * coeffs[b] * coeffs[s]) / (a * b * (s**2))
            total += term
    return total


def regular_cubic_tensor_exact(N: int, max_m: int = 50) -> float:
    """Exact value of T_N(sigma_N) = (1/N^4) sum_{m1, m2 >= 1} 1 / (m1 m2 (m1+m2)^2)

    Note sum_{m1,m2 >= 1} 1 / (m1 m2 (m1+m2)^2) = zeta(4) / 2 = pi^4 / 180.
    """
    return float(sp.zeta(4) / (2.0 * (N**4)))


def verify_weight_rigidity_bound(
    weights: List[float], d3_N: float, N: int
) -> Tuple[bool, float, float]:
    """Verify inequality (4.9): sum_{l=1}^N (w_l - 1/N)^2 <= 2 e^4 N^2 d_{3,N}."""
    lhs = sum((w - 1.0 / N) ** 2 for w in weights)
    rhs = 2.0 * (math.e**4) * (N**2) * max(0.0, d3_N)
    return lhs <= rhs + 1e-12, lhs, rhs


def verify_discrete_rigidity_master(
    N: int = 6, delta_angle: float = 0.05, delta_weight: float = 0.02
) -> Dict[str, Any]:
    """Perform master verification of discrete rigidity invariants."""
    w_reg, th_reg = regular_root_measure(N)

    # 1. Regular checks
    d3_reg = inverse_power_defect(w_reg, th_reg, N, p=3, max_k=3000)
    g_reg = poisson_defect(w_reg, th_reg, N, q=0.6)
    dB_reg = bessel_defect(w_reg, th_reg, N, max_k=3000)
    TN_reg = principal_cubic_tensor_T_N(w_reg, th_reg, max_sum=150)
    TN_exact = regular_cubic_tensor_exact(N)

    # 2. Perturbed check
    w_pert = list(w_reg)
    w_pert[0] += delta_weight
    w_pert[1] -= delta_weight

    th_pert = list(th_reg)
    th_pert[0] += delta_angle
    th_pert[1] -= delta_angle

    d3_pert = inverse_power_defect(w_pert, th_pert, N, p=3, max_k=3000)
    g_pert = poisson_defect(w_pert, th_pert, N, q=0.6)
    dB_pert = bessel_defect(w_pert, th_pert, N, max_k=3000)
    TN_pert = principal_cubic_tensor_T_N(w_pert, th_pert, max_sum=150)

    q = 0.6
    A_N_val = fejer_poisson_A_N(q, N)
    weight_var = sum(w**2 for w in w_pert) - (1.0 / N)
    cert_lb = A_N_val * weight_var

    return {
        "N": N,
        "d3_reg": d3_reg,
        "g_reg": g_reg,
        "dB_reg": dB_reg,
        "TN_reg_real": TN_reg.real,
        "TN_exact": TN_exact,
        "TN_reg_matches_exact": abs(TN_reg.real - TN_exact) < 1e-4 * TN_exact,
        "d3_pert": d3_pert,
        "g_pert": g_pert,
        "dB_pert": dB_pert,
        "cert_lb": cert_lb,
        "g_pert_ge_cert_lb": g_pert >= cert_lb - 1e-9,
        "d3_pert_positive": d3_pert > 0,
        "dB_pert_positive": dB_pert > 0,
    }
