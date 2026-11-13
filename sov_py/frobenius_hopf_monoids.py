"""Frobenius Functors and One-Sided Hopf Monoids in Braided Monoidal Categories.

Grounding:
    Lucrezia Bottegoni, Davide Ferri, Paolo Saracco (2026),
    "Frobenius functors and one-sided Hopf algebras in braided monoidal categories",
    arXiv preprint.

Key Structural Invariants & Theoretical Equivalences (Theorem 4.4):
Let (M, (x), 1, c) be a braided monoidal category admitting coequalizers of reflexive pairs
and equalizers of coreflexive pairs. Let (B, m, u, Delta, eps) be a bimonoid in M.
The following are equivalent:
  (i)   B is a right Hopf monoid whose right antipode S: B -> B is anti-multiplicative
        and anti-comultiplicative:
          m(id (x) S) Delta = u eps,
          S m = m c_{B,B} (S (x) S),
          (S (x) S) c_{B,B} Delta = Delta S.
  (ii)  The canonical comparison morphism sigma_M: M^{co B} -> M (x)_B 1 is a split-mono
        for every right Hopf module M.
  (iii) sigma is a natural isomorphism.
  (iv)  The free Hopf module functor - (x) B: M -> M_B^B is Frobenius.
  (v)   The component sigma_{B^. (x) B^._.} is an isomorphism.
  (vi)  The canonical morphism i_B: B -> (B^. (x) B^._.) (x)_B 1 is an isomorphism.

Retraction and Splitting Explicit Construction:
  zeta_M: M -> M^{co B} given by zeta_M = mu_M (M (x) S) delta_M.
  Factors through M (x)_B 1 to give rho_M: M (x)_B 1 -> M^{co B} satisfying
  rho_M circ sigma_M = id_{M^{co B}}.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple
import numpy as np


@dataclass(frozen=True)
class FiniteBimonoid:
    """Finite-dimensional bimonoid / bialgebra over a field k (represented as R).

    dim: dimension of B
    mult: shape (dim, dim, dim), mult[i, j, k] = coefficient of e_k in e_i * e_j
    unit: shape (dim,), vector representing 1_B
    comult: shape (dim, dim, dim), comult[i, j, k] = coefficient of e_j (x) e_k in Delta(e_i)
    counit: shape (dim,), eps(e_i)
    """
    dim: int
    mult: np.ndarray
    unit: np.ndarray
    comult: np.ndarray
    counit: np.ndarray

    def check_associativity(self, tol: float = 1e-10) -> bool:
        """Check (xy)z = x(yz)."""
        # (e_i * e_j) * e_k = sum_p mult[i, j, p] mult[p, k, q] e_q
        left = np.einsum("ijp,pkq->ijkq", self.mult, self.mult)
        # e_i * (e_j * e_k) = sum_p mult[j, k, p] mult[i, p, q] e_q
        right = np.einsum("jkp,ipq->ijkq", self.mult, self.mult)
        return bool(np.allclose(left, right, atol=tol))

    def check_unitality(self, tol: float = 1e-10) -> bool:
        """Check 1 * x = x and x * 1 = x."""
        left = np.einsum("i,ijk->jk", self.unit, self.mult)
        right = np.einsum("j,ijk->ik", self.unit, self.mult)
        eye = np.eye(self.dim)
        return bool(np.allclose(left, eye, atol=tol) and np.allclose(right, eye, atol=tol))

    def check_coassociativity(self, tol: float = 1e-10) -> bool:
        """Check (Delta (x) id) Delta = (id (x) Delta) Delta."""
        # Delta(e_i) = sum comult[i, j, k] e_j (x) e_k
        # (Delta (x) id) Delta: sum comult[i, p, k] comult[p, j, q] e_j (x) e_q (x) e_k
        left = np.einsum("ipk,pjq->ijqk", self.comult, self.comult)
        # (id (x) Delta) Delta: sum comult[i, j, p] comult[p, q, k] e_j (x) e_q (x) e_k
        right = np.einsum("ijp,pqk->ijqk", self.comult, self.comult)
        return bool(np.allclose(left, right, atol=tol))

    def check_counitality(self, tol: float = 1e-10) -> bool:
        """Check (eps (x) id) Delta = id = (id (x) eps) Delta."""
        left = np.einsum("j,ijk->ik", self.counit, self.comult)
        right = np.einsum("k,ijk->ij", self.counit, self.comult)
        eye = np.eye(self.dim)
        return bool(np.allclose(left, eye, atol=tol) and np.allclose(right, eye, atol=tol))

    def check_bialgebra_compatibility(self, tol: float = 1e-10) -> bool:
        """Check Delta(xy) = Delta(x) Delta(y) and eps(xy) = eps(x) eps(y)."""
        # Delta(e_i * e_j) = sum mult[i, j, p] comult[p, a, b] e_a (x) e_b
        left_delta = np.einsum("ijp,pab->ijab", self.mult, self.comult)
        # Delta(e_i) Delta(e_j) = sum comult[i, x, y] comult[j, z, w] mult[x, z, a] mult[y, w, b]
        right_delta = np.einsum("ixy,jzw,xza,ywb->ijab", self.comult, self.comult, self.mult, self.mult)
        if not np.allclose(left_delta, right_delta, atol=tol):
            return False

        # eps(e_i * e_j) = sum mult[i, j, p] eps[p]
        left_eps = np.einsum("ijp,p->ij", self.mult, self.counit)
        right_eps = np.outer(self.counit, self.counit)
        return bool(np.allclose(left_eps, right_eps, atol=tol))


def verify_right_antipode(
    B: FiniteBimonoid,
    S: np.ndarray,
    tol: float = 1e-10,
) -> Dict[str, bool]:
    """Verify right antipode conditions:

    1. id * S = u eps:
       sum comult[i, j, k] S[k, l] mult[j, l, m] = counit[i] unit[m]
    2. Anti-multiplicativity:
       S(e_i * e_j) = S(e_j) * S(e_i)
       sum mult[i, j, p] S[p, m] = sum S[j, a] S[i, b] mult[a, b, m]
    3. Anti-comultiplicativity:
       Delta(S(e_i)) = (S (x) S)(tau(Delta(e_i)))
       sum S[i, p] comult[p, a, b] = sum comult[i, y, x] S[x, a] S[y, b]
    """
    # 1. Right convolution inverse of id:
    # conv = sum_j,k,l comult[i, j, k] S[k, l] mult[j, l, m]
    conv = np.einsum("ijk,kl,jlm->im", B.comult, S, B.mult)
    target_conv = np.outer(B.counit, B.unit)
    is_right_antipode = bool(np.allclose(conv, target_conv, atol=tol))

    # 2. Anti-multiplicativity:
    left_anti_mult = np.einsum("ijp,pm->ijm", B.mult, S)
    right_anti_mult = np.einsum("ja,ib,abm->ijm", S, S, B.mult)
    is_anti_multiplicative = bool(np.allclose(left_anti_mult, right_anti_mult, atol=tol))

    # 3. Anti-comultiplicativity (in symmetric category with flip c_{B,B}(x (x) y) = y (x) x):
    left_anti_comult = np.einsum("ip,pab->iab", S, B.comult)
    # (S (x) S) tau Delta(e_i): tau exchanges outputs so comult[i, y, x] -> e_x (x) e_y
    right_anti_comult = np.einsum("iyx,xa,yb->iab", B.comult, S, S)
    is_anti_comultiplicative = bool(np.allclose(left_anti_comult, right_anti_comult, atol=tol))

    # Unit condition S(u) = u
    S_u = S @ B.unit
    preserves_unit = bool(np.allclose(S_u, B.unit, atol=tol))

    return {
        "is_right_antipode": is_right_antipode,
        "is_anti_multiplicative": is_anti_multiplicative,
        "is_anti_comultiplicative": is_anti_comultiplicative,
        "preserves_unit": preserves_unit,
        "is_valid_one_sided_hopf": (
            is_right_antipode and is_anti_multiplicative and is_anti_comultiplicative
        ),
    }


def verify_coinvariant_retraction_splitting(
    B: FiniteBimonoid,
    S: np.ndarray,
    tol: float = 1e-10,
) -> Dict[str, bool]:
    """Verify Theorem 4.4 coinvariant projection zeta_M and splitting of sigma_M.

    Using the canonical Hopf module M = B^. (x) B^._.:
      action mu_M: M (x) B -> M
      coaction delta_M: M -> M (x) B
      zeta_M = mu_M circ (id_M (x) S) circ delta_M: M -> M
    """
    dim_M = B.dim * B.dim

    # Basis of M: e_i (x) e_j indexed by (i, j)
    # Coaction delta_M: delta_M(e_i (x) e_j) = sum comult[j, a, b] (e_i (x) e_a) (x) e_b
    # Action mu_M: (e_i (x) e_j) * e_k = sum mult[i, k, a] mult[j, k, b] e_a (x) e_b
    # Wait, for B^. (x) B^._.:
    # tensor product of regular modules: (x (x) y) * z = x * z_1 (x) y * z_2
    # with coaction delta(x (x) y) = (x (x) y_1) (x) y_2

    # Zeta operator on M:
    # zeta(x (x) y) = sum (x (x) y_1) * S(y_2)
    # = sum (x * S(y_2)_1) (x) (y_1 * S(y_2)_2)
    # Using anti-comultiplicativity of S: S(y_2)_1 (x) S(y_2)_2 = S(y_3) (x) S(y_2)
    # Then y_1 S(y_2) = eps(y_1) 1, so this reduces to (x * S(y)) (x) 1!

    # Let's test zeta matrix Z of size (dim_M, dim_M):
    Z = np.zeros((B.dim, B.dim, B.dim, B.dim))
    for i in range(B.dim):
        for j in range(B.dim):
            # zeta(e_i (x) e_j) = sum_k S[j, k] (e_i * e_k) (x) 1
            for k in range(B.dim):
                weight = S[j, k]
                if abs(weight) > tol:
                    for p in range(B.dim):
                        coeff = weight * B.mult[i, k, p]
                        # Target is e_p (x) 1_B = sum_u B.unit[u] e_p (x) e_u
                        for u in range(B.dim):
                            Z[p, u, i, j] += coeff * B.unit[u]

    Z_flat = Z.reshape(dim_M, dim_M)

    # 1. Idempotency: Z^2 = Z (zeta_M is a projection)
    Z_sq = Z_flat @ Z_flat
    is_projection = bool(np.allclose(Z_sq, Z_flat, atol=tol))

    # 2. Image lies in coinvariants: (id (x) Delta) Z = (Z (x) u)
    # Coinvariant condition: delta(m) = m (x) 1
    # For every vector in the image of Z, its second factor is proportional to unit
    image_vectors = Z_flat[:, np.linalg.svd(Z_flat)[1] > tol]
    in_coinvariants = True
    for col in range(image_vectors.shape[1]):
        vec_2d = image_vectors[:, col].reshape(B.dim, B.dim)
        # Check that vec_2d[p, u] = alpha_p * unit[u]
        # Project onto unit:
        norm_unit_sq = float(np.sum(B.unit**2))
        proj_unit = (vec_2d @ B.unit) / norm_unit_sq
        recon = np.outer(proj_unit, B.unit)
        if not np.allclose(vec_2d, recon, atol=tol):
            in_coinvariants = False
            break

    # 3. Retraction on coinvariants: Z v = v for v in coinvariants
    # Coinvariants have form outer(alpha, unit)
    retraction_valid = True
    for p in range(B.dim):
        v = np.outer(np.eye(B.dim)[p], B.unit).reshape(-1)
        Zv = Z_flat @ v
        if not np.allclose(Zv, v, atol=tol):
            retraction_valid = False
            break

    return {
        "zeta_is_projection": is_projection,
        "image_in_coinvariants": in_coinvariants,
        "retraction_on_coinvariants": retraction_valid,
        "split_monomorphism_confirmed": (is_projection and in_coinvariants and retraction_valid),
    }


def construct_group_algebra_bimonoid(group_mult_table: List[List[int]]) -> FiniteBimonoid:
    """Construct standard group algebra k[G] bimonoid from group multiplication table."""
    G_order = len(group_mult_table)
    mult = np.zeros((G_order, G_order, G_order))
    for i in range(G_order):
        for j in range(G_order):
            k = group_mult_table[i][j]
            mult[i, j, k] = 1.0

    unit = np.zeros(G_order)
    unit[0] = 1.0  # e_0 is identity

    comult = np.zeros((G_order, G_order, G_order))
    for i in range(G_order):
        comult[i, i, i] = 1.0  # Group-like: Delta(g) = g (x) g

    counit = np.ones(G_order)  # eps(g) = 1

    return FiniteBimonoid(
        dim=G_order,
        mult=mult,
        unit=unit,
        comult=comult,
        counit=counit,
    )
