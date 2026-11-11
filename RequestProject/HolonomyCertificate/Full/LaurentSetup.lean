import Mathlib

/-!
# Laurent polynomial setup for holonomy certificates

Basic definitions for evaluating Laurent polynomials on the unit circle
and related infrastructure.
-/

open scoped BigOperators
open Polynomial

noncomputable section

/-- Evaluate a Laurent polynomial at exp(2πit) on the unit circle. -/
def evalLaurentCircle (f : LaurentPolynomial ℂ) (t : ℝ) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ)
    (Units.mk0 (Complex.exp (2 * ↑Real.pi * t * Complex.I))
      (Complex.exp_ne_zero _)) f

/-- The elementary symmetric value of a root family at index k. -/
def elementarySymmetricValue {d : ℕ} (r : Fin d → ℂ) (k : ℕ) : ℂ :=
  Multiset.esymm (Finset.univ.val.map r) k

/-- The subset-product polynomial:
  ∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
    (X - C (ad * ∏ i ∈ I, (-r i))) -/
def subsetProductPoly (d m : ℕ) (ad : ℂ) (r : Fin d → ℂ) : Polynomial ℂ :=
  ∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
    (X - C (ad * ∏ i ∈ I, (-r i)))

/-- General version of subsetProductPoly over any field -/
def subsetProductPolyGen {K : Type*} [Field K] (d m : ℕ) (ad : K) (r : Fin d → K) :
    Polynomial K :=
  ∏ I ∈ (Finset.univ : Finset (Fin d)).powersetCard m,
    (X - C (ad * ∏ i ∈ I, (-r i)))

end
