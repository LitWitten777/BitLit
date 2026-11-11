import Mathlib
import RequestProject.JensenHolonomy
import RequestProject.HolonomyCertificate.Full.AlgebraicLaurentCertificateAssembly

/-!
# Final Assembly: Local Holonomy Certificate (Periodic-Log Form)
-/

open Complex Finset MeasureTheory Polynomial
open scoped BigOperators Real

set_option maxHeartbeats 800000

noncomputable section

/-- Evaluate a bivariate Laurent polynomial given by coefficients `coeffs`
    and a Laurent shift `M`. -/
def evalBiLaurentPoly
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (M : ℤ) (t x : ℝ) : ℂ :=
  circleParam x ^ (-M) *
    ∑ j : Fin (d + 1), evalLaurentCircle (coeffs j) t * (circleParam x) ^ (j : ℕ)

/-
The bivariate Laurent polynomial, when the z-polynomial factors,
    equals the Jensen-factored form.
-/
lemma evalBiLaurentPoly_eq_factored
    {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (M : ℤ) (t : ℝ) (r : Fin d → ℂ)
    (ad_val : ℂ)
    (hfact : Polynomial.C ad_val * ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
        ∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (x : ℝ) :
    evalBiLaurentPoly coeffs M t x =
      circleParam x ^ (-M) * ad_val * ∏ i : Fin d, (circleParam x - r i) := by
  unfold evalBiLaurentPoly;
  convert congr_arg ( fun p : Polynomial ℂ => circleParam x ^ ( -M ) * p.eval ( circleParam x ) ) hfact.symm using 1 <;> norm_num [ Polynomial.eval_finset_sum, Polynomial.eval_prod ] ; ring

/-
**Local holonomy-certificate theorem (periodic-log form).**
-/
theorem local_holonomy_certificate_full_periodic_log_form
    {a b : ℝ} (hab : a < b)
    {d : ℕ} (m : ℕ) (M : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin d → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        M = ↑((Finset.univ.filter (fun i : Fin d => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = m ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (d + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (ell : ℝ → ℝ → ℂ)
    (hell : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      IsPeriodicLog (ell t) (evalBiLaurentPoly coeffs M t))
    (J : ℝ → ℂ)
    (hJ : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell t x)) :
    ∃ a' b' : ℝ,
      a < a' ∧ a' < b' ∧ b' < b ∧
      ∃ N : ℕ,
      ∃ A : Fin (N + 1) → LaurentPolynomial ℂ,
        (∃ n : Fin (N + 1), A n ≠ 0) ∧
        ∀ t ∈ Set.Ioo a' b',
          ∑ n : Fin (N + 1),
            evalLaurentCircle (A n) t * (J t) ^ (n : ℕ) = 0 := by
  convert algebraic_laurent_certificate_from_jensen_identity hab d m ad had coeffs h_ad_coeff J _;
  intro t ht h_eval
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hroots t ht h_eval
  use r, Finset.univ.filter (fun i => 1 < ‖r i‖);
  have := complex_jensen_holonomy_product ( show ∀ x : ℝ, evalBiLaurentPoly coeffs M t x = circleParam x ^ ( -M ) * evalLaurentCircle ad t * ∏ i : Fin d, ( circleParam x - r i ) from ?_ ) ?_ ?_ ?_ ( hell t ht h_eval );
  · exact ⟨ hr3, hr4, hJ t ht h_eval ▸ this ⟩;
  · convert evalBiLaurentPoly_eq_factored coeffs M t r ( evalLaurentCircle ad t ) hr4 using 1;
  · assumption;
  · assumption;
  · exact hr2

end