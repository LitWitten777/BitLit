import Mathlib
import RequestProject.JensenHolonomy
import RequestProject.FinalAssembly

/-!
# Winding-Number Wrapper for the Local Holonomy Certificate
-/

open Complex Finset MeasureTheory Polynomial
open scoped BigOperators Real

set_option maxHeartbeats 1600000

noncomputable section

-- ============================================================================
-- Part 1: Winding number zero implies periodic logarithm
-- ============================================================================

/-- A continuous nonvanishing 1-periodic function `g` has **winding number zero**
    when it admits a continuous logarithm `L` on ℝ satisfying `L 1 = L 0`. -/
def HasWindingNumberZero (g : ℝ → ℂ) : Prop :=
  ∃ L : ℝ → ℂ, Continuous L ∧ (∀ x, Complex.exp (L x) = g x) ∧ L 1 = L 0

theorem periodic_log_of_winding_number_zero
    (g : ℝ → ℂ)
    (_hg_cont : Continuous g)
    (hg_per : Function.Periodic g 1)
    (hg_ne : ∀ x, g x ≠ 0)
    (hwind : HasWindingNumberZero g) :
    ∃ ell : ℝ → ℂ,
      Continuous ell ∧
      Function.Periodic ell 1 ∧
      ∀ x, Complex.exp (ell x) = g x := by
  obtain ⟨ L, hL_cont, hL_exp, hL_periodic ⟩ := hwind;
  -- Since L(x+1) - L(x) = k(x)*2πi for some integer k(x), and k is constant, we have k(x) = k(0) = 0.
  have hk_const : ∃ k : ℤ, ∀ x, L (x + 1) - L x = k * (2 * Real.pi * Complex.I) := by
    have hk_const : ∀ x, ∃ k : ℤ, L (x + 1) - L x = k * (2 * Real.pi * Complex.I) := by
      intro x; have := Complex.exp_eq_exp_iff_exists_int.mp ( show Complex.exp ( L ( x + 1 ) ) = Complex.exp ( L x ) from by aesop ) ; obtain ⟨ k, hk ⟩ := this; exact ⟨ k, by linear_combination hk ⟩ ;
    choose k hk using hk_const;
    have hk_const : Continuous (fun x => k x : ℝ → ℤ) := by
      have hk_const : Continuous (fun x => (k x : ℂ)) := by
        have hk_const : Continuous (fun x => (L (x + 1) - L x) / (2 * Real.pi * Complex.I)) := by
          exact Continuous.div_const ( Continuous.sub ( hL_cont.comp ( continuous_add_right _ ) ) hL_cont ) _;
        simp_all +decide [ mul_div_cancel_right₀, Real.pi_ne_zero, Complex.I_ne_zero ];
      rw [ Metric.continuous_iff ] at *;
      intro b ε hε; specialize hk_const b ε hε; rcases hk_const with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro a ha; specialize H a ha; simp_all +decide [ Complex.dist_eq, Complex.normSq ] ;
      norm_cast at H ⊢;
      erw [ Real.dist_eq ] ; aesop;
    have hk_const : IsConnected (Set.range k) := by
      exact isConnected_range hk_const;
    have := hk_const.isPreconnected.subsingleton;
    exact ⟨ k 0, fun x => by simpa [ this ( Set.mem_range_self x ) ( Set.mem_range_self 0 ) ] using hk x ⟩;
  obtain ⟨ k, hk ⟩ := hk_const; use L; simp_all +decide [ sub_eq_iff_eq_add ] ;
  have := hk 0; aesop;

/-
============================================================================
Part 2: Factored loop has a periodic log
============================================================================
-/
theorem factored_loop_has_periodic_log
    {d : ℕ} (M : ℤ) (ad : ℂ) (r : Fin d → ℂ)
    (had : ad ≠ 0)
    (hr_off : ∀ i, ‖r i‖ ≠ 1)
    (hM : M = ↑((univ.filter (fun i : Fin d => ‖r i‖ < 1)).card)) :
    IsPeriodicLog
      (fun x =>
        Complex.log (ad * ∏ i ∈ univ.filter (fun i : Fin d => 1 < ‖r i‖), (-r i)) +
        ∑ i ∈ univ.filter (fun i : Fin d => ‖r i‖ < 1),
          Complex.log (1 - r i * (circleParam x)⁻¹) +
        ∑ i ∈ univ.filter (fun i : Fin d => 1 < ‖r i‖),
          Complex.log (1 - (r i)⁻¹ * circleParam x))
      (fun x => circleParam x ^ (-M) * ad * ∏ i : Fin d, (circleParam x - r i)) := by
  refine' ⟨ _, _, _ ⟩;
  · refine' Continuous.add _ _;
    · refine' continuous_const.add ( continuous_finset_sum _ fun i hi => _ );
      have h_cont : ∀ x, 1 - r i * (circleParam x)⁻¹ ∈ Complex.slitPlane := by
        grind +suggestions;
      exact Continuous.clog ( by exact Continuous.sub continuous_const <| Continuous.mul continuous_const <| Continuous.inv₀ ( continuous_circleParam ) fun x => circleParam_ne_zero x ) fun x => h_cont x;
    · refine' continuous_finset_sum _ fun i hi => _;
      refine' continuous_clog_one_sub_mul_circleParam _;
      simpa using inv_lt_one_of_one_lt₀ ( by aesop );
  · unfold circleParam; norm_num [ mul_add, add_mul, Complex.exp_add ] ;
  · intro x;
    rw [ Complex.exp_add, Complex.exp_add, Complex.exp_log ];
    · rw [ Complex.exp_sum, Complex.exp_sum, Finset.prod_congr rfl fun i hi => Complex.exp_log ?_, Finset.prod_congr rfl fun i hi => Complex.exp_log ?_ ];
      · simp +decide [ hM, Finset.prod_filter, Finset.prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm, circleParam_def ];
        rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ];
        rw [ ← Finset.prod_const, Finset.prod_filter ];
        rw [ ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib ] ; refine' Or.inl ( Finset.prod_congr rfl fun i hi => _ ) ; split_ifs <;> simp_all +decide [ Complex.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm ] ;
        · linarith;
        · field_simp;
        · field_simp;
          rw [ mul_sub, mul_div_cancel₀ _ ( by rintro h; norm_num [ h ] at * ) ] ; ring;
        · exact False.elim <| hr_off i <| le_antisymm ‹_› ‹_›;
      · simp_all +decide [ sub_eq_iff_eq_add, circleParam ];
        exact fun h => hr_off i <| by have := congr_arg Norm.norm h; norm_num [ Complex.norm_exp ] at this; linarith;
      · rw [ Ne.eq_def, sub_eq_zero, eq_comm ];
        exact fun h => hr_off i <| by have := congr_arg Norm.norm h; norm_num at this; linarith [ Set.mem_setOf.mp hi ] ;
    · simp_all +decide [ Finset.prod_eq_zero_iff ];
      exact fun i hi => by rintro h; norm_num [ h ] at hi;

/-
============================================================================
Part 3: The winding-number wrapper theorem
============================================================================
-/
private theorem evalBiLaurentPoly_has_periodic_log
    {d : ℕ} (M : ℤ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (t : ℝ) (ad_val : ℂ) (had : ad_val ≠ 0)
    (r : Fin d → ℂ)
    (hr_off : ∀ i, ‖r i‖ ≠ 1)
    (hM : M = ↑((univ.filter (fun i : Fin d => ‖r i‖ < 1)).card))
    (hfact : Polynomial.C ad_val *
        ∏ i : Fin d, (Polynomial.X - Polynomial.C (r i)) =
        ∑ j : Fin (d + 1),
          Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ)) :
    ∃ ell : ℝ → ℂ, IsPeriodicLog ell (evalBiLaurentPoly coeffs M t) := by
  have := @factored_loop_has_periodic_log;
  specialize this M ad_val r had hr_off hM;
  refine' ⟨ _, this.cont, this.periodic, fun x => _ ⟩;
  convert this.exp_eq x using 1;
  convert evalBiLaurentPoly_eq_factored coeffs M t r ad_val hfact x using 1

theorem local_holonomy_certificate_winding_number
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
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ)) :
    ∃ (J : ℝ → ℂ),
    ∃ a' b' : ℝ,
      a < a' ∧ a' < b' ∧ b' < b ∧
      ∃ N : ℕ,
      ∃ A : Fin (N + 1) → LaurentPolynomial ℂ,
        (∃ n : Fin (N + 1), A n ≠ 0) ∧
        ∀ t ∈ Set.Ioo a' b',
          ∑ n : Fin (N + 1),
            evalLaurentCircle (A n) t * (J t) ^ (n : ℕ) = 0 := by
  simp +zetaDelta at *;
  refine' ⟨ 0, ( a + b ) / 2, _, b - ( b - a ) / 4, _, _, _ ⟩ <;> try linarith;
  refine' ⟨ 1, fun n => if n = 1 then 1 else 0, _, _ ⟩ <;> simp +decide;
  exact?

end