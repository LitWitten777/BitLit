import Mathlib

open Complex Finset MeasureTheory
open scoped BigOperators Real

set_option maxHeartbeats 800000

noncomputable section

/-! # Jensen Holonomy Formula -/

/-- The standard parameterization of the unit circle: `circleParam x = exp(2πix)`. -/
def circleParam (x : ℝ) : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I * ↑x)

/-- A continuous 1-periodic logarithm of a loop. -/
structure IsPeriodicLog (ell : ℝ → ℂ) (P : ℝ → ℂ) : Prop where
  cont : Continuous ell
  periodic : Function.Periodic ell 1
  exp_eq : ∀ x, Complex.exp (ell x) = P x

-- ============================================================================
-- Section 1: Basic properties of circleParam
-- ============================================================================

lemma circleParam_def (x : ℝ) :
    circleParam x = Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) := rfl

@[simp] lemma norm_circleParam (x : ℝ) : ‖circleParam x‖ = 1 := by
  simp [circleParam, Complex.norm_exp]

@[simp] lemma circleParam_ne_zero (x : ℝ) : circleParam x ≠ 0 := by
  exact Complex.exp_ne_zero _

@[simp] lemma circleParam_zero : circleParam 0 = 1 := by
  simp [circleParam]

lemma circleParam_periodic : Function.Periodic circleParam 1 := by
  unfold circleParam; norm_num [ mul_add, Complex.exp_add ] ;

lemma continuous_circleParam : Continuous circleParam := by
  exact Complex.continuous_exp.comp (by continuity)

lemma circleParam_inv (x : ℝ) : (circleParam x)⁻¹ = circleParam (-x) := by
  unfold circleParam; rw [← Complex.exp_neg]; push_cast; ring

/-
============================================================================
Section 2: Uniqueness of periodic logarithm
============================================================================
-/
lemma continuous_int_mul_two_pi_I_const {f : ℝ → ℂ} (hf : Continuous f)
    (hval : ∀ x, ∃ k : ℤ, f x = ↑k * (2 * ↑Real.pi * Complex.I)) :
    ∃ k : ℤ, ∀ x, f x = ↑k * (2 * ↑Real.pi * Complex.I) := by
  choose k hk using hval;
  -- Since $f$ is continuous and integer-valued, it must be constant.
  have h_const : Continuous k := by
    have h_const : Continuous (fun x => (k x : ℂ)) := by
      convert hf.div_const ( 2 * Real.pi * Complex.I ) using 2 ; aesop;
    rw [ Metric.continuous_iff ] at *;
    simp_all +decide [ Complex.dist_eq, Complex.normSq ];
    norm_cast at * ; aesop;
  -- Since $k$ is continuous and integer-valued, it must be constant.
  have h_const_k : ∀ x y : ℝ, k x = k y := by
    have h_const : IsPreconnected (Set.range k) := by
      exact isPreconnected_range h_const;
    exact fun x y => by have := h_const.subsingleton ( Set.mem_range_self x ) ( Set.mem_range_self y ) ; aesop;
  exact ⟨ k 0, fun x => hk x ▸ h_const_k x 0 ▸ rfl ⟩

lemma exp_integral_periodic_log_eq {ell₁ ell₂ : ℝ → ℂ} {P : ℝ → ℂ}
    (h1 : IsPeriodicLog ell₁ P) (h2 : IsPeriodicLog ell₂ P) :
    Complex.exp (∫ x in (0:ℝ)..1, ell₁ x) =
    Complex.exp (∫ x in (0:ℝ)..1, ell₂ x) := by
  -- By definition of $IsPeriodicLog$, we know that $ell_1(x) - ell_2(x) = k(x) \cdot 2\pi i$ for some integer $k(x)$.
  have h_diff : ∀ x, ∃ k : ℤ, ell₁ x - ell₂ x = k * (2 * Real.pi * Complex.I) := by
    intro x;
    have h_eq : Complex.exp (ell₁ x) = Complex.exp (ell₂ x) := by
      rw [ h1.exp_eq, h2.exp_eq ];
    rw [ Complex.exp_eq_exp_iff_exists_int ] at h_eq; obtain ⟨ k, hk ⟩ := h_eq; exact ⟨ k, by linear_combination hk ⟩ ;
  -- By continuous_int_mul_two_pi_I_const, k is constant.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ x, ell₁ x - ell₂ x = k * (2 * Real.pi * Complex.I) := by
    exact continuous_int_mul_two_pi_I_const ( h1.cont.sub h2.cont ) h_diff;
  rw [ intervalIntegral.integral_congr fun x hx => show ell₁ x = ell₂ x + k * ( 2 * Real.pi * Complex.I ) by linear_combination hk x, intervalIntegral.integral_add ] <;> norm_num;
  · exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨ k, by ring ⟩;
  · exact h2.cont.intervalIntegrable _ _

/-
============================================================================
Section 3: Key integral computation
============================================================================
-/
lemma one_sub_mul_circleParam_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) (x : ℝ) :
    (1 - w * circleParam x) ∈ Complex.slitPlane := by
  unfold slitPlane circleParam;
  norm_num [ Complex.exp_re, Complex.exp_im ];
  contrapose! hw;
  exact Real.le_sqrt_of_sq_le ( by simpa [ Complex.normSq_apply ] using by nlinarith [ sq_nonneg ( w.re * Real.sin ( 2 * Real.pi * x ) + w.im * Real.cos ( 2 * Real.pi * x ) ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * x ) ] )

lemma continuous_clog_one_sub_mul_circleParam {w : ℂ} (hw : ‖w‖ < 1) :
    Continuous (fun x : ℝ => Complex.log (1 - w * circleParam x)) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x;
  refine' ContinuousAt.clog _ _;
  · exact Continuous.continuousAt ( by exact Continuous.sub continuous_const <| Continuous.mul continuous_const <| by exact continuous_circleParam );
  · exact?

lemma integral_clog_one_sub_mul_circleParam {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ x in (0:ℝ)..1, Complex.log (1 - w * circleParam x) = 0 := by
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∫ x in (0 : ℝ)..1, ∑' n : ℕ, w ^ (n + 1) * circleParam x ^ (n + 1) / (n + 1) = ∑' n : ℕ, ∫ x in (0 : ℝ)..1, w ^ (n + 1) * circleParam x ^ (n + 1) / (n + 1) := by
    rw [ intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_tsum ];
    · norm_num [ intervalIntegral.integral_of_le zero_le_one ];
    · exact fun n => Continuous.aestronglyMeasurable ( by exact Continuous.div_const ( by exact Continuous.mul ( continuous_const.pow _ ) ( by exact Continuous.pow ( by exact continuous_circleParam ) _ ) ) _ );
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun n => _ ) _ );
      use fun n => ENNReal.ofReal ( ‖w‖ ^ ( n + 1 ) / ( n + 1 ) );
      · refine' le_trans ( MeasureTheory.lintegral_mono fun x => _ ) _;
        use fun x => ENNReal.ofReal ( ‖w‖ ^ ( n + 1 ) / ( n + 1 ) );
        · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
          · norm_cast;
          · positivity;
        · norm_num;
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg fun n => by positivity ];
        · exact ENNReal.ofReal_lt_top;
        · exact Summable.of_nonneg_of_le ( fun n => div_nonneg ( pow_nonneg ( norm_nonneg _ ) _ ) ( by positivity ) ) ( fun n => div_le_self ( pow_nonneg ( norm_nonneg _ ) _ ) ( by linarith ) ) ( Summable.comp_injective ( summable_geometric_of_lt_one ( norm_nonneg _ ) hw ) ( Nat.succ_injective ) );
  -- Evaluate the integral $\int_0^1 e^{2\pi i (n+1)x} \, dx$.
  have h_integral : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, circleParam x ^ (n + 1) = 0 := by
    -- Evaluate the integral $\int_0^1 e^{2\pi i (n+1)x} \, dx$ using the fundamental theorem of calculus.
    intro n
    have h_ftc : ∀ a b : ℝ, ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * (n + 1) * x) = (1 / (2 * Real.pi * Complex.I * (n + 1))) * (Complex.exp (2 * Real.pi * Complex.I * (n + 1) * b) - Complex.exp (2 * Real.pi * Complex.I * (n + 1) * a)) := by
      intro a b; have := @integral_exp_mul_complex a b; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      convert @this ( I * ( Real.pi * ( ( n + 1 ) * 2 ) ) ) ( by norm_num [ Complex.ext_iff, Real.pi_ne_zero, Nat.cast_add_one_ne_zero ] ) using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    convert h_ftc 0 1 using 3 <;> norm_num [ circleParam ];
    · rw [ ← Complex.exp_nat_mul ] ; push_cast ; ring;
    · exact Or.inr ( sub_eq_zero_of_eq <| Complex.exp_eq_one_iff.mpr ⟨ n + 1, by push_cast; ring ⟩ );
  -- By definition of $circleParam$, we know that $log(1 - w * circleParam x) = -\sum_{n=1}^{\infty} \frac{(w * circleParam x)^n}{n}$.
  have h_log_series : ∀ x : ℝ, log (1 - w * circleParam x) = -∑' n : ℕ, w ^ (n + 1) * circleParam x ^ (n + 1) / (n + 1) := by
    intro x
    have h_series : HasSum (fun n : ℕ => (w * circleParam x) ^ (n + 1) / (n + 1)) (-Complex.log (1 - w * circleParam x)) := by
      have h_series : HasSum (fun n : ℕ => (w * circleParam x) ^ n / n) (-Complex.log (1 - w * circleParam x)) := by
        have h_series : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n : ℕ => z ^ n / n) (-Complex.log (1 - z)) := by
          grind +suggestions;
        exact h_series _ ( by simpa [ norm_circleParam ] using hw );
      convert hasSum_nat_add_iff' 1 |>.2 h_series using 1 ; aesop;
      norm_num [ Finset.sum_range_succ' ];
    simp_all +decide [ mul_pow ];
    rw [ h_series.tsum_eq, neg_neg ];
  simp_all +decide [ mul_div_assoc ]

lemma integral_clog_one_sub_mul_circleParam_inv {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ x in (0:ℝ)..1, Complex.log (1 - w * (circleParam x)⁻¹) = 0 := by
  -- By substitution using $u = 1 - x$, the integral becomes $\int_{0}^{1} \log(1 - w e^{2 \pi i u}) du$.
  suffices h_subst : ∫ x in (0 : ℝ)..1, Complex.log (1 - w * circleParam (1 - x)) = ∫ x in (0 : ℝ)..1, Complex.log (1 - w * circleParam x) by
    convert h_subst using 1;
    · unfold circleParam; norm_num [ mul_sub, Complex.exp_sub ] ;
    · rw [ integral_clog_one_sub_mul_circleParam hw ];
  convert intervalIntegral.integral_comp_sub_left _ 1 using 2 <;> norm_num

/-
============================================================================
Section 4: Main theorem
============================================================================
-/
theorem complex_jensen_holonomy_product
    {d : ℕ} {M : ℤ} {ad : ℂ} {r : Fin d → ℂ}
    {P_loop : ℝ → ℂ} {ell : ℝ → ℂ}
    (hP : ∀ x, P_loop x =
      circleParam x ^ (-M) * ad * ∏ i : Fin d, (circleParam x - r i))
    (had : ad ≠ 0)
    (hr_off : ∀ i, ‖r i‖ ≠ 1)
    (hM : M = ↑((univ.filter (fun i : Fin d => ‖r i‖ < 1)).card))
    (hell : IsPeriodicLog ell P_loop) :
    Complex.exp (∫ x in (0:ℝ)..1, ell x) =
      ad * (∏ i ∈ Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖), (-r i)) := by
  -- Define the explicit periodic logarithm $\ell_0$.
  set ell₀ : ℝ → ℂ := fun x => Complex.log (ad * ∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (-r i)) + ∑ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), Complex.log (1 - r i / circleParam x) + ∑ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), Complex.log (1 - circleParam x / r i);
  -- Show that $\ell_0$ is a valid periodic logarithm.
  have h_ell₀_valid : IsPeriodicLog ell₀ P_loop := by
    have h_exp_ell₀ : ∀ x, Complex.exp (ell₀ x) = P_loop x := by
      intro x;
      have h_exp_ell₀ : Complex.exp (ell₀ x) = (ad * ∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (-r i)) * (∏ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), (1 - r i / circleParam x)) * (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (1 - circleParam x / r i)) := by
        rw [ Complex.exp_add, Complex.exp_add, Complex.exp_log ];
        · rw [ Complex.exp_sum, Complex.exp_sum, Finset.prod_congr rfl fun i hi => Complex.exp_log <| ?_, Finset.prod_congr rfl fun i hi => Complex.exp_log <| ?_ ];
          · rw [ Ne.eq_def, sub_eq_zero, eq_div_iff ] <;> norm_num [ circleParam_ne_zero ];
            · exact fun h => hr_off i <| by rw [ h ] ; exact norm_circleParam x;
            · exact fun h => by norm_num [ h ] at hi;
          · rw [ Ne.eq_def, sub_eq_zero, eq_div_iff ] <;> norm_num [ circleParam_ne_zero ];
            exact fun h => hr_off i <| by rw [ ← h, norm_circleParam ] ;
        · simp_all +decide [ Finset.prod_eq_zero_iff ];
          exact fun i hi => by rintro h; norm_num [ h ] at hi;
      -- Simplify the expression for $\exp(\ell_0(x))$.
      have h_simplify : (∏ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), (1 - r i / circleParam x)) * (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (1 - circleParam x / r i)) = (∏ i, (circleParam x - r i)) / (circleParam x ^ (Finset.card (Finset.univ.filter (fun i => ‖r i‖ < 1))) * (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (-r i))) := by
        have h_simplify : (∏ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), (1 - r i / circleParam x)) = (∏ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), (circleParam x - r i)) / (circleParam x ^ (Finset.card (Finset.univ.filter (fun i => ‖r i‖ < 1)))) ∧ (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (1 - circleParam x / r i)) = (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (circleParam x - r i)) / (∏ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), (-r i)) := by
          constructor;
          · rw [ Finset.prod_congr rfl fun i hi => one_sub_div ( circleParam_ne_zero x ) ];
            rw [ Finset.prod_div_distrib, Finset.prod_const, Finset.card_eq_sum_ones ];
          · rw [ ← Finset.prod_div_distrib ];
            refine' Finset.prod_congr rfl fun i hi => _;
            rw [ sub_div' ] <;> ring ; norm_num [ show r i ≠ 0 from fun h => by norm_num [ h ] at hi ];
        rw [ h_simplify.1, h_simplify.2, div_mul_div_comm ];
        rw [ ← Finset.prod_union ];
        · rcongr i ; cases lt_or_gt_of_ne ( hr_off i ) <;> aesop;
        · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
      by_cases h : ∏ i with 1 < ‖r i‖, -r i = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      grind;
    constructor;
    · refine' Continuous.add ( Continuous.add continuous_const _ ) _;
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' continuous_iff_continuousAt.mpr _;
        intro x;
        refine' ContinuousAt.clog _ _;
        · exact ContinuousAt.sub continuousAt_const <| ContinuousAt.div continuousAt_const ( continuous_circleParam.continuousAt ) <| circleParam_ne_zero x;
        · simp_all +decide [ Complex.slitPlane, circleParam ];
          exact Or.inl ( lt_of_le_of_lt ( Complex.re_le_norm _ ) ( by simpa [ Complex.norm_exp ] using hi ) );
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' Continuous.clog _ _;
        · exact Continuous.sub continuous_const <| Continuous.div_const ( continuous_circleParam ) _;
        · intro x; simp_all +decide [ Complex.slitPlane ];
          refine' Or.inl ( lt_of_le_of_lt ( Complex.re_le_norm _ ) _ );
          simp +zetaDelta at *;
          exact inv_lt_one_of_one_lt₀ hi;
    · simp +zetaDelta at *;
      unfold circleParam; norm_num [ mul_add, add_mul, Complex.exp_add ] ;
    · assumption;
  have h_exp_ell₀ : Complex.exp (∫ x in (0:ℝ)..1, ell₀ x) = ad * ∏ i with 1 < ‖r i‖, -r i := by
    -- The integral of the logarithms of the terms involving $r_i$ is zero because they are periodic with period 1.
    have h_int_zero : ∫ x in (0:ℝ)..1, ∑ i ∈ Finset.univ.filter (fun i => ‖r i‖ < 1), Complex.log (1 - r i / circleParam x) = 0 ∧ ∫ x in (0:ℝ)..1, ∑ i ∈ Finset.univ.filter (fun i => 1 < ‖r i‖), Complex.log (1 - circleParam x / r i) = 0 := by
      constructor <;> rw [ intervalIntegral.integral_finset_sum ] <;> norm_num;
      · refine' Finset.sum_eq_zero fun i hi => _;
        convert integral_clog_one_sub_mul_circleParam_inv ( show ‖r i‖ < 1 from by simpa using hi ) using 1;
      · intro i hi; apply_rules [ ContinuousOn.intervalIntegrable ] ;
        refine' ContinuousOn.clog _ _ <;> norm_num [ circleParam ];
        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub continuousAt_const <| ContinuousAt.div continuousAt_const ( Complex.continuous_exp.continuousAt.comp <| ContinuousAt.mul continuousAt_const <| Complex.continuous_ofReal.continuousAt ) <| Complex.exp_ne_zero _;
        · intro x hx₁ hx₂; rw [ Complex.slitPlane ] ; norm_num [ Complex.exp_ne_zero ];
          exact Or.inl ( lt_of_le_of_lt ( Complex.re_le_norm _ ) ( by simpa [ Complex.norm_exp ] using hi ) );
      · refine' Finset.sum_eq_zero fun i hi => _;
        have := integral_clog_one_sub_mul_circleParam ( show ‖ ( r i ) ⁻¹‖ < 1 from by simpa [ abs_inv ] using inv_lt_one_of_one_lt₀ <| by aesop );
        simpa only [ div_eq_inv_mul ] using this;
      · intro i hi;
        apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.clog _ _;
        · exact Continuous.continuousOn ( by exact Continuous.sub continuous_const <| Continuous.div_const ( by exact Complex.continuous_exp.comp <| by continuity ) _ );
        · intro x hx; simp +decide [ Complex.slitPlane, circleParam ] ;
          norm_num [ Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im ];
          field_simp;
          refine' Or.inl ( div_lt_one ( normSq_pos.mpr ( show r i ≠ 0 from by rintro h; norm_num [ h ] at hi ) ) |>.2 _ );
          norm_num [ Complex.normSq, Complex.norm_def ] at *;
          rw [ Real.lt_sqrt ] at hi <;> nlinarith [ sq_nonneg ( Real.cos ( 2 * Real.pi * x ) * ( r i |> Complex.im ) - Real.sin ( 2 * Real.pi * x ) * ( r i |> Complex.re ) ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * x ) ];
    rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> norm_num [ h_int_zero ];
    · rw [ Complex.exp_log ];
      simp_all +decide [ Finset.prod_eq_zero_iff ];
      exact fun i hi => by rintro h; norm_num [ h ] at hi;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' continuousOn_finset_sum _ fun i hi => ContinuousOn.clog _ _;
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub continuousAt_const <| ContinuousAt.div continuousAt_const ( show ContinuousAt circleParam x from by exact Continuous.continuousAt <| by exact continuous_circleParam ) <| by exact circleParam_ne_zero x;
      · simp_all +decide [ Complex.slitPlane ];
        intro x hx₁ hx₂; contrapose! hr_off; simp_all +decide [ Complex.div_re, Complex.div_im, circleParam ] ;
        norm_num [ Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq, Complex.norm_exp ] at hr_off;
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        rw [ Real.sqrt_lt' ] at hi <;> nlinarith [ sq_nonneg ( ( r i |> Complex.re ) * Real.sin ( 2 * Real.pi * x ) - ( r i |> Complex.im ) * Real.cos ( 2 * Real.pi * x ) ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * x ) ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' ContinuousOn.add continuousOn_const _;
      refine' continuousOn_finset_sum _ fun i hi => ContinuousOn.clog _ _;
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub continuousAt_const <| ContinuousAt.div continuousAt_const ( show ContinuousAt circleParam x from by exact Continuous.continuousAt <| by exact continuous_circleParam ) <| by exact circleParam_ne_zero x;
      · simp_all +decide [ Complex.slitPlane ];
        intro x hx₁ hx₂; contrapose! hr_off; simp_all +decide [ Complex.div_re, Complex.div_im, circleParam ] ;
        norm_num [ Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq, Complex.norm_exp ] at hr_off;
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        rw [ Real.sqrt_lt' ] at hi <;> nlinarith [ sq_nonneg ( ( r i |> Complex.re ) * Real.sin ( 2 * Real.pi * x ) - ( r i |> Complex.im ) * Real.cos ( 2 * Real.pi * x ) ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * x ) ];
    · apply_rules [ Continuous.intervalIntegrable ];
      refine' continuous_finset_sum _ fun i hi => _;
      refine' Continuous.clog _ _;
      · exact Continuous.sub continuous_const <| Continuous.div_const ( continuous_circleParam ) _;
      · intro x; simp +decide [ Complex.slitPlane, circleParam ] ;
        norm_num [ Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im ];
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        rw [ Real.lt_sqrt ] at hi <;> norm_num at *;
        field_simp;
        exact Or.inl ( by rw [ div_lt_iff₀ ] <;> nlinarith [ sq_nonneg ( ( r i |> Complex.re ) * Real.sin ( 2 * Real.pi * x ) - Real.cos ( 2 * Real.pi * x ) * ( r i |> Complex.im ) ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * x ) ] );
  rw [ ← h_exp_ell₀, exp_integral_periodic_log_eq hell h_ell₀_valid ]

end

#check complex_jensen_holonomy_product