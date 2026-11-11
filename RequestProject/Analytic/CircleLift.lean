import Mathlib

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex

/-!
# Local real-analytic angle lift of a unit-modulus analytic map

If `H` is analytic and nonvanishing with `‖H‖ ≡ 1` on an open set, then near any
point it can be written as `H x = exp(2πi · y x)` for a real differentiable
angle `y`, whose derivative is bounded below in absolute value wherever
`deriv H ≠ 0`.  This is the lifting input to the analytic parameter-rigidity
argument.
-/

namespace CriticalMixedHRT

/-
For a unit-modulus analytic map, the logarithmic derivative is purely
imaginary.
-/
theorem re_deriv_div_self_eq_zero
    (U : Set ℝ) (hU : IsOpen U) (H : ℝ → ℂ)
    (hH : AnalyticOnNhd ℝ H U) (hHnorm : ∀ s ∈ U, ‖H s‖ = 1)
    (s : ℝ) (hs : s ∈ U) :
    (deriv H s / H s).re = 0 := by
  -- Let $f(x) = H(x) \overline{H(x)}$. Since $H(x)$ has unit modulus on $U$, we have $f(x) = 1$ for all $x \in U$.
  set f : ℝ → ℂ := fun x => H x * (starRingEnd ℂ) (H x)
  have hf : ∀ x ∈ U, f x = 1 := by
    simp +zetaDelta at *;
    simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
  -- By definition of $f$, we know that its derivative is zero everywhere in $U$.
  have h_deriv_f : deriv f s = 0 := by
    exact HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( hU.mem_nhds hs ) hf ) );
  -- By definition of $f$, we know that its derivative is given by the product rule.
  have h_deriv_f_prod : deriv f s = deriv H s * (starRingEnd ℂ) (H s) + H s * (starRingEnd ℂ) (deriv H s) := by
    convert HasDerivAt.deriv ( HasDerivAt.mul ( hH.differentiableOn.differentiableAt ( hU.mem_nhds hs ) |> DifferentiableAt.hasDerivAt ) ( HasDerivAt.star ( hH.differentiableOn.differentiableAt ( hU.mem_nhds hs ) |> DifferentiableAt.hasDerivAt ) ) ) using 1;
  simp_all +decide [ Complex.ext_iff, div_eq_mul_inv ];
  grind

/-
**Local real-analytic angle lift.**  Near any point `s₀` where
`deriv H ≠ 0`, a unit-modulus analytic `H` factors as `exp(2πi · y)` for a real
function `y` with derivative bounded below in absolute value by a positive
constant.
-/
theorem analytic_circle_local_lift
    (U : Set ℝ) (hU : IsOpen U) (H : ℝ → ℂ)
    (hH : AnalyticOnNhd ℝ H U) (hHnorm : ∀ s ∈ U, ‖H s‖ = 1)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (hderiv : deriv H s₀ ≠ 0) :
    ∃ (a b : ℝ) (y : ℝ → ℝ) (y' : ℝ → ℝ) (c : ℝ),
      0 < c ∧ s₀ ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U ∧
      (∀ x ∈ Set.Ioo a b, HasDerivAt y (y' x) x) ∧
      (∀ x ∈ Set.Ioo a b, c ≤ |y' x|) ∧
      (∀ x ∈ Set.Ioo a b,
        H x = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y x : ℂ))) := by
  obtain ⟨a, b, hab⟩ : ∃ a b, s₀ ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U ∧ ∀ x ∈ Set.Ioo a b, (H x / H s₀).re > 0 ∧ ‖deriv H x‖ > ‖deriv H s₀‖ / 2 := by
    have h_cont : ContinuousAt (fun x => (H x / H s₀).re) s₀ ∧ ContinuousAt (fun x => ‖deriv H x‖) s₀ := by
      constructor;
      · exact Complex.continuous_re.continuousAt.comp ( ContinuousAt.div_const ( hH.continuousOn.continuousAt ( hU.mem_nhds hs₀ ) ) _ );
      · exact ContinuousAt.norm ( hH.deriv.continuousOn.continuousAt ( hU.mem_nhds hs₀ ) );
    have h_cont : ∃ ε > 0, ∀ x, abs (x - s₀) < ε → (H x / H s₀).re > 0 ∧ ‖deriv H x‖ > ‖deriv H s₀‖ / 2 := by
      exact Metric.mem_nhds_iff.mp ( Filter.inter_mem ( h_cont.1.eventually ( lt_mem_nhds ( show ( H s₀ / H s₀ |> Complex.re ) > 0 from by rw [ div_self <| by specialize hHnorm s₀ hs₀; aesop ] ; norm_num ) ) ) ( h_cont.2.eventually ( lt_mem_nhds ( show ‖deriv H s₀‖ > ‖deriv H s₀‖ / 2 from half_lt_self <| norm_pos_iff.mpr hderiv ) ) ) );
    obtain ⟨ ε, ε_pos, hε ⟩ := h_cont; rcases Metric.mem_nhds_iff.mp ( hU.mem_nhds hs₀ ) with ⟨ δ, δ_pos, hδ ⟩ ; exact ⟨ s₀ - Min.min ε δ, s₀ + Min.min ε δ, ⟨ by linarith [ lt_min ε_pos δ_pos ], by linarith [ lt_min ε_pos δ_pos ] ⟩, fun x hx => hδ <| mem_ball_iff_norm.mpr <| abs_lt.mpr ⟨ by linarith [ hx.1, min_le_left ε δ, min_le_right ε δ ], by linarith [ hx.2, min_le_left ε δ, min_le_right ε δ ] ⟩, fun x hx => hε x <| abs_lt.mpr ⟨ by linarith [ hx.1, min_le_left ε δ, min_le_right ε δ ], by linarith [ hx.2, min_le_left ε δ, min_le_right ε δ ] ⟩ ⟩ ;
  refine' ⟨ a, b, fun x => ( Complex.log ( H x / H s₀ ) |> Complex.im ) / ( 2 * Real.pi ) + Complex.arg ( H s₀ ) / ( 2 * Real.pi ), fun x => ( deriv H x / H x |> Complex.im ) / ( 2 * Real.pi ), ‖deriv H s₀‖ / ( 4 * Real.pi ), by positivity, hab.1, hab.2.1, _, _, _ ⟩ <;> simp_all +decide [ Complex.norm_exp ];
  · intro x hx₁ hx₂
    have h_log : HasDerivAt (fun x => Complex.log (H x / H s₀)) ((deriv H x / H x)) x := by
      convert HasDerivAt.comp x ( Complex.hasDerivAt_log _ ) ( HasDerivAt.div_const ( hH.differentiableOn.differentiableAt ( hU.mem_nhds <| hab.2.1 ⟨ hx₁, hx₂ ⟩ ) |> DifferentiableAt.hasDerivAt ) _ ) using 1 <;> norm_num [ Complex.exp_ne_zero, hderiv ];
      · rw [ div_mul_div_comm, mul_comm ] ; ring ; norm_num [ show H s₀ ≠ 0 from by specialize hHnorm s₀ hs₀; aesop ] ;
      · exact Or.inl ( hab.2.2 x hx₁ hx₂ |>.1 );
    rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
    convert Complex.continuous_im.continuousAt.tendsto.comp h_log |> ( ·.div_const ( 2 * Real.pi ) ) using 2 ; norm_num ; ring;
  · -- By definition of $y'$, we know that $|(deriv H x / H x).im| = ‖deriv H x‖$.
    have h_im : ∀ x ∈ Set.Ioo a b, |(deriv H x / H x).im| = ‖deriv H x‖ := by
      intro x hx
      have h_im : (deriv H x / H x).re = 0 := by
        apply re_deriv_div_self_eq_zero U hU H hH hHnorm x (hab.2.1 hx);
      simp_all +decide [ Complex.div_re, Complex.div_im ];
      rw [ ← sq_eq_sq₀ ] <;> norm_num [ Complex.normSq_apply, Complex.norm_def ] at *;
      rw [ Real.sq_sqrt ( add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ ) ) ] ; rw [ div_add_div_same, div_eq_iff ] at h_im <;> norm_num [ hHnorm x ( hab.2.1 hx ) ] at * ; nlinarith [ hHnorm x ( hab.2.1 hx ) ] ;
    intro x hx₁ hx₂; rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 * Real.pi ) ] ; rw [ h_im x ⟨ hx₁, hx₂ ⟩ ] ; rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, hab.2.2 x hx₁ hx₂ ] ;
  · intro x hx₁ hx₂; have := Complex.exp_log ( show H x / H s₀ ≠ 0 from div_ne_zero ( by specialize hHnorm x ( hab.2.1 ⟨ hx₁, hx₂ ⟩ ) ; aesop ) ( by specialize hHnorm s₀ hs₀; aesop ) ) ; simp_all +decide [ Complex.exp_add, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, Real.pi_ne_zero ] ;
    convert congr_arg ( fun z => z * H s₀ ) this.symm using 1 <;> ring;
    · rw [ mul_assoc, mul_inv_cancel₀ ( by specialize hHnorm s₀ hs₀; aesop ), mul_one ];
    · rw [ ← Complex.exp_add ] ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ] ; ring;
      rw [ Real.cos_add, Real.sin_add ] ; norm_num [ Complex.cos_arg, Complex.sin_arg, show H s₀ ≠ 0 from by specialize hHnorm s₀ hs₀; aesop, show H x ≠ 0 from by specialize hHnorm x ( hab.2.1 ⟨ hx₁, hx₂ ⟩ ) ; aesop ] ; ring ; norm_num [ Real.exp_log, hHnorm x ( hab.2.1 ⟨ hx₁, hx₂ ⟩ ), hHnorm s₀ hs₀ ] ;

end CriticalMixedHRT