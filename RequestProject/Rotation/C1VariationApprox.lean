import Mathlib
import RequestProject.Rotation.ConcreteVariation

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology intervalIntegral

/-!
# C¹ functions have bounded variation controlled by the L¹-norm of the derivative
(Run C, Task 1, target 2)

For a `C¹` function `f` on `[0,1]` with derivative `f'`, the total variation is
controlled by the `L¹`-norm of the derivative:
```
  eVariationOn f (Set.Icc 0 1) ≤ ENNReal.ofReal (∫ x in 0..1, ‖f' x‖).
```
In particular such an `f` has bounded variation (`ConcreteHasBV f`) and its
concrete total variation is bounded by `∫₀¹ ‖f'‖`.

The proof is the classical one: on any monotone partition `0 ≤ u₀ ≤ ⋯ ≤ uₙ ≤ 1`,
the fundamental theorem of calculus gives
`f(uᵢ₊₁) - f(uᵢ) = ∫_{uᵢ}^{uᵢ₊₁} f'`, hence
`‖f(uᵢ₊₁) - f(uᵢ)‖ ≤ ∫_{uᵢ}^{uᵢ₊₁} ‖f'‖`, and summing telescopes to
`∫_{u₀}^{uₙ} ‖f'‖ ≤ ∫₀¹ ‖f'‖`.  Taking the supremum over partitions gives the
claim.
-/

namespace CriticalMixedHRT

/-- FTC norm bound: for a `C¹` function on a window containing `[a,b]` with
`a ≤ b`, `‖f b - f a‖ ≤ ∫ x in a..b, ‖f' x‖`. -/
theorem norm_sub_le_integral_norm_deriv
    {f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc a b)) :
    ‖f b - f a‖ ≤ ∫ x in a..b, ‖f' x‖ := by
  have hint : IntervalIntegrable f' MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hFTC : (∫ x in a..b, f' x) = f b - f a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hderiv x (by rwa [Set.uIcc_of_le hab] at hx)
    · exact hint
  calc ‖f b - f a‖ = ‖∫ x in a..b, f' x‖ := by rw [hFTC]
    _ ≤ ∫ x in a..b, ‖f' x‖ := intervalIntegral.norm_integral_le_integral_norm hab

/-
**C¹ variation bound.** The total variation of a `C¹` function over `[0,1]`
is at most the `L¹`-norm of its derivative.
-/
theorem eVariationOn_le_ofReal_integral_norm_deriv
    {f f' : ℝ → ℂ}
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc (0 : ℝ) 1)) :
    eVariationOn f (Set.Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (∫ x in (0 : ℝ)..1, ‖f' x‖) := by
  refine' iSup_le _;
  rintro ⟨ n, ⟨ u, hu₁, hu₂ ⟩ ⟩;
  -- Apply the pointwise bound to each term in the sum.
  have h_sum_bound : ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ ≤ ∫ x in (u 0)..(u n), ‖f' x‖ := by
    have h_sum_bound : ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ ≤ ∑ i ∈ Finset.range n, ∫ x in (u i).. (u (i + 1)), ‖f' x‖ := by
      apply Finset.sum_le_sum;
      intro i hi;
      apply norm_sub_le_integral_norm_deriv;
      · exact hu₁ ( Nat.le_succ _ );
      · exact fun x hx => hderiv x ⟨ hu₂ i |>.1.trans hx.1, hx.2.trans ( hu₂ ( i + 1 ) |>.2 ) ⟩;
      · exact hcont.mono ( Set.Icc_subset_Icc ( hu₂ i |>.1 ) ( hu₂ ( i + 1 ) |>.2 ) );
    convert h_sum_bound using 1;
    rw [ intervalIntegral.sum_integral_adjacent_intervals ];
    intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ];
    exact ContinuousOn.norm ( hcont.mono ( by rw [ Set.uIcc_of_le ( hu₁ ( Nat.le_succ _ ) ) ] ; exact Set.Icc_subset_Icc ( hu₂ _ |>.1 ) ( hu₂ _ |>.2 ) ) );
  -- Since $u$ is monotone and $u_i \in [0, 1]$ for all $i$, we have $\int_{u_0}^{u_n} \|f'(x)\| \, dx \leq \int_0^1 \|f'(x)\| \, dx$.
  have h_integral_bound : ∫ x in (u 0)..(u n), ‖f' x‖ ≤ ∫ x in (0 : ℝ)..1, ‖f' x‖ := by
    apply_rules [ intervalIntegral.integral_mono_interval ];
    · linarith [ hu₂ 0 |>.1 ];
    · norm_num;
    · exact hu₂ n |>.2;
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      simpa using hcont.norm;
  convert ENNReal.ofReal_le_ofReal ( h_sum_bound.trans h_integral_bound ) using 1;
  rw [ ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _ ] ; norm_num [ edist_dist, dist_eq_norm ]

/-- A `C¹` function on `[0,1]` has bounded variation in the concrete sense. -/
theorem concreteHasBV_of_c1
    {f f' : ℝ → ℂ}
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc (0 : ℝ) 1)) :
    ConcreteHasBV f := by
  have h := eVariationOn_le_ofReal_integral_norm_deriv hderiv hcont
  exact ne_top_of_le_ne_top (by exact ENNReal.ofReal_ne_top) h

/-- The concrete total variation of a `C¹` function is bounded by the `L¹`-norm
of its derivative. -/
theorem concreteVariation_le_integral_norm_deriv
    {f f' : ℝ → ℂ}
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Set.Icc (0 : ℝ) 1)) :
    concreteVariation f ≤ ∫ x in (0 : ℝ)..1, ‖f' x‖ := by
  have h := eVariationOn_le_ofReal_integral_norm_deriv hderiv hcont
  unfold concreteVariation
  calc (eVariationOn f (Set.Icc (0 : ℝ) 1)).toReal
      ≤ (ENNReal.ofReal (∫ x in (0 : ℝ)..1, ‖f' x‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = ∫ x in (0 : ℝ)..1, ‖f' x‖ :=
        ENNReal.toReal_ofReal
          (intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _))

end CriticalMixedHRT