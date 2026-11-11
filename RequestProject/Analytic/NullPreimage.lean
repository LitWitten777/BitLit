import Mathlib

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology

/-!
# Null preimages under expanding maps

Real-analysis infrastructure used in the analytic parameter-rigidity step.

* `lipschitzOnWith_image_volume_zero` — a Lipschitz map sends null sets to null
  sets (on `ℝ`).
* `expanding_preimage_null` — if `f` has derivative bounded below in absolute
  value by `c > 0` on an open interval, then the preimage of a null set
  intersected with that interval is null.
-/

namespace CriticalMixedHRT

/-
A function that is Lipschitz on a set sends a null subset to a null set
(in `ℝ`, where Hausdorff `1`-measure is Lebesgue measure).
-/
theorem lipschitzOnWith_image_volume_zero
    {K : NNReal} {g : ℝ → ℝ} {s : Set ℝ}
    (hg : LipschitzOnWith K g s) {t : Set ℝ} (hts : t ⊆ s)
    (ht : volume t = 0) :
    volume (g '' t) = 0 := by
  -- Apply `LipschitzOnWith.hausdorffMeasure_image_le` with `d = 1` (1 ≥ 0) to get `μH[1] (g '' t) ≤ K^1 * μH[1] t`.
  have h_le : MeasureTheory.Measure.hausdorffMeasure 1 (g '' t) ≤ (K : ENNReal) * MeasureTheory.Measure.hausdorffMeasure 1 t := by
    convert LipschitzOnWith.hausdorffMeasure_image_le ( hg.mono hts ) ( by norm_num : ( 0 : ℝ ) ≤ 1 ) using 1 ; norm_num [ ENNReal.ofReal ];
  simp_all +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ]

/-
**Expanding preimage is null.**  If `f` has, on the open interval
`Set.Ioo a b`, a derivative bounded below in absolute value by a constant
`c > 0`, then the preimage of any null set `N` meets `Set.Ioo a b` in a null
set.
-/
theorem expanding_preimage_null
    (a b : ℝ) (f : ℝ → ℝ) (f' : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, c ≤ |f' x|)
    (N : Set ℝ) (hN : volume N = 0) :
    volume ({x | x ∈ Set.Ioo a b ∧ f x ∈ N}) = 0 := by
  -- Step 1 (lower Lipschitz bound). For any `x y ∈ I` we have `c * |x - y| ≤ |f x - f y|`.
  have h_lower_lip : ∀ x y : ℝ, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → x < y → c * (y - x) ≤ |f y - f x| := by
    intro x y hx hy hxy;
    have := exists_deriv_eq_slope f hxy;
    contrapose! this;
    exact ⟨ continuousOn_of_forall_continuousAt fun z hz => HasDerivAt.continuousAt ( hf z ⟨ by linarith [ hz.1, hx.1 ], by linarith [ hz.2, hy.2 ] ⟩ ), fun z hz => ( hf z ⟨ by linarith [ hz.1, hx.1 ], by linarith [ hz.2, hy.2 ] ⟩ |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt ), fun z hz => by rw [ ne_eq, eq_div_iff ] <;> cases abs_cases ( f y - f x ) <;> cases abs_cases ( f' z ) <;> nlinarith [ hf' z ⟨ by linarith [ hz.1, hx.1 ], by linarith [ hz.2, hy.2 ] ⟩, ( hf z ⟨ by linarith [ hz.1, hx.1 ], by linarith [ hz.2, hy.2 ] ⟩ |> HasDerivAt.deriv ) ] ⟩;
  -- Step 2 (Lipschitz inverse). Let `g := Set.invFunOn f I`, the left inverse of `f` on `I`.
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Ioo a b, g (f x) = x ∧ ∀ u ∈ f '' Set.Ioo a b, ∀ v ∈ f '' Set.Ioo a b, |g u - g v| ≤ (1 / c) * |u - v| := by
    -- Define the inverse function $g$ on the image of $f$.
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Ioo a b, g (f x) = x := by
      have h_inj : ∀ x y : ℝ, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → f x = f y → x = y := by
        intro x y hx hy hxy; exact le_antisymm ( le_of_not_gt fun h => by have := h_lower_lip _ _ hy hx h; norm_num [ hxy ] at this; nlinarith ) ( le_of_not_gt fun h => by have := h_lower_lip _ _ hx hy h; norm_num [ hxy ] at this; nlinarith ) ;
      have h_inv : ∀ y ∈ f '' Set.Ioo a b, ∃! x, x ∈ Set.Ioo a b ∧ f x = y := by
        exact fun y hy => by obtain ⟨ x, hx, rfl ⟩ := hy; exact ⟨ x, ⟨ hx, rfl ⟩, fun z hz => h_inj _ _ hz.1 hx hz.2 ⟩ ;
      choose! g hg₁ hg₂ using h_inv;
      exact ⟨ g, fun x hx => hg₂ _ ( Set.mem_image_of_mem f hx ) _ ⟨ hx, rfl ⟩ ▸ rfl ⟩;
    refine' ⟨ g, fun x hx => ⟨ hg x hx, _ ⟩ ⟩;
    rintro _ ⟨ u, hu, rfl ⟩ _ ⟨ v, hv, rfl ⟩;
    cases lt_trichotomy u v <;> simp_all +decide [ abs_sub_comm, div_eq_inv_mul ];
    · rw [ inv_mul_eq_div, le_div_iff₀ ] <;> cases abs_cases ( u - v ) <;> cases abs_cases ( f u - f v ) <;> nlinarith [ h_lower_lip u v hu.1 hu.2 hv.1 hv.2 ‹_› ];
    · cases ‹_› <;> simp_all +decide [ abs_sub_comm, inv_mul_eq_div ];
      rw [ le_div_iff₀' hc ] ; specialize h_lower_lip v u hv.1 hv.2 hu.1 hu.2 ‹_› ; cases abs_cases ( u - v ) <;> cases abs_cases ( f u - f v ) <;> cases abs_cases ( f v - f u ) <;> nlinarith;
  -- By `lipschitzOnWith_image_volume_zero` (already proved above) applied to `g` (Lipschitz on `f '' I`, with `f '' A ⊆ f '' I`), `volume (g '' (f '' A)) = 0`.
  have h_volume_g : volume (g '' (f '' {x | x ∈ Set.Ioo a b ∧ f x ∈ N})) = 0 := by
    apply lipschitzOnWith_image_volume_zero;
    any_goals exact f '' Set.Ioo a b;
    any_goals exact Real.toNNReal ( 1 / c );
    · rw [ lipschitzOnWith_iff_norm_sub_le ];
      simp +zetaDelta at *;
      exact fun x y hy₁ hy₂ hx z w hw₁ hw₂ hz => by rw [ max_eq_left ( by positivity ) ] ; exact hg y hy₁ hy₂ |>.2 _ _ hy₁ hy₂ hx _ _ hw₁ hw₂ hz;
    · grind;
    · exact MeasureTheory.measure_mono_null ( Set.image_subset_iff.mpr fun x hx => hx.2 ) hN;
  refine' MeasureTheory.measure_mono_null _ h_volume_g;
  exact fun x hx => ⟨ f x, ⟨ x, hx, rfl ⟩, hg x hx.1 |>.1 ⟩

end CriticalMixedHRT