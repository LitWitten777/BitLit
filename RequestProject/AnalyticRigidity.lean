import Mathlib
import RequestProject.ResonanceGroup
import RequestProject.Analytic.NullPreimage
import RequestProject.Analytic.ResonanceReal
import RequestProject.Analytic.CircleLift

set_option maxHeartbeats 1000000

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex

/-!
# Analytic parameter rigidity (Section 7)

This file concerns the analytic rigidity step of the dossier.

We fully prove the self-contained analytic core (`analytic_modulus_one_of_pos_measure`):
a real-analytic `ℂ`-valued function on a connected open subset of `ℝ` whose
modulus equals `1` on a set of positive measure has modulus `1` everywhere on
the domain.  This is the first half of Lemma 7.2 and uses the identity theorem
for analytic functions.

The full Lemma 7.2 (`analytic_map_into_resonance_group_constant`) additionally
needs the change-of-variables/Lusin-`N` argument that the preimage of the
Haar-null resonance group under a nonconstant analytic map is null; that part
is recorded as a `sorry`.
-/

namespace CriticalMixedHRT

/-- The (multiplicative) resonance group `G_θ = {ζ ∈ S¹ : ζ^{qₙ} → 1}` as a
subset of `ℂ`. -/
def resonanceGroupC (q : ℕ → ℕ) : Set ℂ :=
  {ζ : ℂ | ‖ζ‖ = 1 ∧ Filter.Tendsto (fun n => ζ ^ (q n)) Filter.atTop (nhds 1)}

/-
**Analytic modulus rigidity (first half of Lemma 7.2).** If `H` is
real-analytic on a connected open set `U ⊆ ℝ` and `‖H‖ = 1` on a
positive-measure subset of `U`, then `‖H‖ = 1` on all of `U`.
-/
theorem analytic_modulus_one_of_pos_measure
    (U : Set ℝ) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U)
    (E : Set ℝ) (hEU : E ⊆ U)
    (hEpos : 0 < volume E)
    (hHE : ∀ s ∈ E, ‖H s‖ = 1) :
    ∀ s ∈ U, ‖H s‖ = 1 := by
  -- Since `E` has positive measure, it contains an accumulation point within itself.
  have h_acc : ∃ s₀ ∈ E, AccPt s₀ (𝓟 E) := by
    contrapose! hEpos;
    -- If `E` has no accumulation points, then `E` is discrete.
    have h_discrete : DiscreteTopology E := by
      refine' discreteTopology_iff_isOpen_singleton.mpr _;
      simp_all +decide [ AccPt ];
      simp_all +decide [ Filter.inf_principal_eq_bot ];
      intro x hx; rw [ Metric.isOpen_iff ] ; simp_all +decide [ Metric.mem_nhdsWithin_iff ] ;
      obtain ⟨ ε, ε_pos, hε ⟩ := hEpos x hx; exact ⟨ ε, ε_pos, fun y hy hyx => Classical.not_not.1 fun h => hε ⟨ hyx, h ⟩ hy ⟩ ;
    -- Since `E` is discrete, it is countable.
    have h_countable : Set.Countable E := by
      exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete;
    rw [ h_countable.measure_zero ];
  -- Since the norm squared of H is 1 on E, 'φ' must be identically zero on U by the previous lemma.
  have h_phi_zero : ∀ s ∈ U, ‖H s‖ ^ 2 = 1 := by
    have h_phi_zero : AnalyticOnNhd ℝ (fun s => ‖H s‖ ^ 2 - 1) U := by
      have h_phi_analytic : AnalyticOnNhd ℝ (fun s => starRingEnd ℂ (H s) * H s - 1) U := by
        apply_rules [ AnalyticOnNhd.sub, AnalyticOnNhd.mul, analyticOnNhd_const ];
        intro x hx;
        have h_conj_analytic : AnalyticAt ℝ (fun z : ℂ => starRingEnd ℂ z) (H x) := by
          apply_rules [ ContDiffAt.analyticAt ];
          exact ( Complex.conjCLE.contDiff.contDiffAt );
        exact h_conj_analytic.comp ( hH x hx );
      convert Complex.reCLM.comp_analyticOnNhd h_phi_analytic using 2 ; norm_num [ Complex.normSq, Complex.sq_norm ];
    have h_phi_zero : ∀ s ∈ U, ‖H s‖ ^ 2 - 1 = 0 := by
      have h_zero_on_E : ∀ s ∈ E, ‖H s‖ ^ 2 - 1 = 0 := by
        aesop
      obtain ⟨ s₀, hs₀₁, hs₀₂ ⟩ := h_acc; have := h_phi_zero.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc ( hEU hs₀₁ ) ?_; simp_all +decide ;
      · exact fun s hs => this hs;
      · rw [ accPt_iff_frequently ] at hs₀₂;
        rw [ Filter.frequently_iff ] at *;
        intro U hU; rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU with ⟨ V, hV₁, hV₂ ⟩ ; rcases hs₀₂ hV₁ with ⟨ x, hx₁, hx₂, hx₃ ⟩ ; use x; aesop;
    exact fun s hs => sub_eq_zero.mp ( h_phi_zero s hs );
  exact fun s hs => by nlinarith [ h_phi_zero s hs, norm_nonneg ( H s ) ] ;

/-
The zero set of the derivative of a non-constant analytic map on a
preconnected open set is null.
-/
theorem deriv_zero_set_null
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U)
    (hne : ∃ s ∈ U, ∃ t ∈ U, H s ≠ H t) :
    volume {s | s ∈ U ∧ deriv H s = 0} = 0 := by
  -- By the identity theorem for analytic functions, if `deriv H` is zero on a set with an accumulation point in `U`, then `deriv H` is identically zero on `U`.
  have h_identity : ∀ s₀ ∈ U, (∃ᶠ s in nhdsWithin s₀ ({s ∈ U | deriv H s = 0} \ {s₀}), True) → ∀ s ∈ U, deriv H s = 0 := by
    intro s₀ hs₀ hacc s hs;
    apply_rules [ hH.deriv.eqOn_zero_of_preconnected_of_frequently_eq_zero ];
    rw [ Metric.nhdsWithin_basis_ball.frequently_iff ] at *;
    exact fun ε hε => by obtain ⟨ x, hx₁, hx₂ ⟩ := hacc ε hε; exact ⟨ x, ⟨ hx₁.1, hx₁.2.2 ⟩, hx₁.2.1.2 ⟩ ;
  -- If `deriv H` is zero on a set with an accumulation point in `U`, then `deriv H` is identically zero on `U`.
  by_cases h_zero : ∃ s₀ ∈ U, ∃ᶠ s in nhdsWithin s₀ ({s ∈ U | deriv H s = 0} \ {s₀}), True;
  · obtain ⟨ s₀, hs₀₁, hs₀₂ ⟩ := h_zero;
    have h_const : ∀ s ∈ U, H s = H s₀ := by
      have := h_identity s₀ hs₀₁ hs₀₂;
      intro s hs;
      have h_const : ∀ a b, a ∈ U → b ∈ U → ∫ x in a..b, deriv H x = H b - H a := by
        intros a b ha hb;
        rw [ intervalIntegral.integral_deriv_eq_sub' ];
        · rfl;
        · exact fun x hx => hH.differentiableOn.differentiableAt ( hU.mem_nhds <| by cases Set.mem_uIcc.mp hx <;> [ exact hUc.Icc_subset ha hb ⟨ by linarith, by linarith ⟩ ; exact hUc.Icc_subset hb ha ⟨ by linarith, by linarith ⟩ ] );
        · exact ContinuousOn.congr ( show ContinuousOn ( fun _ => 0 ) _ from continuousOn_const ) fun x hx => this x <| by cases Set.mem_uIcc.mp hx <;> [ exact hUc.Icc_subset ha hb ‹_› ; exact hUc.Icc_subset hb ha ‹_› ] ;
      specialize h_const s₀ s hs₀₁ hs; rw [ intervalIntegral.integral_congr fun x hx => this x <| by cases ( Set.mem_uIcc.mp hx ) <;> [ exact hUc.Icc_subset hs₀₁ hs ⟨ by linarith, by linarith ⟩ ; exact hUc.Icc_subset hs hs₀₁ ⟨ by linarith, by linarith ⟩ ] ] at h_const; norm_num at h_const; linear_combination h_const.symm;
    grind;
  · -- If `deriv H` is zero on a set with no accumulation point in `U`, then `Z` is discrete.
    have h_discrete : DiscreteTopology {s ∈ U | deriv H s = 0} := by
      refine' singletons_open_iff_discrete.mp _;
      simp_all +decide [ Metric.isOpen_iff ];
      intro x hx hx'; specialize h_zero x hx; rw [ nhdsWithin, Filter.inf_principal_eq_bot ] at h_zero; simp_all +decide [ Metric.mem_nhds_iff ] ;
      obtain ⟨ ε, ε_pos, hε ⟩ := h_zero; exact ⟨ ε, ε_pos, fun a ha ha' ha'' => Classical.not_not.1 fun ha''' => hε ha'' ⟨ ⟨ ha, ha' ⟩, ha''' ⟩ ⟩ ;
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete |> fun h => h.measure_zero MeasureTheory.MeasureSpace.volume

/-
Local nullity of the resonance preimage: near a point where `deriv H ≠ 0`,
the set of parameters whose `H`-value lands in the resonance group is null.
-/
theorem local_resonance_preimage_null
    (q : ℕ → ℕ) (hq : Filter.Tendsto q Filter.atTop Filter.atTop)
    (U : Set ℝ) (hU : IsOpen U) (H : ℝ → ℂ)
    (hH : AnalyticOnNhd ℝ H U) (hHnorm : ∀ s ∈ U, ‖H s‖ = 1)
    (s₀ : ℝ) (hs₀ : s₀ ∈ U) (hderiv : deriv H s₀ ≠ 0) :
    ∃ a b : ℝ, s₀ ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U ∧
      volume {x | x ∈ Set.Ioo a b ∧ H x ∈ resonanceGroupC q} = 0 := by
  -- Apply `analytic_circle_local_lift` to obtain `a`, `b`, `y`, `y'`, and `c`.
  obtain ⟨a, b, y, y', c, hc, hs₀b, habU, hyderiv, hcyderiv, hExp⟩ := analytic_circle_local_lift U hU H hH hHnorm s₀ hs₀ hderiv;
  refine' ⟨ a, b, hs₀b, habU, _ ⟩;
  refine' MeasureTheory.measure_mono_null _ ( expanding_preimage_null a b y y' c hc hyderiv hcyderiv ( resonanceReal q ) ( resonanceReal_volume_zero q hq ) );
  simp +contextual [ resonanceGroupC, resonanceReal, hExp ];
  exact fun x hx₁ hx₂ hx₃ hx₄ => hx₄.congr fun n => by rw [ ← Complex.exp_nat_mul ] ; ring;

/-
**Lemma 7.2 (analytic map into the resonance group is constant).** A
real-analytic, nowhere-zero `H : U → ℂ` on a connected open interval whose
values lie in the Haar-null resonance group on a positive-measure set is
constant.
-/
theorem analytic_map_into_resonance_group_constant
    (q : ℕ → ℕ) (hq : Filter.Tendsto q Filter.atTop Filter.atTop)
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U) (hHne : ∀ s ∈ U, H s ≠ 0)
    (hpos : 0 < volume {s | s ∈ U ∧ H s ∈ resonanceGroupC q}) :
    ∀ s ∈ U, ∀ t ∈ U, H s = H t := by
  -- Unit modulus: let `E := {s | s ∈ U ∧ H s ∈ resonanceGroupC q}`. By `analytic_modulus_one_of_pos_measure U hUc H hH E (fun s hs => hs.1) hpos (fun s hs => hs.2.1)` we get `hHnorm : ∀ s ∈ U, ‖H s‖ = 1` (the `‖·‖ = 1` comes from membership in `resonanceGroupC`).
  have hHnorm : ∀ s ∈ U, ‖H s‖ = 1 := by
    apply analytic_modulus_one_of_pos_measure U hUc H hH {s | s ∈ U ∧ H s ∈ resonanceGroupC q} (fun s hs => hs.1) hpos (fun s hs => hs.2.1);
  by_contra hnonconst
  obtain ⟨s₀, hs₀⟩ : ∃ s ∈ U, ∃ t ∈ U, H s ≠ H t := by
    exact by push_neg at hnonconst; exact hnonconst;
  have hderiv_zero_set_null : volume {s | s ∈ U ∧ deriv H s = 0} = 0 := by
    apply deriv_zero_set_null U hU hUc H hH ⟨s₀, hs₀.left, hs₀.right.choose, hs₀.right.choose_spec.left, hs₀.right.choose_spec.right⟩
  set E₀ := {s | s ∈ U ∧ H s ∈ resonanceGroupC q ∧ deriv H s ≠ 0} with hE₀_def
  have hE₀_subset : E₀ ⊆ {s | s ∈ U ∧ deriv H s = 0}ᶜ := by
    exact fun x hx => fun hx' => hx.2.2 hx'.2
  have hE₀_measure_zero : volume E₀ ≤ 0 := by
    -- For each `s : ℝ` with `s ∈ E₀` we have `s ∈ U` and `deriv H s ≠ 0`, so `local_resonance_preimage_null q hq U hU H hH hHnorm s ⟨..⟩ ⟨..⟩` gives an open interval `Set.Ioo (a s) (b s)` with `s ∈ Set.Ioo (a s) (b s)`, `Set.Ioo (a s) (b s) ⊆ U`, and `volume {x | x ∈ Set.Ioo (a s) (b s) ∧ H x ∈ resonanceGroupC q} = 0`.
    have hE₀_cover : ∀ s ∈ E₀, ∃ a b : ℝ, s ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U ∧ volume {x | x ∈ Set.Ioo a b ∧ H x ∈ resonanceGroupC q} = 0 := by
      exact fun s hs => local_resonance_preimage_null q hq U hU H hH hHnorm s hs.1 hs.2.2;
    choose! a b h using hE₀_cover;
    -- Apply `TopologicalSpace.isOpen_iUnion_countable` to get a countable `T` with `⋃ i ∈ T, W i = ⋃ i, W i`.
    obtain ⟨T, hT_countable, hT_union⟩ : ∃ T : Set E₀, T.Countable ∧ ⋃ i ∈ T, Set.Ioo (a i) (b i) = ⋃ i : E₀, Set.Ioo (a i) (b i) := by
      have := TopologicalSpace.isOpen_iUnion_countable ( fun i : E₀ => Set.Ioo ( a i ) ( b i ) ) ( fun i => isOpen_Ioo ) ; aesop;
    -- Since `E₀ ⊆ ⋃ i ∈ T, W i`, we get `E₀ ⊆ ⋃ i ∈ T, {x | x ∈ W i ∧ H x ∈ resonanceGroupC q}`.
    have hE₀_subset_union : E₀ ⊆ ⋃ i ∈ T, {x | x ∈ Set.Ioo (a i) (b i) ∧ H x ∈ resonanceGroupC q} := by
      intro s hs; specialize hT_union; replace hT_union := Set.ext_iff.mp hT_union s; aesop;
    refine' le_trans ( MeasureTheory.measure_mono hE₀_subset_union ) _;
    simp +zetaDelta at *;
    exact MeasureTheory.measure_biUnion_null_iff hT_countable |>.2 fun i hi => h _ i.2.1 i.2.2.1 i.2.1 i.2.2.2 |>.2.2
  have hE_zero_measure : volume {s | s ∈ U ∧ H s ∈ resonanceGroupC q} ≤ 0 := by
    refine' le_trans ( MeasureTheory.measure_mono _ ) _;
    exact { s | s ∈ U ∧ deriv H s = 0 } ∪ E₀;
    · exact fun x hx => if hx' : deriv H x = 0 then Or.inl ⟨ hx.1, hx' ⟩ else Or.inr ⟨ hx.1, hx.2, hx' ⟩;
    · exact le_trans ( MeasureTheory.measure_union_le _ _ ) ( by aesop )
  exact absurd hE_zero_measure (by
  exact not_le_of_gt hpos)

end CriticalMixedHRT