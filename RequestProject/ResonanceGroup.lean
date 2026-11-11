import Mathlib

open scoped Classical BigOperators
open MeasureTheory Filter Topology

/-!
# The resonance group is Haar-null (Lemma 6.6)

For an irrational rotation with continued-fraction denominators `qₙ`, the
*resonance group* is `G_θ = {ζ ∈ S¹ : ζ^{qₙ} → 1}`.  In the additive circle
model `AddCircle 1 ≅ ℝ/ℤ` (via `x ↦ e^{2πix}`), this is
`{x : ℝ/ℤ : qₙ • x → 0}`.

We prove it has Haar measure zero, by a clean Fourier-coefficient argument
(cleaner than the paper's open-subgroup route, and not even needing the
subgroup structure):

If `μ(G) > 0`, then by dominated convergence
`μ(G) = lim_n ∫_G e(qₙ x) dx`, and `∫_G e(qₙ x) dx` is (up to sign of index)
the Fourier coefficient of the indicator `1_G` at frequency `qₙ`.  Since
`1_G ∈ L²`, its Fourier coefficients are square-summable (`hasSum_sq_fourierCoeff`),
hence tend to `0` along `qₙ → ∞`.  So `μ(G) = 0`.
-/

namespace CriticalMixedHRT

/-
**Lemma 6.6.** The resonance set `{x : ℝ/ℤ : qₙ • x → 0}` (the additive
model of `G_θ = {ζ : ζ^{qₙ} → 1}`) has Haar measure zero, whenever `qₙ → ∞`.
-/
theorem resonance_group_haar_measure_zero
    (q : ℕ → ℕ) (hq : Filter.Tendsto q Filter.atTop Filter.atTop) :
    MeasureTheory.volume
      {x : AddCircle (1 : ℝ) |
        Filter.Tendsto (fun n => (q n) • x) Filter.atTop (nhds 0)} = 0 := by
  -- Let $G = {x : AddCircle 1 | Tendsto (fun n => (q n) • x) atTop (𝓝 0)}$. We show $volume G = 0$.
  set G : Set (AddCircle (1 : ℝ)) := {x | Tendsto (fun n => (q n) • x) atTop (𝓝 0)}
  have hG_meas : MeasurableSet G := by
    refine' measurableSet_tendsto _ _;
    fun_prop;
  -- By dominated convergence,
  have h_dom_conv : Filter.Tendsto (fun n => ∫ x, (if x ∈ G then (1 : ℂ) else 0) * fourier (q n) x ∂(volume)) Filter.atTop (nhds (∫ x, (if x ∈ G then (1 : ℂ) else 0) ∂(volume))) := by
    refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => 1;
    · exact fun n => Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.ite hG_meas measurable_const measurable_const ) ( by exact Continuous.measurable ( by continuity ) ) );
    · norm_num;
    · intro n; filter_upwards [ ] with x; split_ifs <;> norm_num [ Complex.norm_exp ] ;
    · refine' MeasureTheory.ae_of_all _ _;
      intro x; split_ifs <;> simp_all +decide [ fourier ] ;
      convert Filter.Tendsto.comp ( show Filter.Tendsto ( fun y : AddCircle 1 => ( y.toCircle : ℂ ) ) ( 𝓝 0 ) ( 𝓝 1 ) from ?_ ) ‹Tendsto ( fun n => q n • x ) atTop ( 𝓝 0 ) › using 2;
      convert Continuous.tendsto _ _ <;> norm_num [ Continuous ];
      fun_prop;
  -- The Fourier coefficients tend to zero along $(q_n)$.
  have h_fourier_zero : Filter.Tendsto (fun n => fourierCoeff (MeasureTheory.indicatorConstLp 2 hG_meas (MeasureTheory.measure_ne_top _ G) 1 : ↥(Lp ℂ 2 (volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))) (-(q n : ℤ))) Filter.atTop (nhds 0) := by
    have h_fourier_zero : Summable (fun i : ℤ => ‖fourierCoeff (MeasureTheory.indicatorConstLp 2 hG_meas (MeasureTheory.measure_ne_top _ G) 1 : ↥(Lp ℂ 2 (volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))) i‖ ^ 2) := by
      have := @hasSum_sq_fourierCoeff;
      convert this ( MeasureTheory.indicatorConstLp 2 hG_meas ( MeasureTheory.measure_ne_top _ G ) 1 : ↥ ( Lp ℂ 2 AddCircle.haarAddCircle ) ) |> HasSum.summable using 1;
      congr!;
      ext; simp [volume];
      congr! 1;
    have h_fourier_zero : Filter.Tendsto (fun i : ℤ => fourierCoeff (MeasureTheory.indicatorConstLp 2 hG_meas (MeasureTheory.measure_ne_top _ G) 1 : ↥(Lp ℂ 2 (volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))) i) (Filter.cofinite) (nhds 0) := by
      have := h_fourier_zero.tendsto_cofinite_zero;
      exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa [ Real.sqrt_sq_eq_abs ] using this.sqrt );
    refine' h_fourier_zero.comp _;
    simp +decide [ Filter.tendsto_def ];
    exact fun s x hx y hy => ⟨ Nat.find ( Filter.eventually_atTop.mp ( hq.eventually_ge_atTop ( Int.toNat ( -x ) ) ) ), fun n hn => hx _ <| by linarith [ Nat.find_spec ( Filter.eventually_atTop.mp ( hq.eventually_ge_atTop ( Int.toNat ( -x ) ) ) ) n hn, Int.self_le_toNat ( -x ) ] ⟩;
  -- By definition of Fourier coefficients, we have
  have h_fourier_def : ∀ n, ∫ x, (if x ∈ G then (1 : ℂ) else 0) * fourier (q n) x ∂(volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) = fourierCoeff (MeasureTheory.indicatorConstLp 2 hG_meas (MeasureTheory.measure_ne_top _ G) 1 : ↥(Lp ℂ 2 (volume : MeasureTheory.Measure (AddCircle (1 : ℝ))))) (-(q n : ℤ)) := by
    intro n; simp +decide [ fourierCoeff ] ; ring_nf;
    rw [ MeasureTheory.integral_congr_ae ];
    convert rfl;
    · ext; simp [volume];
      convert rfl;
    · filter_upwards [ AEEqFun.coeFn_mk ( G.indicator fun x => 1 : AddCircle ( 1 : ℝ ) → ℂ ) ( by exact Measurable.aestronglyMeasurable ( by exact Measurable.indicator measurable_const hG_meas ) ) ] with x hx ; aesop;
  convert tendsto_nhds_unique h_dom_conv ( h_fourier_zero.congr fun n => h_fourier_def n ▸ rfl ) using 1;
  erw [ MeasureTheory.integral_indicator hG_meas ] ; norm_num;
  rw [ MeasureTheory.measureReal_def ];
  rw [ ENNReal.toReal_eq_zero_iff ] ; norm_num

end CriticalMixedHRT