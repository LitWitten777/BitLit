import Mathlib

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology

/-!
# Pending lemmas (faithful statements, proofs deferred)

This file records faithful Lean statements of dossier lemmas whose proofs
require analytic/ergodic infrastructure that is **not** available in the
current Mathlib and would have to be built from scratch.  They are recorded
with `sorry` so the certification interface is explicit.

* `measurable_cocycle_holonomy_zero_mean` — Lemma 6.1 (`M1`).  The proof needs
  the **pointwise Birkhoff ergodic theorem**, which Mathlib does not currently
  provide (only the mean ergodic theorem is available).

Other lemmas of the dossier (Lemma 6.2 measurable winding obstruction,
Lemma 6.4 uniform return sums, Lemma 6.5 holonomy quantization) depend on the
**Denjoy–Koksma inequality**, also absent from Mathlib; Lemmas N1–N3 / the
main reduction depend on the **Zak transform** unitarity theory; and the local
Laurent holonomy certificate (`C1`) depends on a winding-number / continuous
logarithm package.  These are documented in `STATUS.md` rather than given
possibly-unfaithful placeholder statements.
-/

namespace CriticalMixedHRT

/-
**Lemma 6.1 (`M1`): measurable zero-mean multiplicative cocycle.**

Let `(X, μ, T)` be an ergodic probability-preserving system, `φ ∈ L¹(X)`, and
`h : X → ℝ` measurable, nonnegative, and not a.e. zero, with the multiplicative
cocycle relation `h(Tx) = e^{φ(x)} h(x)` a.e.  Then `∫ φ dμ = 0`.

The proof requires the pointwise Birkhoff ergodic theorem (not in Mathlib).
-/
theorem measurable_cocycle_holonomy_zero_mean
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (hErg : Ergodic T μ)
    (φ : X → ℝ) (hφ : Integrable φ μ)
    (h : X → ℝ) (hmeas : Measurable h) (hnonneg : ∀ x, 0 ≤ h x)
    (hpos : ¬ (h =ᵐ[μ] 0))
    (hcocycle : ∀ᵐ x ∂μ, h (T x) = Real.exp (φ x) * h x) :
    ∫ x, φ x ∂μ = 0 := by
  -- Set g x = Real.log (h x). The set {x | h(Tx) = 0} is also null (it is T⁻¹' Z, and hT.measure_preimage of a null measurable set is null). For a.e. x we have h x > 0 and h(Tx) > 0; taking logs of h(Tx) = exp(φ x) * h x gives g(Tx) = φ x + g x for a.e. x (use Real.log_mul, Real.log_exp).
  set g : X → ℝ := fun x => Real.log (h x)
  have hg : ∀ᵐ x ∂μ, g (T x) = φ x + g x := by
    have h_pos : ∀ᵐ x ∂μ, 0 < h x := by
      have h_pos : ∀ᵐ x ∂μ, h x = 0 → h (T x) = 0 := by
        filter_upwards [ hcocycle ] with x hx hx' using by simp +decide [ hx', hx ] ;
      have h_pos : μ {x | h x = 0} = 0 ∨ μ {x | h x = 0} = 1 := by
        have h_pos : MeasureTheory.MeasurePreserving T μ μ ∧ QuasiErgodic T μ := by
          exact ⟨ hT, hErg.quasiErgodic ⟩;
        have := h_pos.2.ae_empty_or_univ₀ ( show NullMeasurableSet { x | h x = 0 } μ from hmeas ( MeasurableSingletonClass.measurableSet_singleton 0 ) |> MeasurableSet.nullMeasurableSet ) ?_;
        · cases' this with h h <;> [ left; right ] <;> rw [ MeasureTheory.measure_congr h ] <;> simp +decide [ MeasureTheory.IsProbabilityMeasure.measure_univ ];
        · have h_pos : ∀ᵐ x ∂μ, h (T x) = 0 → h x = 0 := by
            filter_upwards [ hcocycle ] with x hx using fun hx' => by simpa [ hx', Real.exp_ne_zero ] using hx.symm;
          filter_upwards [ ‹∀ᵐ x ∂μ, h x = 0 → h ( T x ) = 0›, h_pos ] with x hx₁ hx₂ using by aesop;
      cases' h_pos with h_pos h_pos;
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_pos ] with x hx using lt_of_le_of_ne ( hnonneg x ) ( Ne.symm hx );
      · have h_pos : μ {x | h x ≠ 0} = 0 := by
          rw [ show { x | ¬h x = 0 } = ( Set.univ \ { x | h x = 0 } ) by ext; simp +decide, MeasureTheory.measure_diff ] <;> norm_num [ h_pos ];
          exact hmeas ( MeasurableSingletonClass.measurableSet_singleton 0 ) |> MeasurableSet.nullMeasurableSet;
        exact False.elim <| hpos <| MeasureTheory.ae_iff.mpr h_pos;
    filter_upwards [ hcocycle, h_pos ] with x hx hx' using by rw [ show g ( T x ) = Real.log ( Real.exp ( φ x ) * h x ) by rw [ ← hx ], Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ;
  -- Applying the lemma of dominated convergence to the sequence $χ_N(g(T(x))) - χ_N(g(x))$ with $N \to \infty$.
  have h_dominated : Filter.Tendsto (fun N : ℕ => ∫ x, (max (-N : ℝ) (min N (g (T x)))) - (max (-N : ℝ) (min N (g x))) ∂μ) Filter.atTop (nhds (∫ x, φ x ∂μ)) := by
    refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => |φ x|;
    · intro n
      have h_measurable : Measurable (fun x => max (-n : ℝ) (min n (g x))) := by
        exact Measurable.max measurable_const ( Measurable.min measurable_const ( Measurable.log hmeas ) )
      have h_measurable_T : Measurable (fun x => max (-n : ℝ) (min n (g (T x)))) := by
        exact h_measurable.comp hT.measurable
      exact (h_measurable_T.aestronglyMeasurable.sub h_measurable.aestronglyMeasurable);
    · exact hφ.abs;
    · intro n; filter_upwards [ hg ] with x hx; simp +decide [ hx ] ;
      cases abs_cases ( φ x ) <;> cases abs_cases ( max ( -n : ℝ ) ( min ( n : ℝ ) ( φ x + g x ) ) - max ( -n : ℝ ) ( min ( n : ℝ ) ( g x ) ) ) <;> cases max_cases ( -n : ℝ ) ( min ( n : ℝ ) ( φ x + g x ) ) <;> cases max_cases ( -n : ℝ ) ( min ( n : ℝ ) ( g x ) ) <;> cases min_cases ( n : ℝ ) ( φ x + g x ) <;> cases min_cases ( n : ℝ ) ( g x ) <;> linarith;
    · filter_upwards [ hg ] with x hx;
      exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop ⌈|g ( T x )|⌉₊, Filter.eventually_gt_atTop ⌈|g x|⌉₊ ] with n hn hn'; rw [ max_eq_right, max_eq_right ] <;> cases abs_cases ( g ( T x ) ) <;> cases abs_cases ( g x ) <;> linarith [ Nat.le_ceil ( |g ( T x )| ), Nat.le_ceil ( |g x| ), show ( n : ℝ ) ≥ ⌈|g ( T x )|⌉₊ + 1 by exact_mod_cast hn, show ( n : ℝ ) ≥ ⌈|g x|⌉₊ + 1 by exact_mod_cast hn', min_eq_right ( show ( n : ℝ ) ≥ g ( T x ) by linarith [ Nat.le_ceil ( |g ( T x )| ), Nat.le_ceil ( |g x| ), show ( n : ℝ ) ≥ ⌈|g ( T x )|⌉₊ + 1 by exact_mod_cast hn ] ), min_eq_right ( show ( n : ℝ ) ≥ g x by linarith [ Nat.le_ceil ( |g ( T x )| ), Nat.le_ceil ( |g x| ), show ( n : ℝ ) ≥ ⌈|g x|⌉₊ + 1 by exact_mod_cast hn' ] ) ] );
  -- By measure preservation, $\int \chi_N(g(T(x))) \, d\mu = \int \chi_N(g(x)) \, d\mu$.
  have h_measure_preservation : ∀ N : ℕ, ∫ x, max (-N : ℝ) (min N (g (T x))) ∂μ = ∫ x, max (-N : ℝ) (min N (g x)) ∂μ := by
    intro N
    have h_measure_preservation : ∫ x, max (-N : ℝ) (min N (g (T x))) ∂μ = ∫ x, max (-N : ℝ) (min N (g x)) ∂(MeasureTheory.Measure.map T μ) := by
      rw [ MeasureTheory.integral_map ];
      · exact hT.measurable.aemeasurable;
      · exact Measurable.aestronglyMeasurable ( by measurability );
    rw [ h_measure_preservation, hT.map_eq ];
  refine' tendsto_nhds_unique h_dominated ( tendsto_const_nhds.congr' _ );
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN;
  rw [ MeasureTheory.integral_sub, h_measure_preservation N, sub_self ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => N;
    · norm_num;
    · refine' Measurable.aestronglyMeasurable _;
      exact Measurable.max measurable_const ( Measurable.min measurable_const ( Measurable.log ( hmeas.comp hT.measurable ) ) );
    · filter_upwards [ ] with x using abs_le.mpr ⟨ by cases max_cases ( -N : ℝ ) ( min ( N : ℝ ) ( g ( T x ) ) ) <;> cases min_cases ( N : ℝ ) ( g ( T x ) ) <;> linarith, by cases max_cases ( -N : ℝ ) ( min ( N : ℝ ) ( g ( T x ) ) ) <;> cases min_cases ( N : ℝ ) ( g ( T x ) ) <;> linarith ⟩;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => N;
    · norm_num;
    · exact Measurable.aestronglyMeasurable ( by measurability );
    · filter_upwards [ ] with x using abs_le.mpr ⟨ by cases max_cases ( -N : ℝ ) ( min ( N : ℝ ) ( g x ) ) <;> cases min_cases ( N : ℝ ) ( g x ) <;> linarith, by cases max_cases ( -N : ℝ ) ( min ( N : ℝ ) ( g x ) ) <;> cases min_cases ( N : ℝ ) ( g x ) <;> linarith ⟩

end CriticalMixedHRT