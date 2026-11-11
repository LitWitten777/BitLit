import Mathlib
import RequestProject.Zak.ConcreteZakDense
import RequestProject.Zak.ConcreteZakPlancherel
import RequestProject.HRT.FiberOperator

open scoped Classical BigOperators Real ENNReal
open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Stage 6B — Fubini / fibre-density regularity for the concrete Zak transform

This module discharges, *for the concrete dense-class Zak transform*
`concreteZakDense`, the two regularity facts that the abstract
`active_set_positive_measure_of_nonzero_window`
(`RequestProject/HRT/FiberOperator.lean`) took as explicit hypotheses:

* `concrete_fiberDensity_integrable` — interval-integrability on `[0,1]` of the
  fibre density `s ↦ ∫₀¹ ‖Zf(x,s)‖² dx`;
* `concrete_active_set_positive_measure` — for a nonzero window the active fibre
  set has positive Lebesgue measure.

Both hold for the dense class of bounded, measurable windows supported in a
bounded interval `[0,N)` (which is dense in `L²(ℝ)`).  The fibre density is
bounded (by `(N·C)²`) and measurable, hence interval-integrable; the total fibre
mass is `∫_ℝ ‖f‖²` by `concreteZakDense_plancherel`, so the nonnegative density
cannot vanish a.e. when `f` is nonzero.

This is the concrete realization of the Fubini/fibre-density regularity folded
into the `L2ZakModel` interface (Blocker `ZAK_MODEL_INTERFACE`).
-/

namespace CriticalMixedHRT

/-
**Fibre-density interval-integrability (concrete model).**
For a bounded measurable window `f` supported in `[0,N)`, the fibre density
`s ↦ ∫₀¹ ‖Zf(x,s)‖² dx` is interval-integrable on `[0,1]`.
-/
theorem concrete_fiberDensity_integrable (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    IntervalIntegrable (fiberDensity (concreteZakDense f)) volume 0 1 := by
  obtain ⟨ C, hC ⟩ := hbdd;
  have h_bounded : ∀ s, (fiberDensity (concreteZakDense f)) s ≤ (N * C) ^ 2 := by
    intro s
    have h_inner : ∀ x ∈ Set.Ico (0:ℝ) 1, ‖concreteZakDense f x s‖ ^ 2 ≤ (N * C) ^ 2 := by
      intro x hx
      have h_sum : ‖concreteZakDense f x s‖ ≤ ∑ k ∈ Finset.Ico (0 : ℤ) N, ‖f (x + k)‖ := by
        rw [ concreteZakDense_eq_finsum_of_supp N f hsupp x hx s ];
        exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun _ _ => by simp +decide [ Complex.norm_exp ] );
      exact pow_le_pow_left₀ ( norm_nonneg _ ) ( h_sum.trans <| le_trans ( Finset.sum_le_sum fun _ _ => hC _ ) <| by simp +decide [ mul_comm ] ) _;
    refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
    refine' fun x => ( N * C ) ^ 2;
    · norm_num;
    · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => ( N * C ) ^ 2;
      · fun_prop;
      · refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
        refine' fun x => ‖∑ k ∈ Finset.Ico ( 0 : ℤ ) N, f ( x + k ) * Complex.exp ( -2 * Real.pi * Complex.I * k * s )‖ ^ 2;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by rw [ concreteZakDense_eq_finsum_of_supp N f hsupp x ⟨ hx.1.le, hx.2 ⟩ s ] ;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by simpa using h_inner x ⟨ hx.1.le, hx.2 ⟩ ;
    · exact IntervalIntegrable.symm intervalIntegral.intervalIntegrable_const
    · intro x hx; cases hx.2.eq_or_lt <;> simp_all +decide [ Set.Ico ] ;
      have := concreteZakDense_quasiperiodic_x f 0 s; simp_all +decide [ concreteZakDense ] ;
      have := h_inner 0 ( by norm_num ) ( by norm_num ) ; simp_all +decide [ Complex.norm_exp ] ;
    · norm_num;
  apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun s => ( N * C ) ^ 2;
  · norm_num;
    fun_prop;
  · refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
    refine' fun s => ∫ x in Set.Icc 0 1, ‖∑ k ∈ Finset.Ico ( 0 : ℤ ) ( N : ℤ ), f ( x + k ) * Complex.exp ( - ( 2 * Real.pi * Complex.I * k * s ) )‖ ^ 2;
    · refine' MeasureTheory.StronglyMeasurable.aestronglyMeasurable _;
      refine' MeasureTheory.StronglyMeasurable.integral_prod_right _;
      fun_prop;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs;
      rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one ];
      convert intervalIntegral.integral_congr_ae _;
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton 1 ) ] with x hx ; intro hx' ; rw [ concreteZakDense_eq_finsum_of_supp ] ; aesop;
      · exact hsupp;
      · grind;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs using by rw [ Real.norm_of_nonneg ( fiberDensity_nonneg _ _ ) ] ; exact h_bounded s;

/-
**Active-set positivity (concrete model).**
For a bounded measurable window `f` supported in `[0,N)` with nonzero `L²`-mass,
the active fibre set has positive Lebesgue measure.
-/
theorem concrete_active_set_positive_measure (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hf : 0 < ∫ t, ‖f t‖ ^ 2) :
    0 < MeasureTheory.volume (activeSet (concreteZakDense f) ∩ Set.Ioc (0:ℝ) 1) := by
  have h_integral_pos : 0 < ∫ s in (0:ℝ)..1, ∫ x in (0:ℝ)..1, ‖concreteZakDense f x s‖ ^ 2 := by
    rw [ concreteZakDense_plancherel N f hsupp hmeas hbdd ] ; linarith;
  convert intervalIntegral.integral_pos_iff_support_of_nonneg_ae _ _ |>.1 h_integral_pos using 1;
  · simp +decide [ activeSet, Function.support ];
    congr! 2;
    exact Set.ext fun x => and_congr ⟨ fun hx => ne_of_gt hx, fun hx => lt_of_le_of_ne ( fiberDensity_nonneg _ _ ) ( Ne.symm hx ) ⟩ Iff.rfl;
  · exact Filter.Eventually.of_forall fun x => intervalIntegral.integral_nonneg ( by norm_num ) fun y hy => sq_nonneg _;
  · contrapose! h_integral_pos; rw [ intervalIntegral.integral_undef h_integral_pos ] ;

end CriticalMixedHRT