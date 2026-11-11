import Mathlib
import RequestProject.PendingLemmas
import RequestProject.Rotation.PeriodicL2Translation

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Part B: zero real holonomy mean

Using the already-certified ergodic zero-mean lemma
`measurable_cocycle_holonomy_zero_mean`, we prove that the real part of the
average periodic logarithm vanishes, discharging the `hRe` hypothesis of
Stage 3A.

The route passes to the additive circle `AddCircle 1`:

* the modulus cocycle `‖h(x-θ)‖ = exp(Re(ell x))·‖h x‖` descends to a positive
  multiplicative cocycle over the irrational rotation;
* `measurable_cocycle_holonomy_zero_mean` gives `∫ Re(ell) = 0` on the circle;
* this transfers to `(∫ y in Ioc 0 1, ell y).re = 0` on the interval.
-/

namespace CriticalMixedHRT

/-
The rotation `y ↦ -↑θ + y` on `AddCircle 1` is ergodic when `θ` is
irrational.
-/
theorem addCircle_irrational_rotation_ergodic {θ : ℝ} (hθ : Irrational θ) :
    Ergodic (fun y : AddCircle (1 : ℝ) => -(θ : AddCircle (1 : ℝ)) + y) volume := by
  have h_addOrderOf_zero : addOrderOf (-θ : AddCircle (1 : ℝ)) = 0 := by
    rw [ addOrderOf_eq_zero_iff' ];
    intro n hn; simp +decide [ hn.ne', hθ.ne_zero ] ;
    erw [ QuotientAddGroup.eq_zero_iff ] ; norm_num [ hn.ne', hθ.ne_zero ];
    exact fun ⟨ k, hk ⟩ => hθ ⟨ k / n, by push_cast; rw [ div_eq_iff ( by positivity ) ] ; norm_num [ AddSubgroup.mem_zmultiples_iff ] at hk; linarith ⟩;
  convert AddCircle.ergodic_add_left ( p := 1 ) ( a := -θ ) using 1;
  aesop

/-
**Zero real holonomy mean.**

Let `θ` be irrational, `h : ℝ → ℂ` measurable and `1`-periodic and nonzero in
periodic `L²`, `b` a `1`-periodic non-vanishing cocycle with
`h(x-θ) = b x · h x`, and `ell` a measurable `1`-periodic logarithm of `b`
(`exp(ell x) = b x`) which is integrable over one period. Then
`(∫ y in Ioc 0 1, ell y).re = 0`.
-/
theorem periodic_log_integral_re_eq_zero_of_cocycle
    {θ : ℝ} (hθ : Irrational θ)
    (h b ell : ℝ → ℂ)
    (hh_meas : Measurable h) (hh_per : Function.Periodic h 1)
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hb_per : Function.Periodic b 1) (hb_ne : ∀ x, b x ≠ 0)
    (hell_meas : Measurable ell) (hell_per : Function.Periodic ell 1)
    (hell_int : Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (hcocycle : ∀ x, h (x - θ) = b x * h x) :
    (∫ y in Set.Ioc (0 : ℝ) 1, ell y).re = 0 := by
  -- By the periodicity of $h$, we have $\int_0^1 \ell(y) \, dy = \int_0^1 \ell(x) \, dx$.
  have h_periodic : ∫ y in Set.Ioc 0 1, Complex.re (ell y) = (∫ y in Set.Ioc 0 1, ell y).re := by
    convert integral_re hell_int using 1
  generalize_proofs at *; (
  -- By the periodicity of $h$, we have $\int_0^1 \ell(y) \, dy = \int_0^1 \ell(x) \, dx$. Hence, we can apply the result from the previous step.
  have h_periodic : ∫ y in Set.Ioc 0 1, Complex.re (ell y) = 0 := by
    have h_integrable : Integrable (fun y : AddCircle (1 : ℝ) => (AddCircle.liftIoc 1 0 ell y).re) (volume : Measure (AddCircle (1 : ℝ))) := by
      have h_integrable : MeasureTheory.Integrable (fun y : ℝ => ell y) (volume.restrict (Set.Ioc 0 1)) := by
        exact hell_int
      generalize_proofs at *; (
      have h_integrable : MeasureTheory.Integrable (fun y : ℝ => (ell y).re) (volume.restrict (Set.Ioc 0 1)) := by
        exact h_integrable.re
      generalize_proofs at *; (
      have h_integrable : MeasureTheory.Integrable (fun y : AddCircle (1 : ℝ) => (AddCircle.liftIoc 1 0 ell y).re) (Measure.map (fun y : ℝ => (y : AddCircle (1 : ℝ))) (volume.restrict (Set.Ioc 0 1))) := by
        rw [ MeasureTheory.integrable_map_measure ];
        · refine' h_integrable.congr _;
          filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by simp +decide [ periodic_descent_apply ell hell_per x ] ;
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.comp ( Complex.measurable_re ) _;
          exact Measurable.comp ( hell_meas ) ( measurable_subtype_coe ) |> Measurable.comp <| ( AddCircle.measurableEquivIoc 1 0 ).measurable;
        · exact Continuous.aemeasurable ( by continuity )
      generalize_proofs at *; (
      convert h_integrable using 1
      generalize_proofs at *; (
      convert ( AddCircle.measurePreserving_mk 1 0 ).map_eq.symm using 1;
      norm_num +zetaDelta at *))))
    have h_cocycle : ∀ᵐ y ∂(volume : Measure (AddCircle (1 : ℝ))), ‖AddCircle.liftIoc 1 0 h (-(θ : AddCircle (1 : ℝ)) + y)‖ = Real.exp ((AddCircle.liftIoc 1 0 ell y).re) * ‖AddCircle.liftIoc 1 0 h y‖ := by
      have h_cocycle : ∀ x : ℝ, ‖h (x - θ)‖ = Real.exp ((ell x).re) * ‖h x‖ := by
        simp_all +decide [ Complex.norm_exp ];
        exact fun x => Or.inl ( by rw [ ← hlog, Complex.norm_exp ] ) ;
      generalize_proofs at *; (
      have h_cocycle : ∀ x : ℝ, ‖AddCircle.liftIoc 1 0 h (-(θ : AddCircle (1 : ℝ)) + (x : AddCircle (1 : ℝ)))‖ = Real.exp ((AddCircle.liftIoc 1 0 ell (x : AddCircle (1 : ℝ))).re) * ‖AddCircle.liftIoc 1 0 h (x : AddCircle (1 : ℝ))‖ := by
        intro x; convert h_cocycle x using 1 ;
        · convert congr_arg Norm.norm ( CriticalMixedHRT.periodic_descent_apply h hh_per ( -θ + x ) ) using 1 ; ring!;
        · rw [ periodic_descent_apply h hh_per x, periodic_descent_apply ell hell_per x ]
      generalize_proofs at *; (
      filter_upwards [ ] with y using by rcases QuotientAddGroup.mk_surjective y with ⟨ x, rfl ⟩ ; exact h_cocycle x;))
    generalize_proofs at *; (
    have h_not_ae_zero : ¬ (fun y : AddCircle (1 : ℝ) => ‖AddCircle.liftIoc 1 0 h y‖) =ᵐ[volume] 0 := by
      intro H
      have h_zero : eLpNorm (AddCircle.liftIoc 1 0 h) 2 (volume : Measure (AddCircle (1 : ℝ))) = 0 := by
        rw [ eLpNorm_eq_lintegral_rpow_enorm_toReal ] <;> norm_num [ H ];
        rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ] ; filter_upwards [ H ] with x hx ; aesop;
      generalize_proofs at *; (
      have h_zero : eLpNorm (AddCircle.liftIoc 1 0 h) 2 (volume : Measure (AddCircle (1 : ℝ))) = eLpNorm h 2 (volume.restrict (Set.Ioc 0 1)) := by
        have h_zero : eLpNorm (AddCircle.liftIoc 1 0 h) 2 (volume : Measure (AddCircle (1 : ℝ))) = eLpNorm (AddCircle.liftIoc 1 0 h ∘ (fun x : ℝ => (x : AddCircle (1 : ℝ)))) 2 (volume.restrict (Set.Ioc 0 1)) := by
          rw [ ← MeasureTheory.eLpNorm_comp_measurePreserving ];
          · exact MeasureTheory.AEStronglyMeasurable.congr ( MeasureTheory.aestronglyMeasurable_const ) ( by filter_upwards [ H ] with y hy; aesop );
          · convert AddCircle.measurePreserving_mk 1 0 using 1;
            norm_num +zetaDelta at *
        generalize_proofs at *; (
        convert h_zero using 1
        generalize_proofs at *; (
        congr! 1
        generalize_proofs at *; (
        exact funext fun x => by simpa using periodic_descent_apply h hh_per x |> Eq.symm;)))
      generalize_proofs at *; (
      aesop))
    generalize_proofs at *; (
    convert measurable_cocycle_holonomy_zero_mean ( volume : Measure ( AddCircle ( 1 : ℝ ) ) ) ( fun y => - ( θ : AddCircle ( 1 : ℝ ) ) + y ) _ _ ( fun y => ( AddCircle.liftIoc 1 0 ell y ).re ) h_integrable ( fun y => ‖AddCircle.liftIoc 1 0 h y‖ ) _ _ h_not_ae_zero _ using 1
    generalize_proofs at *; (
    convert AddCircle.integral_preimage ( 1 : ℝ ) 0 ( fun y => ( AddCircle.liftIoc 1 0 ell y ).re ) using 1 ; norm_num [ periodic_descent_apply ];
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ periodic_descent_apply ell hell_per x ] ;);
    exact ⟨ by simp +decide [ AddCircle.measure_univ ] ⟩
    all_goals generalize_proofs at *; try exact fun _ => norm_nonneg _;
    · convert MeasureTheory.measurePreserving_add_left volume ( -θ : AddCircle ( 1 : ℝ ) ) using 1;
    · convert addCircle_irrational_rotation_ergodic hθ using 1;
    · refine' Measurable.norm _;
      convert hh_meas.comp ( show Measurable ( fun x : AddCircle ( 1 : ℝ ) => ( AddCircle.equivIoc 1 0 x : ℝ ) ) from ?_ ) using 1
      generalize_proofs at *; (
      exact measurable_subtype_coe.comp ( AddCircle.measurableEquivIoc 1 0 |> MeasurableEquiv.measurable ));
    · exact h_cocycle))
  generalize_proofs at *; (
  linarith))

end CriticalMixedHRT