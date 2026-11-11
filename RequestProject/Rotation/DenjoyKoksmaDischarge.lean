import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.Rotation.ConcreteVariation
import RequestProject.Rotation.C1VariationApprox
import RequestProject.Rotation.ConcreteDenjoyKoksma
import RequestProject.Rotation.C1UniformReturnSums

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Denjoy–Koksma discharge run

The Stage 2B return data `DenjoyKoksmaReturnData θ` carries the Denjoy–Koksma
estimate as a field, and `DenjoyKoksmaReturnData.ofConcrete` instantiates it from
the *complex-valued* Denjoy–Koksma inequality

```
∀ g : ℝ → ℂ, ConcreteHasBV g → periodMean g = 0 →
  ∀ (n : ℕ) (x : ℝ),
    ‖∑ j ∈ Finset.range (R.q n), g (x - j θ)‖ ≤ concreteVariation g
```

This module performs a genuine, no-`sorry` **reduction** of that complex
estimate to the standard **real-valued** Denjoy–Koksma inequality (with the same
constant `1`), packaged in the explicit hypothesis structure
`RealDenjoyKoksma θ` (this is a `structure`, *not* an axiom).

The reduction is the elementary "optimal direction" projection: for a fixed
complex Birkhoff sum `S`, projecting `g` onto the unit phase `w = conj S / ‖S‖`
turns the complex sum norm `‖S‖` into the real sum `∑ (w · g)·re`, whose real
variation is `≤ concreteVariation g` (the projection `z ↦ (w·z).re` is
`1`-Lipschitz) and whose real mean vanishes. The real Denjoy–Koksma inequality
then yields `‖S‖ ≤ concreteVariation g`.

Consequently the remaining blocker `DK_VARIATION_INTERFACE` is reduced from the
complex estimate to the canonical real Denjoy–Koksma theorem
(`RealDenjoyKoksma.dk_real`), which is the standard formulation found in the
literature (Kuipers–Niederreiter / Herman). The reduction itself is fully
proved here.
-/

namespace CriticalMixedHRT

/-- Concrete bounded variation for a **real-valued** function over one period. -/
def ConcreteHasBVReal (h : ℝ → ℝ) : Prop :=
  BoundedVariationOn h (Set.Icc (0 : ℝ) 1)

/-- Concrete real total variation of a real-valued function over one period. -/
noncomputable def concreteVariationReal (h : ℝ → ℝ) : ℝ :=
  (eVariationOn h (Set.Icc (0 : ℝ) 1)).toReal

/-- Concrete period mean of a real-valued function. -/
noncomputable def periodMeanReal (h : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, h x

/-- The real total variation is nonnegative. -/
theorem concreteVariationReal_nonneg (h : ℝ → ℝ) : 0 ≤ concreteVariationReal h :=
  ENNReal.toReal_nonneg

/-- The phase projection of a complex function: `t ↦ (w · g t).re`. -/
noncomputable def projReal (w : ℂ) (g : ℝ → ℂ) : ℝ → ℝ := fun t => (w * g t).re

/-- **The standard real Denjoy–Koksma theorem, as an explicit hypothesis
structure** (not an axiom).

Bundles the continued-fraction return data with the divergence of the return
denominators and the real-valued Denjoy–Koksma inequality with constant `1`.
This is exactly the classical statement: for an irrational rotation by `θ` with
continued-fraction denominators `q n`, every real bounded-variation, zero-mean
function has its full-period Birkhoff sums bounded by its total variation. -/
structure RealDenjoyKoksma (θ : ℝ) extends RotationReturnData θ where
  /-- The return denominators diverge to infinity. -/
  q_tendsto : Tendsto toRotationReturnData.q atTop atTop
  /-- The real Denjoy–Koksma inequality (constant `1`). -/
  dk_real :
    ∀ h : ℝ → ℝ, ConcreteHasBVReal h → periodMeanReal h = 0 →
      ∀ (n : ℕ) (x : ℝ),
        |∑ j ∈ Finset.range (toRotationReturnData.q n), h (x - (j : ℝ) * θ)|
          ≤ concreteVariationReal h

/-
A complex bounded-variation function is integrable over one period.
-/
theorem concreteHasBV_integrableOn {g : ℝ → ℂ} (hg : ConcreteHasBV g) :
    IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume := by
  have h_bounded : ∃ C, ∀ t ∈ Set.Icc 0 1, ‖g t‖ ≤ C := by
    have h_bounded : BoundedVariationOn g (Set.Icc 0 1) := by
      exact hg
    generalize_proofs at *; (
    use ‖g 0‖ + ENNReal.toReal ( eVariationOn g ( Set.Icc 0 1 ) ) ; intro t ht; have := h_bounded.dist_le ht ( Set.left_mem_Icc.mpr zero_le_one ) ; simp_all +decide [ dist_eq_norm ] ; (
    simpa using norm_add_le ( g 0 ) ( g t - g 0 ) |> le_trans <| by linarith;);)
  generalize_proofs at *; (
  have h_measurable : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
    have h_measurable : MeasureTheory.AEStronglyMeasurable (fun t => Complex.re (g t)) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) ∧ MeasureTheory.AEStronglyMeasurable (fun t => Complex.im (g t)) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
      have h_measurable : LocallyBoundedVariationOn (fun t => Complex.re (g t)) (Set.Icc 0 1) ∧ LocallyBoundedVariationOn (fun t => Complex.im (g t)) (Set.Icc 0 1) := by
        have h_measurable : eVariationOn (fun t => Complex.re (g t)) (Set.Icc 0 1) ≠ ⊤ ∧ eVariationOn (fun t => Complex.im (g t)) (Set.Icc 0 1) ≠ ⊤ := by
          have h_measurable : eVariationOn (fun t => Complex.re (g t)) (Set.Icc 0 1) ≤ eVariationOn g (Set.Icc 0 1) ∧ eVariationOn (fun t => Complex.im (g t)) (Set.Icc 0 1) ≤ eVariationOn g (Set.Icc 0 1) := by
            constructor <;> refine' iSup_le fun p => _ <;> simp +decide [ eVariationOn ] at *;
            · refine' le_trans _ ( le_ciSup _ p ) <;> norm_num [ edist_dist ];
              exact Finset.sum_le_sum fun _ _ => ENNReal.ofReal_le_ofReal ( by simpa [ dist_eq_norm ] using Complex.abs_re_le_norm ( g ( p.2.val ( ‹_› + 1 ) ) - g ( p.2.val ‹_› ) ) ) ;
            · refine' le_trans _ ( le_ciSup _ p ) <;> norm_num [ edist_dist ];
              exact Finset.sum_le_sum fun _ _ => ENNReal.ofReal_le_ofReal <| by simpa [ dist_eq_norm ] using Complex.abs_im_le_norm ( g ( p.2.val ( ‹_› + 1 ) ) - g ( p.2.val ‹_› ) ) ;
          generalize_proofs at *; (
          exact ⟨ ne_of_lt ( lt_of_le_of_lt h_measurable.1 ( lt_top_iff_ne_top.mpr ‹_› ) ), ne_of_lt ( lt_of_le_of_lt h_measurable.2 ( lt_top_iff_ne_top.mpr ‹_› ) ) ⟩)
        generalize_proofs at *; (
        simp_all +decide [ LocallyBoundedVariationOn ];
        exact ⟨ fun a b ha hb ha' hb' => ne_of_lt <| lt_of_le_of_lt ( eVariationOn.mono _ <| Set.inter_subset_left ) <| lt_top_iff_ne_top.mpr h_measurable.1, fun a b ha hb ha' hb' => ne_of_lt <| lt_of_le_of_lt ( eVariationOn.mono _ <| Set.inter_subset_left ) <| lt_top_iff_ne_top.mpr h_measurable.2 ⟩)
      generalize_proofs at *; (
      have h_measurable : ∀ {f : ℝ → ℝ}, LocallyBoundedVariationOn f (Set.Icc 0 1) → MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
        intro f hf
        have h_monotone : ∃ g h : ℝ → ℝ, MonotoneOn g (Set.Icc 0 1) ∧ MonotoneOn h (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc 0 1, f t = g t - h t := by
          have := hf.exists_monotoneOn_sub_monotoneOn
          generalize_proofs at *; (
          exact ⟨ this.choose, this.choose_spec.choose, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.1, fun t ht => congr_fun this.choose_spec.choose_spec.2.2 t ⟩)
        generalize_proofs at *; (
        obtain ⟨ g, h, hg, hh, hgh ⟩ := h_monotone
        have h_measurable : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) ∧ MeasureTheory.AEStronglyMeasurable h (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
          have h_measurable : ∀ {f : ℝ → ℝ}, MonotoneOn f (Set.Icc 0 1) → MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
            intro f hf
            have h_measurable : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
              have h_monotone : MonotoneOn f (Set.Icc 0 1) := hf
              have h_measurable : MeasureTheory.AEStronglyMeasurable (fun t => f (min 1 (max 0 t))) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 1)) := by
                have h_measurable : Monotone (fun t => f (min 1 (max 0 t))) := by
                  intro t t' htt';
                  exact h_monotone ⟨ by cases max_cases 0 t <;> cases min_cases 1 ( max 0 t ) <;> linarith, by cases max_cases 0 t <;> cases min_cases 1 ( max 0 t ) <;> linarith ⟩ ⟨ by cases max_cases 0 t' <;> cases min_cases 1 ( max 0 t' ) <;> linarith, by cases max_cases 0 t' <;> cases min_cases 1 ( max 0 t' ) <;> linarith ⟩ ( by cases max_cases 0 t <;> cases min_cases 1 ( max 0 t ) <;> cases max_cases 0 t' <;> cases min_cases 1 ( max 0 t' ) <;> linarith )
                generalize_proofs at *; (
                exact h_measurable.measurable.aestronglyMeasurable.restrict)
              exact h_measurable.congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => by simp +decide [ hx.1, hx.2 ] )
            generalize_proofs at *; (
            exact h_measurable)
          generalize_proofs at *; (
          exact ⟨ h_measurable hg, h_measurable hh ⟩)
        generalize_proofs at *; (
        exact MeasureTheory.AEStronglyMeasurable.congr ( h_measurable.1.sub h_measurable.2 ) ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => by aesop )))
      generalize_proofs at *; (
      exact ⟨ h_measurable <| by tauto, h_measurable <| by tauto ⟩))
    generalize_proofs at *; (
    convert h_measurable.1.smul_const ( 1 : ℂ ) |> AEStronglyMeasurable.add <| h_measurable.2.smul_const Complex.I using 1 ; ext ; simp +decide)
  generalize_proofs at *; (
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun _ => h_bounded.choose, by norm_num, by simpa only [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] using h_measurable, Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_bounded.choose_spec x <| Set.Ioc_subset_Icc_self hx ]))

/-
The phase projection of a bounded-variation function has real bounded
variation (the projection is Lipschitz, so it preserves finite variation).
-/
theorem concreteHasBVReal_projReal {w : ℂ} {g : ℝ → ℂ}
    (hg : ConcreteHasBV g) :
    ConcreteHasBVReal (projReal w g) := by
  refine' ne_top_of_le_ne_top ( ENNReal.mul_ne_top _ _ ) _;
  exact ↑‖w‖₊;
  exact eVariationOn g ( Set.Icc 0 1 );
  · exact ENNReal.coe_ne_top;
  · exact hg;
  · convert (LipschitzWith.lipschitzOnWith ( show LipschitzWith ‖w‖₊ ( fun z : ℂ => ( w * z |> Complex.re ) ) from ?_ ) ).comp_eVariationOn_le ( Set.mapsTo_univ g ( Set.Icc 0 1 ) ) using 1;
    rw [ lipschitzWith_iff_norm_sub_le ];
    intro x y; have := norm_mul_le w ( x - y ) ; simp_all +decide [ mul_sub ] ;
    exact le_trans ( by simpa [ Complex.normSq, Complex.norm_def ] using Complex.abs_re_le_norm ( w * x - w * y ) ) this

theorem concreteVariationReal_projReal_le {w : ℂ} (hw : ‖w‖ ≤ 1) {g : ℝ → ℂ}
    (hg : ConcreteHasBV g) :
    concreteVariationReal (projReal w g) ≤ concreteVariation g := by
  convert ENNReal.toReal_mono _ _ using 1;
  · exact hg;
  · refine' iSup_le fun p => _;
    refine' le_trans _ ( le_ciSup _ p );
    · -- Since the real part function is Lipschitz with constant 1, the variation of the real part is less than or equal to the variation of the original function.
      have h_lip : ∀ x y : ℂ, ‖(w * x).re - (w * y).re‖ₑ ≤ ‖x - y‖ₑ := by
        intro x y
        have h_lip : ‖(w * x).re - (w * y).re‖ ≤ ‖w‖ * ‖x - y‖ := by
          convert Complex.abs_re_le_norm ( w * ( x - y ) ) using 1 ; simp +decide [ mul_sub ];
          rw [ norm_mul ];
        rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
        exact le_trans ( by simpa [ Complex.normSq, Complex.norm_def ] using h_lip ) ( mul_le_of_le_one_left ( norm_nonneg _ ) hw );
      exact Finset.sum_le_sum fun i _ => h_lip _ _;
    · simp +zetaDelta at *

/-
The phase projection of a zero-mean function has zero real mean.
-/
theorem periodMeanReal_projReal {w : ℂ} {g : ℝ → ℂ}
    (hg : ConcreteHasBV g) (h0 : periodMean g = 0) :
    periodMeanReal (projReal w g) = 0 := by
  unfold periodMeanReal projReal;
  convert congr_arg Complex.re ( show ∫ x in Set.Ioc 0 1, w * g x = 0 from ?_ ) using 1;
  · convert ( integral_re ?_ );
    any_goals tauto;
    exact MeasureTheory.Integrable.const_mul ( concreteHasBV_integrableOn hg ) _;
  · rw [ MeasureTheory.integral_const_mul, show ∫ x in Set.Ioc 0 1, g x = 0 from h0, MulZeroClass.mul_zero ]

/-
**Complex Denjoy–Koksma from real Denjoy–Koksma.**

The complex Denjoy–Koksma estimate (constant `1`, in the complex norm variation)
follows from the real Denjoy–Koksma theorem packaged in `RealDenjoyKoksma θ`.
-/
theorem complex_denjoy_koksma_of_real {θ : ℝ} (S : RealDenjoyKoksma θ)
    (g : ℝ → ℂ) (hg : ConcreteHasBV g) (h0 : periodMean g = 0)
    (n : ℕ) (x : ℝ) :
    ‖∑ j ∈ Finset.range (S.toRotationReturnData.q n), g (x - (j : ℝ) * θ)‖
      ≤ concreteVariation g := by
  by_contra h_contra;
  obtain ⟨w, hw⟩ : ∃ w : ℂ, ‖w‖ = 1 ∧ (w * ∑ j ∈ Finset.range (S.q n), g (x - j * θ)).re = ‖∑ j ∈ Finset.range (S.q n), g (x - j * θ)‖ := by
    use (starRingEnd ℂ) (∑ j ∈ Finset.range (S.q n), g (x - j * θ)) / ‖∑ j ∈ Finset.range (S.q n), g (x - j * θ)‖;
    norm_num [ Complex.normSq, Complex.norm_def ];
    rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), div_self ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · grind;
    · exact ne_of_gt <| lt_of_le_of_lt ( by exact ENNReal.toReal_nonneg ) h_contra;
  have := S.dk_real ( projReal w g ) ( concreteHasBVReal_projReal hg ) ( periodMeanReal_projReal hg h0 ) n x;
  simp_all +decide [ projReal ];
  simp_all +decide [ ← Finset.mul_sum _ _ _ ];
  exact h_contra.not_ge ( this.trans ( concreteVariationReal_projReal_le ( by aesop ) hg ) )

/-- Alias matching the requested name: the concrete (complex) Denjoy–Koksma
estimate, derived from the standard real Denjoy–Koksma theorem. -/
theorem concrete_denjoy_koksma_estimate {θ : ℝ} (S : RealDenjoyKoksma θ) :
    ∀ g : ℝ → ℂ, ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range (S.toRotationReturnData.q n), g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  fun g hg h0 n x => complex_denjoy_koksma_of_real S g hg h0 n x

/-- **Denjoy–Koksma return data from the standard real DK theorem.**

Builds the full Stage 2B `DenjoyKoksmaReturnData θ` from a `RealDenjoyKoksma θ`
package, with the complex Denjoy–Koksma field discharged via
`complex_denjoy_koksma_of_real`. No external complex `dk` estimate is required. -/
noncomputable def DenjoyKoksmaReturnData.ofStandardDK {θ : ℝ} (S : RealDenjoyKoksma θ) :
    DenjoyKoksmaReturnData θ :=
  DenjoyKoksmaReturnData.ofConcrete S.toRotationReturnData
    (fun g hg h0 n x => complex_denjoy_koksma_of_real S g hg h0 n x)

/-- Alias matching the requested name. -/
noncomputable def concrete_denjoy_koksma_return_data {θ : ℝ} (S : RealDenjoyKoksma θ) :
    DenjoyKoksmaReturnData θ :=
  DenjoyKoksmaReturnData.ofStandardDK S

@[simp] theorem DenjoyKoksmaReturnData.ofStandardDK_q {θ : ℝ} (S : RealDenjoyKoksma θ) :
    (DenjoyKoksmaReturnData.ofStandardDK S).q = S.toRotationReturnData.q := rfl

/-- **Upgraded C¹ zero-mean uniform return-sum endpoint, using concrete
(real) Denjoy–Koksma data** rather than the abstract interface.

For `φ` admitting a mean-zero trigonometric-polynomial approximation in the
concrete variation, the continued-fraction return sums converge to `0`
uniformly. -/
theorem c1_zeroMean_returnSum_tendstoUniformly_concrete
    {θ : ℝ} (S : RealDenjoyKoksma θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ)
    (happrox : TrigApproxInVariation (DenjoyKoksmaReturnData.ofStandardDK S) φ) :
    TendstoUniformly
      (fun n (x : ℝ) =>
        ∑ j ∈ Finset.range (S.toRotationReturnData.q n), φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop :=
  c1_zeroMean_returnSum_tendstoUniformly (DenjoyKoksmaReturnData.ofStandardDK S) hθ φ happrox

end CriticalMixedHRT