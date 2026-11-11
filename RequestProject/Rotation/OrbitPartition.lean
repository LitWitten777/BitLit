import Mathlib
import RequestProject.Rotation.DenjoyKoksmaDischarge
import RequestProject.Rotation.RealDenjoyKoksma

/-!
# Corrected (periodic) real Denjoy–Koksma interface and orbit star-discrepancy

`RequestProject.Rotation.RealDenjoyKoksma` proves that the previous run's
`RealDenjoyKoksma θ` structure is **uninhabitable**, because its `dk_real` field
omits the periodicity hypothesis required by the classical Denjoy–Koksma theorem.

This module supplies the *faithful* replacement: the structure
`RealDenjoyKoksmaPeriodic θ`, whose real Denjoy–Koksma field is restricted to
`1`-periodic functions.  Unlike the previous structure, this one is a sound (and
classically true) interface — it is not refuted by the
`RequestProject.Rotation.RealDenjoyKoksma.dk_real_predicate_false`
counterexample, which exploited a non-periodic test function.

We then prove the **complex-from-real reduction for periodic data**
(`complex_denjoy_koksma_of_real_periodic`): the complex periodic Denjoy–Koksma
inequality (constant `1`) follows from the real one, by projecting onto the
optimal unit phase.  This is the periodic analogue of
`CriticalMixedHRT.complex_denjoy_koksma_of_real`, but built on the *satisfiable*
interface.
-/

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

/-- The phase projection of a `1`-periodic complex function is `1`-periodic. -/
theorem projReal_periodic {w : ℂ} {g : ℝ → ℂ} (hg : Function.Periodic g 1) :
    Function.Periodic (projReal w g) 1 := by
  intro t
  unfold projReal
  rw [hg t]

/-- **Faithful (periodic) real Denjoy–Koksma interface.**

The classically true Denjoy–Koksma theorem for an irrational rotation by `θ`
with continued-fraction return denominators `q n`: every `1`-periodic,
bounded-variation, zero-mean real function has its full-period Birkhoff sums
bounded by its total variation (constant `1`).

This corrects `CriticalMixedHRT.RealDenjoyKoksma` by adding the `Function.Periodic
h 1` hypothesis, without which the inequality is false
(`RealDenjoyKoksma.dk_real_predicate_false`). -/
structure RealDenjoyKoksmaPeriodic (θ : ℝ) extends RotationReturnData θ where
  /-- The return denominators diverge to infinity. -/
  q_tendsto : Tendsto toRotationReturnData.q atTop atTop
  /-- The real Denjoy–Koksma inequality for `1`-periodic functions (constant `1`). -/
  dk_real_periodic :
    ∀ h : ℝ → ℝ, Function.Periodic h 1 → ConcreteHasBVReal h → periodMeanReal h = 0 →
      ∀ (n : ℕ) (x : ℝ),
        |∑ j ∈ Finset.range (toRotationReturnData.q n), h (x - (j : ℝ) * θ)|
          ≤ concreteVariationReal h

/-
**Complex periodic Denjoy–Koksma from real periodic Denjoy–Koksma.**

For a `1`-periodic complex bounded-variation function of zero mean, the complex
full-period Birkhoff sum is bounded in norm by the concrete variation, with the
same constant `1`.  Proof: project onto the optimal unit phase `w = conj S/‖S‖`;
`projReal w g` is `1`-periodic (`projReal_periodic`), bounded-variation
(`concreteHasBVReal_projReal`), zero-mean (`periodMeanReal_projReal`), and its
real variation is `≤ concreteVariation g` (`concreteVariationReal_projReal_le`),
so the real periodic inequality applies.
-/
theorem complex_denjoy_koksma_of_real_periodic {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ)
    (g : ℝ → ℂ) (hper : Function.Periodic g 1) (hg : ConcreteHasBV g) (h0 : periodMean g = 0)
    (n : ℕ) (x : ℝ) :
    ‖∑ j ∈ Finset.range (S.toRotationReturnData.q n), g (x - (j : ℝ) * θ)‖
      ≤ concreteVariation g := by
  by_contra h;
  -- Choose `w := conj Σ / ‖Σ‖`; then `‖w‖ = 1` and `(w * Σ).re = ‖Σ‖`.
  obtain ⟨w, hw⟩ : ∃ w : ℂ, ‖w‖ ≤ 1 ∧ (w * ∑ j ∈ Finset.range (S.q n), g (x - (j : ℝ) * θ)).re = ‖∑ j ∈ Finset.range (S.q n), g (x - (j : ℝ) * θ)‖ := by
    use (starRingEnd ℂ (∑ j ∈ Finset.range (S.q n), g (x - (j : ℝ) * θ))) / ‖∑ j ∈ Finset.range (S.q n), g (x - (j : ℝ) * θ)‖;
    simp_all +decide [ Complex.normSq_eq_norm_sq, Complex.div_re, Complex.div_im ];
    simp +decide [ Complex.normSq, Complex.norm_def, sq ];
    grind;
  have := S.dk_real_periodic ( projReal w g ) ( projReal_periodic hper ) ( concreteHasBVReal_projReal hg ) ( periodMeanReal_projReal hg h0 ) n x;
  -- Now `∑ j, projReal w g (x-j*θ) = ∑ j, (w * g (x-j*θ)).re = (w * Σ).re = ‖Σ‖` (pull out `w` via `← Finset.mul_sum`, then `.re`).
  have h_sum : ∑ j ∈ Finset.range (S.q n), (w * g (x - (j : ℝ) * θ)).re = (w * ∑ j ∈ Finset.range (S.q n), g (x - (j : ℝ) * θ)).re := by
    simp +decide [ Finset.mul_sum _ _ _, Complex.mul_re ];
  exact h ( by linarith! [ abs_le.mp this, concreteVariationReal_projReal_le hw.1 hg ] )

end CriticalMixedHRT