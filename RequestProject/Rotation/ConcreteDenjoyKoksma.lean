import Mathlib
import RequestProject.Rotation.ConcreteVariation
import RequestProject.Rotation.C1VariationApprox
import RequestProject.Rotation.C1UniformReturnSums

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Reducing the variation-approximation hypothesis to L¹ density of derivatives
(Run C, Task 1, target 3)

Stage 2B's uniform return-sum theorem is conditional on the abstract predicate
`TrigApproxInVariation D φ`: that `φ` can be approximated, in the variation
functional carried by `D`, by mean-zero trigonometric polynomials.

For a *concrete* Denjoy–Koksma return data
`D = DenjoyKoksmaReturnData.ofConcrete R dk` (whose `HasBV`, `variation`, `mean`
are the genuine objects `ConcreteHasBV`, `concreteVariation`, `periodMean`), we
prove that `TrigApproxInVariation D φ` follows from the **standard `L¹` density
statement**: that for every `ε > 0` there is a mean-zero trigonometric
polynomial `P = trigPoly a s` (`0 ∉ s`) such that the remainder `φ - P` is `C¹`
on `[0,1]` with `∫₀¹ ‖(φ - P)'‖ < ε`.

This is the honest reduction requested: the only remaining input is the
classical density of trigonometric polynomials in `L¹` (here, density of their
derivatives, supplied by Fejér/Cesàro means), and the variation side is
discharged by the `C¹` variation bound `concreteVariation_le_integral_norm_deriv`
of `C1VariationApprox`.
-/

namespace CriticalMixedHRT

/-- **Variation approximation from L¹ density of derivatives (concrete data).**

Let `R` be rotation return data and `dk` the Denjoy–Koksma estimate phrased with
the concrete variation objects, so that `D := DenjoyKoksmaReturnData.ofConcrete
R dk` has concrete analytic fields.  If for every `ε > 0` there is a mean-zero
trigonometric polynomial `P = trigPoly a s` (`0 ∉ s`) whose remainder
`g := φ - P` is `C¹` on `[0,1]` with `L¹`-derivative norm `< ε`, then
`TrigApproxInVariation D φ` holds.

The variation of the remainder is controlled by its derivative's `L¹` norm via
`concreteVariation_le_integral_norm_deriv`, and `C¹`-ness gives `ConcreteHasBV`. -/
theorem c1_has_trigApprox_in_variation_of_l1_deriv_density
    {θ : ℝ} (R : RotationReturnData θ)
    (dk : ∀ g : ℝ → ℂ, ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range (R.q n), g (x - (j : ℝ) * θ)‖ ≤ concreteVariation g)
    (φ : ℝ → ℂ)
    (hdense : ∀ ε : ℝ, 0 < ε →
      ∃ (a : ℤ → ℂ) (s : Finset ℤ) (g' : ℝ → ℂ),
        (0 : ℤ) ∉ s ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun y => φ y - trigPoly a s y) (g' x) x) ∧
        ContinuousOn g' (Set.Icc (0 : ℝ) 1) ∧
        periodMean (fun x => φ x - trigPoly a s x) = 0 ∧
        (∫ x in (0 : ℝ)..1, ‖g' x‖) < ε) :
    TrigApproxInVariation (DenjoyKoksmaReturnData.ofConcrete R dk) φ := by
  intro ε hε
  obtain ⟨a, s, g', hs, hderiv, hcont, hmean, hl1⟩ := hdense ε hε
  refine ⟨a, s, hs, ?_, ?_, ?_⟩
  · -- ConcreteHasBV of the C¹ remainder
    simpa using concreteHasBV_of_c1 hderiv hcont
  · -- mean zero
    simpa using hmean
  · -- variation < ε, via the C¹ variation bound
    have hvar := concreteVariation_le_integral_norm_deriv hderiv hcont
    simpa using lt_of_le_of_lt hvar hl1

end CriticalMixedHRT
