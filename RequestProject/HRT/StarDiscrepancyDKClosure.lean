import Mathlib
import RequestProject.HRT.PeriodicDKClosure
import RequestProject.Rotation.StarDiscrepancyCorrection

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

/-!
# Closure of the periodic Denjoy–Koksma chain over the *corrected* star-discrepancy data

The structure `ContinuedFractionStarDiscrepancyData θ`
(`RequestProject.Rotation.StarDiscrepancyCorrection`) is the honest replacement
for the uninhabitable `StandardRealDenjoyKoksmaCombinatorics θ` (whose
`star_discrepancy_le_one` field is **false** — see `star_discrepancy_le_one_false`)
and `ContinuedFractionReturnData θ` (whose grid-balanced `orbit_partition` field
is **false**).  It carries the *true* **centered** star-discrepancy bound
(oscillation `≤ 2`), and via the recentered Koksma inequality
(`koksma_real_periodic_centered`) it produces the faithful periodic real
Denjoy–Koksma data `RealDenjoyKoksmaPeriodic θ` directly — with **no** dependence
on either false structure.

This module records the **fully closed** downstream endpoints, each consuming a
`ContinuedFractionStarDiscrepancyData θ`.  They are the corrected analogues of the
endpoints in `RequestProject.HRT.ContinuedFractionDKClosure` (which route through
the false grid-balanced `ContinuedFractionReturnData`).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Faithful periodic real Denjoy–Koksma data from corrected star-discrepancy
data.**  Both Koksma's (recentered) inequality and the true centered
star-discrepancy bound discharged, this builds `RealDenjoyKoksmaPeriodic θ` from a
`ContinuedFractionStarDiscrepancyData θ`. -/
noncomputable def real_denjoy_koksma_periodic_from_star_discrepancy_data {θ : ℝ}
    (D : ContinuedFractionStarDiscrepancyData θ) : RealDenjoyKoksmaPeriodic θ :=
  RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData D

/-- **Concrete complex periodic Denjoy–Koksma estimate, closed over corrected
star-discrepancy data.** -/
theorem concrete_denjoy_koksma_estimate_periodic_from_star_discrepancy_data {θ : ℝ}
    (D : ContinuedFractionStarDiscrepancyData θ) :
    ∀ g : ℝ → ℂ, Function.Periodic g 1 → ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range
            ((RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData D).toRotationReturnData.q n),
            g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  concrete_denjoy_koksma_estimate_periodic
    (RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData D)

/-- **Conditional final contradiction, closed over corrected star-discrepancy
data.**

The corrected final contradiction with the *only* Denjoy–Koksma input being a
`ContinuedFractionStarDiscrepancyData Dat.θ` (the recentered Koksma inequality and
the true centered orbit star-discrepancy bound both discharged).  Together with
the root-data, analytic, and winding interfaces, this derives `False` — with no
dependence on the false `orbit_partition` or false `star_discrepancy_le_one`
structures. -/
theorem critical_mixed_final_contradiction_with_valid_DK_interface_from_star_discrepancy_data
    {Z : L2ZakModel V} (Dat : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (D : ContinuedFractionStarDiscrepancyData Dat.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface Dat.θ
      (DenjoyKoksmaReturnData.ofPeriodicDK
        (RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData D)) a₀ b₀)
    (wind : CriticalMixedWindingInterface Dat.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_valid_DK_interface Dat
    (RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData D) rootData analytic wind

end CriticalMixedHRT
