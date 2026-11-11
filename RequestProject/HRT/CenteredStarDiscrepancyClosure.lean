import Mathlib
import RequestProject.HRT.StarDiscrepancyDKClosure
import RequestProject.Rotation.CenteredOrbitGrid

/-!
# Closure of the periodic Denjoy–Koksma chain through the *centered orbit grid*

This module wires the centered orbit grid reduction
(`RequestProject.Rotation.CenteredOrbitGrid`) into the final contradiction.

Recall the corrected, honest data structure `ContinuedFractionStarDiscrepancyData θ`
carries the **true** centered orbit star-discrepancy bound (oscillation `≤ 2`),
and that the previous run's targets

* `ContinuedFractionReturnData.orbit_partition` (grid-balancedness, `c = 0`) and
* `StandardRealDenjoyKoksmaCombinatorics.star_discrepancy_le_one`
  (unsigned `|orbitDiscrepancy| ≤ 1`)

are both **false** (see `star_discrepancy_le_one_false`) and quarantined.

The centered orbit grid property `StandardCenteredOrbitGridProperty θ q`
(`RequestProject.Rotation.CenteredOrbitGrid`) is the honest centered replacement:
a strictly smaller, finite, combinatorial statement (the three-distance /
best-approximation content for convergent denominators) from which the centered
star-discrepancy bound — and hence the entire faithful periodic Denjoy–Koksma
interface — is *proved* here.

This file records the final contradiction endpoint whose only Denjoy–Koksma input
is rotation return data together with the centered orbit grid property:
`critical_mixed_final_contradiction_with_valid_DK_interface_centered_closed`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Concrete complex periodic Denjoy–Koksma estimate, closed over the centered
orbit grid.**  The centered star-discrepancy bound is *proved* from the (strictly
smaller, finite) centered orbit grid property; the recentered Koksma inequality
then yields the periodic estimate. -/
theorem concrete_denjoy_koksma_estimate_periodic_centered_closed {θ : ℝ}
    (R : RotationReturnData θ) (hqt : Tendsto R.q atTop atTop) (hθ : Irrational θ)
    (H : StandardCenteredOrbitGridProperty θ R.q) :
    ∀ g : ℝ → ℂ, Function.Periodic g 1 → ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range
            ((real_denjoy_koksma_periodic_from_proved_centered_discrepancy
                R hqt hθ H).toRotationReturnData.q n),
            g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  concrete_denjoy_koksma_estimate_periodic
    (real_denjoy_koksma_periodic_from_proved_centered_discrepancy R hqt hθ H)

/-- **Conditional final contradiction, closed over the centered orbit grid.**

The final contradiction whose *only* Denjoy–Koksma input is the rotation return
data `R` together with the centered orbit grid property
`StandardCenteredOrbitGridProperty Dat.θ R.q` (the honest centered three-distance
content).  From it the corrected star-discrepancy data is constructed, the
recentered Koksma inequality is applied, and — together with the root-data,
analytic, and winding interfaces — `False` is derived, with **no** dependence on
the false `orbit_partition` or false unsigned `star_discrepancy_le_one`. -/
theorem critical_mixed_final_contradiction_with_valid_DK_interface_centered_closed
    {Z : L2ZakModel V} (Dat : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (R : RotationReturnData Dat.θ) (hqt : Tendsto R.q atTop atTop)
    (H : StandardCenteredOrbitGridProperty Dat.θ R.q)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface Dat.θ
      (DenjoyKoksmaReturnData.ofPeriodicDK
        (RealDenjoyKoksmaPeriodic.ofContinuedFractionStarDiscrepancyData
          (ContinuedFractionStarDiscrepancyData.ofCenteredOrbitGrid R hqt Dat.hθ_irr H)))
        a₀ b₀)
    (wind : CriticalMixedWindingInterface Dat.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_valid_DK_interface_from_star_discrepancy_data
    Dat (ContinuedFractionStarDiscrepancyData.ofCenteredOrbitGrid R hqt Dat.hθ_irr H)
    rootData analytic wind

end CriticalMixedHRT
