import Mathlib
import RequestProject.HRT.PeriodicDKClosure
import RequestProject.Rotation.ContinuedFractionReturnData

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

/-!
# Closure of the corrected periodic Denjoy–Koksma chain over enriched data

`RequestProject.Rotation.ContinuedFractionReturnData` introduces the enriched
structure `ContinuedFractionReturnData θ` and *proves* the orbit
star-discrepancy bound `star_discrepancy_le_one` from its grid-balanced
orbit-partition field, yielding the adapter

```
ContinuedFractionReturnData.toStandardRealDenjoyKoksmaCombinatorics :
  ContinuedFractionReturnData θ → StandardRealDenjoyKoksmaCombinatorics θ
```

Combined with the already-discharged Koksma inequality
(`RequestProject.Rotation.PeriodicKoksma`), the entire corrected periodic
Denjoy–Koksma chain is therefore reduced to constructing a
`ContinuedFractionReturnData θ` — equivalently, to establishing the
grid-balanced orbit partition (the three-gap / best-approximation
equidistribution property) for continued-fraction convergent denominators.

This module records the **fully closed** downstream endpoints: each consumes a
`ContinuedFractionReturnData θ` directly.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Faithful periodic real Denjoy–Koksma data, fully closed over enriched
continued-fraction return data.**  Koksma's inequality and the star-discrepancy
bound both discharged, this builds `RealDenjoyKoksmaPeriodic θ` from a
`ContinuedFractionReturnData θ`. -/
noncomputable def real_denjoy_koksma_periodic_fully_closed {θ : ℝ}
    (D : ContinuedFractionReturnData θ) : RealDenjoyKoksmaPeriodic θ :=
  RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData D

/-- **Concrete complex periodic Denjoy–Koksma estimate, fully closed over
enriched continued-fraction return data.** -/
theorem concrete_denjoy_koksma_estimate_periodic_fully_closed {θ : ℝ}
    (D : ContinuedFractionReturnData θ) :
    ∀ g : ℝ → ℂ, Function.Periodic g 1 → ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range
            ((RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData D).toRotationReturnData.q n),
            g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  concrete_denjoy_koksma_estimate_periodic
    (RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData D)

/-- **Conditional final contradiction, fully closed over enriched
continued-fraction return data.**

The corrected final contradiction with the *only* Denjoy–Koksma input being a
`ContinuedFractionReturnData D.θ` (Koksma's inequality and the orbit
star-discrepancy bound both discharged).  Together with the root-data, analytic,
and winding interfaces, this derives `False`. -/
theorem critical_mixed_final_contradiction_with_valid_DK_interface_fully_closed
    {Z : L2ZakModel V} (Dat : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (D : ContinuedFractionReturnData Dat.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface Dat.θ
      (DenjoyKoksmaReturnData.ofPeriodicDK
        (RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData D)) a₀ b₀)
    (wind : CriticalMixedWindingInterface Dat.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_valid_DK_interface Dat
    (RealDenjoyKoksmaPeriodic.ofContinuedFractionReturnData D) rootData analytic wind

end CriticalMixedHRT
