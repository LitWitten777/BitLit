import Mathlib
import RequestProject.HRT.DenjoyKoksmaValidEndpoints
import RequestProject.Rotation.PeriodicKoksma

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

/-!
# Closure of the corrected periodic Denjoy–Koksma interface

`RequestProject.Rotation.PeriodicKoksma` proves **Koksma's inequality**
(`koksma_real_periodic`, packaged as `standardPeriodicKoksmaInequality_proved`),
the analytic reduction from the orbit star-discrepancy bound to the periodic real
Denjoy–Koksma estimate.  Consequently the entire faithful periodic interface
`RealDenjoyKoksmaPeriodic θ` is constructible from the *single* remaining
combinatorial input

```
StandardRealDenjoyKoksmaCombinatorics θ
```

(the three-gap / best-approximation star-discrepancy bound for continued-fraction
denominators), via `RealDenjoyKoksmaPeriodic.ofStarDiscrepancy`.

This module records the **closed** downstream endpoints: each consumes
`StandardRealDenjoyKoksmaCombinatorics θ` directly (instead of a
`RealDenjoyKoksmaPeriodic θ` term), thereby exhibiting that the whole corrected
periodic Denjoy–Koksma chain — through the complex estimate, the uniform
return-sum convergence, the resonance corollary, and the final conditional
contradiction — is reduced to exactly one combinatorial theorem type.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Koksma's inequality (periodic real form), proved.**  Alias of
`standardPeriodicKoksmaInequality_proved`: for every rotation number, the orbit
star-discrepancy bound implies the periodic real Denjoy–Koksma estimate. -/
theorem real_denjoy_koksma_periodic_proved (θ : ℝ) :
    StandardPeriodicKoksmaInequality θ :=
  standardPeriodicKoksmaInequality_proved θ

/-- **Complex periodic Denjoy–Koksma estimate, closed over the combinatorial
input.**  The corrected complex estimate, with the faithful periodic data built
from the star-discrepancy interface. -/
theorem complex_denjoy_koksma_of_real_periodic_closed
    {θ : ℝ} (C : StandardRealDenjoyKoksmaCombinatorics θ)
    (g : ℝ → ℂ) (hper : Function.Periodic g 1) (hg : ConcreteHasBV g)
    (h0 : periodMean g = 0) (n : ℕ) (x : ℝ) :
    ‖∑ j ∈ Finset.range ((RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C).toRotationReturnData.q n),
        g (x - (j : ℝ) * θ)‖
      ≤ concreteVariation g :=
  complex_denjoy_koksma_of_real_periodic (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)
    g hper hg h0 n x

/-- **Concrete complex periodic Denjoy–Koksma estimate, closed over the
combinatorial input.**  Corrected analogue of `concrete_denjoy_koksma_estimate`,
with the faithful periodic data built from the star-discrepancy interface. -/
theorem concrete_denjoy_koksma_estimate_periodic_closed
    {θ : ℝ} (C : StandardRealDenjoyKoksmaCombinatorics θ) :
    ∀ g : ℝ → ℂ, Function.Periodic g 1 → ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range
            ((RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C).toRotationReturnData.q n),
            g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  concrete_denjoy_koksma_estimate_periodic (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)

/-- **C¹ zero-mean uniform return-sum endpoint, closed over the combinatorial
input.**  The corrected uniform return-sum convergence, with the faithful
periodic data built from the star-discrepancy interface. -/
theorem c1_zeroMean_returnSum_tendstoUniformly_concrete_periodic_closed
    {θ : ℝ} (C : StandardRealDenjoyKoksmaCombinatorics θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ)
    (happrox : TrigApproxInVariation
        (DenjoyKoksmaReturnData.ofPeriodicDK (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)) φ) :
    TendstoUniformly
      (fun n (x : ℝ) =>
        ∑ j ∈ Finset.range
            ((RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C).toRotationReturnData.q n),
          φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop :=
  c1_zeroMean_returnSum_tendstoUniformly_concrete_periodic
    (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C) hθ φ happrox

/-- **Resonance-group corollary, closed over the combinatorial input.**  The
holonomy lies in the resonance group of the return times, with the faithful
periodic data built from the star-discrepancy interface. -/
theorem measurable_cocycle_holonomy_resonant_periodic_valid_closed
    {θ : ℝ} (hθ : Irrational θ) (C : StandardRealDenjoyKoksmaCombinatorics θ)
    (h b ell : ℝ → ℂ)
    (hh_meas : Measurable h) (hh_per : Function.Periodic h 1)
    (hell_meas : Measurable ell) (hell_per : Function.Periodic ell 1)
    (hell_int : Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (happrox : TrigApproxInVariation
        (DenjoyKoksmaReturnData.ofPeriodicDK (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C))
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y)) :
    Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y)
      ∈ resonanceGroupC
          (DenjoyKoksmaReturnData.ofPeriodicDK (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)).q :=
  measurable_cocycle_holonomy_resonant_periodic_valid hθ
    (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)
    h b ell hh_meas hh_per hell_meas hell_per hell_int hmem hpos hcocycle hlog happrox

/-- **Final-assembly Denjoy–Koksma interface, closed over the combinatorial
input.**  Builds the `CriticalMixedDKInterface` from the star-discrepancy
interface alone. -/
noncomputable def CriticalMixedDKInterface_of_periodic_DK_closed
    {θ : ℝ} (C : StandardRealDenjoyKoksmaCombinatorics θ) : CriticalMixedDKInterface θ :=
  CriticalMixedDKInterface.ofPeriodicDK (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)

/-- **Conditional final contradiction, closed over the combinatorial input.**

The corrected final contradiction `critical_mixed_final_contradiction_with_valid_DK_interface`,
with the *only* Denjoy–Koksma input being the combinatorial star-discrepancy
interface `StandardRealDenjoyKoksmaCombinatorics D.θ` (Koksma's inequality having
been discharged in `RequestProject.Rotation.PeriodicKoksma`).  Together with the
root-data, analytic, and winding interfaces, this derives `False`. -/
theorem critical_mixed_final_contradiction_with_valid_DK_interface_closed
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (C : StandardRealDenjoyKoksmaCombinatorics D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ
      (DenjoyKoksmaReturnData.ofPeriodicDK (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C)) a₀ b₀)
    (wind : CriticalMixedWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_valid_DK_interface D
    (RealDenjoyKoksmaPeriodic.ofStarDiscrepancy C) rootData analytic wind

end CriticalMixedHRT
