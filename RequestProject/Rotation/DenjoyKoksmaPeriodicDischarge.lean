import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.Rotation.ConcreteVariation
import RequestProject.Rotation.C1VariationApprox
import RequestProject.Rotation.ConcreteDenjoyKoksma
import RequestProject.Rotation.C1UniformReturnSums
import RequestProject.Rotation.DenjoyKoksmaDischarge
import RequestProject.Rotation.OrbitPartition

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Corrected (periodic) Denjoy–Koksma discharge

`RequestProject.Rotation.RealDenjoyKoksma` proves that the previous run's
`RealDenjoyKoksma θ` structure is **uninhabitable**: its `dk_real` field omits the
periodicity hypothesis required by the classical Denjoy–Koksma theorem
(`dk_real_predicate_false`, `realDenjoyKoksma_isEmpty`).  Consequently every
endpoint of `RequestProject.Rotation.DenjoyKoksmaDischarge` that takes a
`RealDenjoyKoksma θ` argument — `concrete_denjoy_koksma_estimate`,
`DenjoyKoksmaReturnData.ofStandardDK`, `concrete_denjoy_koksma_return_data`,
`c1_zeroMean_returnSum_tendstoUniformly_concrete` — is *vacuously* applicable
(its hypothesis can never be supplied) and must not be used as certification
evidence.

This module rebuilds those four endpoints on the **faithful, satisfiable**
interface `RealDenjoyKoksmaPeriodic θ` (see
`RequestProject.Rotation.OrbitPartition`), whose Denjoy–Koksma field is
restricted to `1`-periodic functions.  The complex reduction uses the already
proved `complex_denjoy_koksma_of_real_periodic`.

Because the complex periodic estimate only holds for `1`-periodic functions, the
abstract `HasBV` predicate of the resulting `DenjoyKoksmaReturnData θ` is taken
to be `ConcreteHasBV g ∧ Function.Periodic g 1`.  This keeps the Denjoy–Koksma
bound field *true* (it is only ever invoked on periodic functions), in contrast
to `ofStandardDK`, whose `HasBV = ConcreteHasBV` predicate would require the
false non-periodic estimate.
-/

namespace CriticalMixedHRT

/-- **Concrete (complex) periodic Denjoy–Koksma estimate**, derived from the
faithful periodic real Denjoy–Koksma interface.

This is the corrected analogue of `concrete_denjoy_koksma_estimate`, with the
necessary `Function.Periodic g 1` hypothesis added (without which the inequality
is false). -/
theorem concrete_denjoy_koksma_estimate_periodic {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) :
    ∀ g : ℝ → ℂ, Function.Periodic g 1 → ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range (S.toRotationReturnData.q n), g (x - (j : ℝ) * θ)‖
          ≤ concreteVariation g :=
  fun g hper hg h0 n x => complex_denjoy_koksma_of_real_periodic S g hper hg h0 n x

/-- **Denjoy–Koksma return data from the faithful periodic real DK interface.**

Builds a Stage 2B `DenjoyKoksmaReturnData θ` from a `RealDenjoyKoksmaPeriodic θ`
package.  The abstract bounded-variation predicate is
`ConcreteHasBV g ∧ Function.Periodic g 1`, so the Denjoy–Koksma bound field is
only ever invoked on `1`-periodic functions, where the periodic estimate
`complex_denjoy_koksma_of_real_periodic` applies.  This is the corrected
analogue of `DenjoyKoksmaReturnData.ofStandardDK`, which depended on the false
non-periodic interface. -/
noncomputable def DenjoyKoksmaReturnData.ofPeriodicDK {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) :
    DenjoyKoksmaReturnData θ where
  toRotationReturnData := S.toRotationReturnData
  HasBV := fun g => ConcreteHasBV g ∧ Function.Periodic g 1
  variation := concreteVariation
  mean := periodMean
  dk_bound := fun g hg h0 n x =>
    complex_denjoy_koksma_of_real_periodic S g hg.2 hg.1 h0 n x

@[simp] theorem DenjoyKoksmaReturnData.ofPeriodicDK_q {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) :
    (DenjoyKoksmaReturnData.ofPeriodicDK S).q = S.toRotationReturnData.q := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofPeriodicDK_HasBV {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) :
    (DenjoyKoksmaReturnData.ofPeriodicDK S).HasBV
      = (fun g => ConcreteHasBV g ∧ Function.Periodic g 1) := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofPeriodicDK_variation {θ : ℝ}
    (S : RealDenjoyKoksmaPeriodic θ) :
    (DenjoyKoksmaReturnData.ofPeriodicDK S).variation = concreteVariation := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofPeriodicDK_mean {θ : ℝ}
    (S : RealDenjoyKoksmaPeriodic θ) :
    (DenjoyKoksmaReturnData.ofPeriodicDK S).mean = periodMean := rfl

/-- Alias matching the requested name: the corrected periodic Denjoy–Koksma
return data. -/
noncomputable def concrete_denjoy_koksma_return_data_periodic {θ : ℝ}
    (S : RealDenjoyKoksmaPeriodic θ) : DenjoyKoksmaReturnData θ :=
  DenjoyKoksmaReturnData.ofPeriodicDK S

/-- **Corrected C¹ zero-mean uniform return-sum endpoint, using the faithful
periodic Denjoy–Koksma data.**

For `φ` admitting a mean-zero trigonometric-polynomial approximation in the
periodic Denjoy–Koksma variation, the continued-fraction return sums converge to
`0` uniformly.  This is the corrected analogue of
`c1_zeroMean_returnSum_tendstoUniformly_concrete`, built on the satisfiable
periodic interface. -/
theorem c1_zeroMean_returnSum_tendstoUniformly_concrete_periodic
    {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ)
    (happrox : TrigApproxInVariation (DenjoyKoksmaReturnData.ofPeriodicDK S) φ) :
    TendstoUniformly
      (fun n (x : ℝ) =>
        ∑ j ∈ Finset.range (S.toRotationReturnData.q n), φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop :=
  c1_zeroMean_returnSum_tendstoUniformly (DenjoyKoksmaReturnData.ofPeriodicDK S) hθ φ happrox

end CriticalMixedHRT
