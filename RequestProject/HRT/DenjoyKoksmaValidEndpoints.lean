import Mathlib
import RequestProject.HRT.ConditionalFinalAssembly
import RequestProject.Rotation.DenjoyKoksmaPeriodicDischarge
import RequestProject.Rotation.HolonomyQuantizationPeriodic

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

/-!
# Task D — non-vacuous endpoints built on the valid periodic Denjoy–Koksma interface

The previous run showed that the structure `RealDenjoyKoksma θ` is uninhabitable
(`realDenjoyKoksma_isEmpty`), so every endpoint quantified over a
`RealDenjoyKoksma θ` argument is vacuously applicable.  The corrected, satisfiable
interface is `RealDenjoyKoksmaPeriodic θ`, from which
`DenjoyKoksmaReturnData.ofPeriodicDK` produces a genuine
`DenjoyKoksmaReturnData θ` whose `dk_bound` field is true (it is only ever applied
to `1`-periodic functions).

This module records the *valid* (non-vacuous) corrected endpoints that route the
project's conditional contradiction and resonance corollaries through the
periodic Denjoy–Koksma data rather than the false `RealDenjoyKoksma θ` object.

The `CriticalMixedDKInterface θ` bundle used by the final-assembly theorems is
*not itself* refuted — it carries an abstract `DenjoyKoksmaReturnData θ`, which is
inhabitable precisely via `ofPeriodicDK`.  The deep mathematical content that
remains open is the construction of a `RealDenjoyKoksmaPeriodic θ` (Koksma's
inequality + the continued-fraction star-discrepancy bound); this module does not
claim that content, only that *when supplied*, the corrected interface feeds the
contradiction soundly.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Build the final-assembly Denjoy–Koksma interface bundle from the faithful
periodic real Denjoy–Koksma data.  This is the *valid* (satisfiable) source of a
`CriticalMixedDKInterface`, replacing any construction routed through the false
`RealDenjoyKoksma θ` object. -/
noncomputable def CriticalMixedDKInterface.ofPeriodicDK {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) :
    CriticalMixedDKInterface θ where
  returnData := DenjoyKoksmaReturnData.ofPeriodicDK S
  hq := S.q_tendsto

@[simp] theorem CriticalMixedDKInterface.ofPeriodicDK_returnData {θ : ℝ}
    (S : RealDenjoyKoksmaPeriodic θ) :
    (CriticalMixedDKInterface.ofPeriodicDK S).returnData
      = DenjoyKoksmaReturnData.ofPeriodicDK S := rfl

/-- **Resonance-group corollary on the valid periodic Denjoy–Koksma data.**

The non-vacuous specialisation of `measurable_cocycle_holonomy_resonant_periodic`
to the satisfiable return data `DenjoyKoksmaReturnData.ofPeriodicDK S`.  Under the
periodic cocycle hypotheses, the holonomy `H = exp(∫₀¹ ell)` lies in the
resonance group of the (valid) return times. -/
theorem measurable_cocycle_holonomy_resonant_periodic_valid
    {θ : ℝ} (hθ : Irrational θ) (S : RealDenjoyKoksmaPeriodic θ)
    (h b ell : ℝ → ℂ)
    (hh_meas : Measurable h) (hh_per : Function.Periodic h 1)
    (hell_meas : Measurable ell) (hell_per : Function.Periodic ell 1)
    (hell_int : Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (happrox : TrigApproxInVariation (DenjoyKoksmaReturnData.ofPeriodicDK S)
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y)) :
    Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y)
      ∈ resonanceGroupC (DenjoyKoksmaReturnData.ofPeriodicDK S).q :=
  measurable_cocycle_holonomy_resonant_periodic hθ (DenjoyKoksmaReturnData.ofPeriodicDK S)
    h b ell hh_meas hh_per hell_meas hell_per hell_int hmem hpos hcocycle hlog happrox

/-- **Valid C¹ zero-mean uniform return-sum endpoint.**

Alias of `c1_zeroMean_returnSum_tendstoUniformly_concrete_periodic`, recording
that the corrected uniform return-sum convergence uses the satisfiable periodic
Denjoy–Koksma data (in contrast to the vacuous
`c1_zeroMean_returnSum_tendstoUniformly_concrete`). -/
theorem c1_zeroMean_returnSum_tendstoUniformly_concrete_valid
    {θ : ℝ} (S : RealDenjoyKoksmaPeriodic θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ)
    (happrox : TrigApproxInVariation (DenjoyKoksmaReturnData.ofPeriodicDK S) φ) :
    TendstoUniformly
      (fun n (x : ℝ) =>
        ∑ j ∈ Finset.range (S.toRotationReturnData.q n), φ ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop :=
  c1_zeroMean_returnSum_tendstoUniformly_concrete_periodic S hθ φ happrox

/-- **Conditional final contradiction with a valid (periodic) Denjoy–Koksma
interface.**

This is the corrected analogue of
`critical_mixed_final_contradiction_with_interfaces`: it consumes the *faithful,
satisfiable* periodic real Denjoy–Koksma data `RealDenjoyKoksmaPeriodic D.θ`
directly (via `CriticalMixedDKInterface.ofPeriodicDK`), rather than the
final-assembly DK bundle that could in principle be sourced from the false
`RealDenjoyKoksma D.θ` object.  From the normalized relation data and the four
remaining interface packages — with the DK side supplied by the valid periodic
interface — the project derives `False`. -/
theorem critical_mixed_final_contradiction_with_valid_DK_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (S : RealDenjoyKoksmaPeriodic D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ
      (DenjoyKoksmaReturnData.ofPeriodicDK S) a₀ b₀)
    (wind : CriticalMixedWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_interfaces D
    (CriticalMixedDKInterface.ofPeriodicDK S) rootData analytic wind

end CriticalMixedHRT
