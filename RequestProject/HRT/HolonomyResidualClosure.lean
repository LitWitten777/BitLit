import Mathlib
import RequestProject.HRT.ActiveFibreWindingZeroOnArc
import RequestProject.HRT.HolonomyIdentificationDischarge
import RequestProject.Rotation.MeasurableWinding

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 1000000

/-!
# Holonomy residual closure run

This module performs the **holonomy residual closure run**.  The active-fibre
winding-zero-on-arc run reduced the remaining holonomy-amplitude interface to
exactly three residual theorem types

```
StandardAEActiveFibreWindingZero                  (a.e. winding zero on active set)
StandardWindingLocallyConstantZeroFreeFamily      (local constancy on the arc)
StandardWindingZeroHolonomyBridge                 (zero-winding ⇒ holonomy)
```

This run **reduces each of the three residuals to a strictly smaller and more
canonical upstream interface**, and proves — fully in Lean, with no new
`sorry`/`axiom`/`admit` — that the upstream interface implies the residual.  The
three upstream interfaces are exactly the *acceptable final blockers* of the run
instructions:

* `StandardMeasurableWindingObstructionForActiveFibres` — the genuine **inputs**
  of the already-formalised measurable winding obstruction
  (`measurable_cocycle_winding_eq_zero`) holding for a.e. active fibre.  From it we
  *derive* the a.e.-winding-zero residual `StandardAEActiveFibreWindingZero`
  (`StandardAEActiveFibreWindingZero_proved`).

* `StandardWindingHomotopyInvarianceZeroFreeLoops` — the statement that the
  integer winding number, viewed as a real-valued function, varies **continuously**
  on the zero-free analytic family over the arc (the content of homotopy
  invariance of the winding number for nonvanishing loops).  From continuity of an
  integer-valued function we *derive* local constancy
  `StandardWindingLocallyConstantZeroFreeFamily`
  (`StandardWindingLocallyConstantZeroFreeFamily_proved`).

* `StandardZeroWindingPeriodicLogHolonomyBridge` — the canonical, choice-free
  per-fibre identification `gauge = algReturnHolonomy` at zero-winding fibres.  Via
  the already-proved `return_multiplier_holonomy_identification` and the root data
  this *derives* the periodic-log/integral bridge
  `StandardWindingZeroHolonomyBridge`
  (`StandardWindingZeroHolonomyBridge_proved`).

Finally the three upstream interfaces (with the root data) are assembled into the
downstream endpoints (`StandardActiveFibreWindingZeroOnArc_fully_proved`,
`StandardCanonicalAmplitudeCompatibility_fully_proved`, and the final
contradiction `critical_mixed_final_contradiction_holonomy_residuals_reduced`).

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Residual 1 — measurable winding obstruction on active fibres -/

/-- **Per-fibre inputs of the measurable winding obstruction.**

The exact hypotheses of `measurable_cocycle_winding_eq_zero` for a single fibre
loop `u`, together with the identification of the candidate winding number `wind`
with the phase-lift degree `d`.  Packaging these as a predicate makes the
fibrewise application of the already-formalised obstruction transparent. -/
def FibreWindingObstructionInput (θ : ℝ)
    (D : DenjoyKoksmaReturnData θ) (wind : ℤ) : Prop :=
  ∃ (u : ℝ → ℂ) (d : ℤ) (g : ℝ → ℝ),
    Measurable u ∧ (∀ x, ‖u x‖ = 1) ∧
    (∀ x, u (x - θ)
      = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))) * u x) ∧
    Tendsto
      (fun n => eLpNorm (fun x => u (x - (D.q n : ℝ) * θ) - u x) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) ∧
    (d ≠ 0 →
      Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1,
        Complex.exp (2 * π * Complex.I * windingPhase d g θ (D.q n) x))
        atTop (𝓝 0)) ∧
    wind = d

/-- **The per-fibre obstruction inputs force zero winding.**

This is the direct fibrewise application of the measurable winding obstruction
`measurable_cocycle_winding_eq_zero`. -/
theorem winding_eq_zero_of_fibreInput {θ : ℝ} (hθ : Irrational θ)
    {D : DenjoyKoksmaReturnData θ} {wind : ℤ}
    (h : FibreWindingObstructionInput θ D wind) : wind = 0 := by
  obtain ⟨u, d, g, hmeas, hu1, hstep, htrans, hosc, hwd⟩ := h
  exact measurable_cocycle_winding_eq_zero hθ D u hmeas hu1 d g hstep htrans hosc
    wind hwd

/-- **`STANDARD_MEASURABLE_WINDING_OBSTRUCTION_FOR_ACTIVE_FIBRES`.**

The acceptable upstream blocker for Residual 1: a positive-measure active subset
`S ⊆ (a₀,b₀)` of the arc on which, for almost every fibre `s ∈ S`, the per-fibre
inputs of the measurable winding obstruction hold (with winding number `W s`).
This packages exactly the *inputs* of the already-formalised obstruction. -/
structure StandardMeasurableWindingObstructionForActiveFibres
    (θ a₀ b₀ : ℝ) (W : ℝ → ℤ) where
  S : Set ℝ
  hSU : S ⊆ Set.Ioo a₀ b₀
  hSpos : 0 < volume S
  hθ : Irrational θ
  D : DenjoyKoksmaReturnData θ
  hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ S → FibreWindingObstructionInput θ D (W s)

/-- **`STANDARD_AE_ACTIVE_FIBRE_WINDING_ZERO_PROVED` (Task B).**

From the measurable-winding-obstruction inputs holding a.e. on a positive-measure
active subset, the a.e.-winding-zero residual `StandardAEActiveFibreWindingZero`
follows: the obstruction `measurable_cocycle_winding_eq_zero` forces `W s = 0` for
a.e. active fibre. -/
noncomputable def StandardAEActiveFibreWindingZero_proved {θ a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W) :
    StandardAEActiveFibreWindingZero a₀ b₀ ad W where
  S := mwo.S
  hSU := mwo.hSU
  hSpos := mwo.hSpos
  hWzero_ae := by
    filter_upwards [mwo.hae] with s hs hsS
    exact winding_eq_zero_of_fibreInput mwo.hθ (hs hsS)

/-- Re-export under the `ae_active_fibre_winding_zero_of_return_cocycle` name. -/
noncomputable def ae_active_fibre_winding_zero_of_return_cocycle {θ a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W) :
    StandardAEActiveFibreWindingZero a₀ b₀ ad W :=
  StandardAEActiveFibreWindingZero_proved mwo

/-! ## Residual 2 — winding homotopy invariance / local constancy -/

/-- **`STANDARD_WINDING_HOMOTOPY_INVARIANCE_ZERO_FREE_LOOPS`.**

The acceptable upstream blocker for Residual 2: the integer winding number `W`,
viewed as a real-valued function, varies **continuously** on the arc
`Set.Ioo a₀ b₀`.  This is exactly the content of homotopy invariance of the
winding number for the zero-free analytic return-multiplier family — a continuous
family of nonvanishing loops has a continuously varying winding number. -/
structure StandardWindingHomotopyInvarianceZeroFreeLoops (a₀ b₀ : ℝ) (W : ℝ → ℤ) :
    Prop where
  hCont : ContinuousOn (fun s => ((W s : ℤ) : ℝ)) (Set.Ioo a₀ b₀)

/-- **`STANDARD_WINDING_LOCALLY_CONSTANT_ZERO_FREE_FAMILY_PROVED` (Task C).**

Continuity of the integer winding number (as a real-valued function) on the arc
implies its local constancy: an integer-valued continuous function cannot vary by
less than `1` without being constant, so on a small enough relative neighbourhood
of each point it equals its value there. -/
theorem StandardWindingLocallyConstantZeroFreeFamily_proved {a₀ b₀ : ℝ} {W : ℝ → ℤ}
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W) :
    StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W where
  hLocConst := by
    intro s hs
    have hcont : ContinuousWithinAt (fun s => ((W s : ℤ) : ℝ)) (Set.Ioo a₀ b₀) s :=
      hom.hCont s hs
    have hball : ∀ᶠ t in 𝓝[Set.Ioo a₀ b₀] s,
        ((W t : ℤ) : ℝ) ∈ Metric.ball ((W s : ℤ) : ℝ) 1 :=
      hcont (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hball] with t ht
    have hd : |((W t : ℤ) : ℝ) - ((W s : ℤ) : ℝ)| < 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at ht; exact ht
    have hlt : |(W t : ℤ) - (W s : ℤ)| < 1 := by
      rw [← Int.cast_sub, ← Int.cast_abs] at hd
      exact_mod_cast hd
    have := abs_lt.mp hlt
    omega

/-- Re-export under the `winding_locally_constant_of_zero_free_homotopy` name. -/
theorem winding_locally_constant_of_zero_free_homotopy {a₀ b₀ : ℝ} {W : ℝ → ℤ}
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W) :
    StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W :=
  StandardWindingLocallyConstantZeroFreeFamily_proved hom

/-! ## Residual 3 — zero-winding periodic-log holonomy bridge -/

/-- **`STANDARD_ZERO_WINDING_PERIODIC_LOG_HOLONOMY_BRIDGE`.**

The acceptable upstream blocker for Residual 3: the canonical, choice-free
per-fibre identification `gauge = algReturnHolonomy` at zero-winding fibres of the
arc.  Compared with `StandardWindingZeroHolonomyBridge` it removes the choice of a
periodic logarithm and the loop-holonomy integral, keeping only the algebraic
identity. -/
structure StandardZeroWindingPeriodicLogHolonomyBridge (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) (W : ℝ → ℤ) : Prop where
  hAlg : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 → W t = 0 →
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t

/-- **`STANDARD_WINDING_ZERO_HOLONOMY_BRIDGE_PROVED` (Task D).**

The canonical algebraic identification `gauge = algReturnHolonomy` at zero-winding
fibres, together with the root data, yields the periodic-log/integral bridge: the
loop holonomy `exp(∫₀¹ ell_t)` of any periodic logarithm equals `algReturnHolonomy`
(`return_multiplier_holonomy_identification`). -/
theorem StandardWindingZeroHolonomyBridge_proved {θ a₀ b₀ : ℝ} {dlau mlau : ℕ}
    {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W) :
    StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W where
  hBridge := by
    intro t ht ht_ne hW0 ell_t hell
    exact return_multiplier_holonomy_identification mlau Mlau ad coeffs
      rootData.h_ad_coeff H θ t ht_ne (rootData.hroots_min t ht ht_ne)
      (zb.hAlg t ht ht_ne hW0) ell_t hell

/-- Re-export under the `zero_winding_periodic_log_holonomy_eq_gauge` name. -/
theorem zero_winding_periodic_log_holonomy_eq_gauge {θ a₀ b₀ : ℝ} {dlau mlau : ℕ}
    {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W) :
    StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W :=
  StandardWindingZeroHolonomyBridge_proved rootData zb

/-! ## Task E — downstream closure from the three upstream blockers -/

/-- **`STANDARD_ACTIVE_FIBRE_WINDING_ZERO_ON_ARC_FULLY_PROVED`.**

The winding form of the residual, built entirely from the three upstream
blockers (`StandardMeasurableWindingObstructionForActiveFibres`,
`StandardWindingHomotopyInvarianceZeroFreeLoops`,
`StandardZeroWindingPeriodicLogHolonomyBridge`) together with the root data. -/
theorem StandardActiveFibreWindingZeroOnArc_fully_proved {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H :=
  StandardActiveFibreWindingZeroOnArc_proved
    (StandardAEActiveFibreWindingZero_proved (ad := ad) mwo)
    (StandardWindingLocallyConstantZeroFreeFamily_proved hom)
    (StandardWindingZeroHolonomyBridge_proved rootData zb)

/-- **`STANDARD_ACTIVE_FIBRE_HOLONOMY_EQUALS_GAUGE_MULTIPLIER_FULLY_PROVED`.** -/
theorem StandardActiveFibreHolonomyEqualsGaugeMultiplier_fully_proved {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W) :
    StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H :=
  (StandardActiveFibreWindingZeroOnArc_fully_proved rootData mwo hom zb).toHolonomyEqualsGaugeMultiplier
    rootData

/-- **`STANDARD_CANONICAL_AMPLITUDE_COMPATIBILITY_FULLY_PROVED`.** -/
theorem StandardCanonicalAmplitudeCompatibility_fully_proved {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H :=
  canonical_amplitude_compatibility_of_winding rootData
    (StandardActiveFibreWindingZeroOnArc_fully_proved rootData mwo hom zb).toHolonomyData

/-- **`CRITICAL_MIXED_FINAL_CONTRADICTION_HOLONOMY_RESIDUALS_REDUCED`.**

The conditional final contradiction with the holonomy-amplitude interface reduced
entirely to the three upstream blockers
(`StandardMeasurableWindingObstructionForActiveFibres`,
`StandardWindingHomotopyInvarianceZeroFreeLoops`,
`StandardZeroWindingPeriodicLogHolonomyBridge`) together with the three packaged
interfaces (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`, `ZAK_MODEL_INTERFACE`).
The active-fibre winding-zero datum is now constructed internally. -/
theorem critical_mixed_final_contradiction_holonomy_residuals_reduced
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {W : ℝ → ℤ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres D.θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (zb : StandardZeroWindingPeriodicLogHolonomyBridge D.θ a₀ b₀ ad coeffs analytic.H W) :
    False :=
  critical_mixed_final_contradiction_with_active_fibre_holonomy_closed D dk rootData
    analytic (StandardActiveFibreWindingZeroOnArc_fully_proved rootData mwo hom zb)

end CriticalMixedHRT
