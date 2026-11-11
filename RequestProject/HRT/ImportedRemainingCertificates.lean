import Mathlib
import RequestProject.HRT.FinalInterfaceDischarge
import RequestProject.HRT.RootCountLocalConstancy
import RequestProject.Rotation.CenteredOrbitGrid
import RequestProject.HRT.CenteredStarDiscrepancyClosure
import RequestProject.HRT.ActiveAnalyticAmplitudeReanchor

/-!
# Imported remaining certificates — clean adapter layer

This module is the single clean place collecting the **exact** remaining
classical-input interfaces of the critical mixed-arithmetic four-point HRT
certification, together with the honest *conditional* adapter endpoints that
already feed each interface into the downstream certificate.

## Status of the remaining blockers (see `IMPORTED_REMAINING_CERTIFICATES_STATUS.md`)

Three of the remaining blockers are isolated in the project as precisely-typed
`Prop`/`Type` residuals (each is a named classical theorem that is **not** in
Mathlib for this toolchain — verified by source search: no `three_gap`,
`Rouche`, or `argument_principle` declarations exist in Mathlib `v4.28.0`):

* `StandardInsideCountLocallyConstant` / `StandardRoucheRootCountStability`
  (Rouché / argument principle: the inside-disk root count of a continuous
  family of fibre polynomials with no boundary roots is locally constant);
* `StandardCenteredOrbitGridProperty`
  (the centered three-distance / best-approximation theorem for continued-fraction
  convergent denominators);
* `StandardCanonicalAmplitudeResonanceProperty`
  (measurable-winding holonomy quantization: the canonical loop-holonomy amplitude
  lands in the resonance group on a positive-measure active set).

The remaining four classical inputs named in the task
(`StandardCriticalMixedNormalForm`, `StandardFourTermRelationToNormalizedRelation`,
`StandardThreePointNonzeroCoefficients`,
`StandardNormalizedContradictionImpliesLinearIndependence`) are the final
geometric-assembly content (`SL(2,ℤ)`/metaplectic normal form, the three-point
HRT theorem, and the linear-independence extraction).  These are **not** present
as Lean declarations anywhere in the project; they correspond to the deep
infrastructure that the single remaining theorem-body `sorry`
(`critical_mixed_orbit_HRT_L2` in `MainStatement.lean`) represents, and which is
not in Mathlib.  They are therefore left as genuinely-absent classical inputs and
documented (not stubbed, not axiomatised) in the status file.

Because none of the eight blockers is provable unconditionally from Mathlib or an
existing certified project endpoint, this file does **not** introduce any
unconditional `_proved` endpoint for them (doing so would require `sorry` or an
axiom).  Instead it pins each *existing* residual to a single canonical alias and
re-exports the honest *conditional* adapter that already feeds it into the
certificate.  No `sorry`, `admit`, `axiom`, `unsafe`, or `@[implemented_by]`
appears here.
-/

namespace CriticalMixedHRT

open Complex Polynomial
open scoped BigOperators Real Classical
open Set

/-! ## Canonical aliases for the three isolated residual interfaces -/

/-- Canonical alias of the Rouché root-count residual (Task B).  Equal by
definition to `StandardInsideCountLocallyConstant`, the locally-constant
inside-disk root count of the fibre polynomial on the active arc. -/
abbrev RemainingRoucheRootCountResidual {d : ℕ}
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ) : Prop :=
  StandardInsideCountLocallyConstant coeffs a b

/-- Canonical alias of the centered three-distance residual (Task C).  Equal by
definition to `StandardCenteredOrbitGridProperty`. -/
abbrev RemainingCenteredThreeDistanceResidual (θ : ℝ) (q : ℕ → ℕ) : Prop :=
  StandardCenteredOrbitGridProperty θ q

/-! ## Conditional adapters (Task B/C/D)

Each adapter takes the corresponding isolated residual as an explicit hypothesis
and produces the downstream certificate datum.  These are honest re-exports of
the reductions already established in the project; they are *not* claims that the
residual itself is proved. -/

/-- **Task B adapter.**  The Rouché root-count stability residual feeds the
minimal return-multiplier root-data interface.  Re-export of
`standardReturnMultiplierRootDataMinimal_of_rouche`. -/
theorem rouche_residual_feeds_rootDataMinimal
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) {a b : ℝ}
    (ad : LaurentPolynomial ℂ) (mlau : ℕ) (Mlau : ℤ)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hrouche : StandardRoucheRootCountStability coeffs a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hMlau : Mlau = (fibreInsideCount coeffs t₀ : ℤ)) :
    StandardReturnMultiplierRootDataMinimal coeffs a b ad mlau Mlau :=
  standardReturnMultiplierRootDataMinimal_of_rouche coeffs ad mlau Mlau hmM hzf
    hrouche ht₀ hMlau

/-- **Task C adapter.**  The centered three-distance residual feeds the corrected
continued-fraction star-discrepancy data.  Re-export of
`ContinuedFractionStarDiscrepancyData_proved`. -/
theorem centeredThreeDistance_residual_feeds_starDiscrepancyData {θ : ℝ}
    (R : RotationReturnData θ) (hqt : Filter.Tendsto R.q Filter.atTop Filter.atTop)
    (hθ : Irrational θ) (H : StandardCenteredOrbitGridProperty θ R.q) :
    Nonempty (ContinuedFractionStarDiscrepancyData θ) :=
  ContinuedFractionStarDiscrepancyData_proved R hqt hθ H

/-- **Task D adapter.**  The canonical-amplitude resonance residual feeds an
active/analytic interface whose amplitude is the canonical loop-holonomy
amplitude.  Re-export of
`canonicalLoopHolonomyAmplitude_satisfies_activeAnalyticInterface`. -/
theorem resonance_residual_feeds_activeAnalyticInterface {θ : ℝ}
    (DK : DenjoyKoksmaReturnData θ) {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hActive : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0)
    (hH : AnalyticOnNhd ℝ (canonicalLoopHolonomyAmplitude θ coeffs ad) (Set.Ioo a₀ b₀))
    (res : StandardCanonicalAmplitudeResonanceProperty DK a₀ b₀ ad coeffs)
    (E : Set ℝ) (hE : E.Finite) :
    ∃ A : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀,
      A.H = canonicalLoopHolonomyAmplitude θ coeffs ad :=
  canonicalLoopHolonomyAmplitude_satisfies_activeAnalyticInterface DK hActive hH res E hE

end CriticalMixedHRT
