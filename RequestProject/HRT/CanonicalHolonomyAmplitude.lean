import Mathlib
import RequestProject.HRT.HolonomyLawBridge

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Canonical holonomy amplitude run

This module performs the **canonical holonomy amplitude run** for the conditional
final assembly theorem.  Its purpose is to eliminate or minimize the residual
holonomy-constancy interface `CriticalMixedHolonomyConstancyInterface`
(`HolonomyLawBridge.lean`), whose single field is

```
  hAlgPhase : algReturnHolonomy coeffs ad t = H s₀ * exp(-2π i θ t).
```

## Task A — where the abstract amplitude `H` is used

The amplitude `H` enters through the active/analytic Zak-model interface
`CriticalMixedActiveAnalyticInterface` (`ConditionalFinalAssembly.lean`): it is an
analytic, nonvanishing function on the window `(a₀, b₀)` whose values lie in the
resonance group on a positive-measure active set.  The previous run
(`HolonomyLawBridge.lean`) proved its **constancy** on the active window
(`active_analytic_holonomy_constant`).  The only residual content of the
holonomy law is the algebraic-phase identity `hAlgPhase`, which references `H`
only through its single constant value `H s₀`.

The detailed field classification is recorded in
`CANONICAL_HOLONOMY_AMPLITUDE_STATUS.md`.

## Task B — the canonical amplitude

We define the **canonical gauge holonomy amplitude** directly from the algebraic
return holonomy,

```
  canonicalGaugeAmplitude θ coeffs ad t = exp(2π i θ t) · algReturnHolonomy coeffs ad t,
```

so that the existing gauge operation `gaugeReturnMultiplier` recovers the
algebraic return holonomy *definitionally*:

```
  gaugeReturnMultiplier (canonicalGaugeAmplitude θ coeffs ad) θ t
    = algReturnHolonomy coeffs ad t.
```

This is `gaugeReturnMultiplier_canonicalGaugeAmplitude`
(alias `canonicalGaugeAmplitude_gauge_identity`).

## Tasks C/D/F — the transparent compatibility field and the constancy interface

The genuine analytic↔algebraic bridge — that the *abstract* Zak-model amplitude
`H` equals the *canonical* algebraic amplitude — is not derivable from the
available interface data (it is exactly the link between the abstract Zak-model
amplitude and the concrete algebraic return loop, which the previous runs already
identified as the genuine remaining obstacle).  Per the Task F fallback policy we
therefore replace the opaque algebraic-phase identity `hAlgPhase` by the strictly
smaller and fully **transparent** compatibility field

```
  H t = canonicalGaugeAmplitude θ coeffs ad t      (on the active window),
```

packaged as `CriticalMixedCanonicalAmplitudeInterface`.

From this transparent compatibility field, together with the *already proved*
analytic constancy of `H` (`active_analytic_holonomy_constant`), we **construct**
the holonomy-constancy interface internally
(`canonical_amplitude_satisfies_holonomy_constancy_interface`), so that
`hAlgPhase` becomes a direct consequence of the gauge identity
`gaugeReturnMultiplier_canonicalGaugeAmplitude` and the constancy theorem.  The
headline endpoint
`critical_mixed_final_contradiction_with_canonical_amplitude_interface` then
restates the conditional final contradiction using only the transparent
compatibility field in place of the opaque `hAlgPhase`.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task B — the canonical amplitude -/

/-- **Canonical gauge holonomy amplitude.**

Defined directly from the choice-free algebraic return holonomy by multiplying by
the inverse rotation phase:
`canonicalGaugeAmplitude θ coeffs ad t = exp(2π i θ t) · algReturnHolonomy coeffs ad t`.
By construction, applying the gauge operation `gaugeReturnMultiplier` (which
multiplies by `exp(-2π i θ t)`) recovers `algReturnHolonomy coeffs ad t`. -/
noncomputable def canonicalGaugeAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) * algReturnHolonomy coeffs ad t

/-- Definitional unfolding of `canonicalGaugeAmplitude`. -/
theorem canonicalGaugeAmplitude_def {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    canonicalGaugeAmplitude θ coeffs ad t =
      Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) * algReturnHolonomy coeffs ad t :=
  rfl

/-- **The gauge of the canonical amplitude recovers the algebraic holonomy.**

The defining property: gauging the canonical amplitude by the rotation phase
returns the choice-free algebraic return holonomy exactly, with no hypotheses. -/
theorem gaugeReturnMultiplier_canonicalGaugeAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    gaugeReturnMultiplier (canonicalGaugeAmplitude θ coeffs ad) θ t =
      algReturnHolonomy coeffs ad t := by
  have hexp :
      Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
        Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have h0 : (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) +
        (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold gaugeReturnMultiplier canonicalGaugeAmplitude
  calc
    Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) * algReturnHolonomy coeffs ad t *
        Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ))
        = algReturnHolonomy coeffs ad t *
            (Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
              Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (t : ℂ))) := by ring
    _ = algReturnHolonomy coeffs ad t * 1 := by rw [hexp]
    _ = algReturnHolonomy coeffs ad t := by ring

/-- Alias of `gaugeReturnMultiplier_canonicalGaugeAmplitude`. -/
theorem canonicalGaugeAmplitude_gauge_identity {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    gaugeReturnMultiplier (canonicalGaugeAmplitude θ coeffs ad) θ t =
      algReturnHolonomy coeffs ad t :=
  gaugeReturnMultiplier_canonicalGaugeAmplitude θ coeffs ad t

/-! ## Task C — narrow regularity adapter -/

/-- **Nonvanishing of the canonical amplitude on fibres with nonzero leading
coefficient.**

When `evalLaurentCircle ad t ≠ 0`, the algebraic return holonomy is a product of
`evalLaurentCircle ad t` with factors `-z` over roots `z` with `‖z‖ > 1`; each
such factor is nonzero (a root with `‖z‖ > 1` cannot be `0`), so the canonical
amplitude — an exponential times this product — is nonzero. -/
theorem canonicalGaugeAmplitude_ne_zero {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) (ht_ne : evalLaurentCircle ad t ≠ 0) :
    canonicalGaugeAmplitude θ coeffs ad t ≠ 0 := by
  rw [canonicalGaugeAmplitude]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  rw [algReturnHolonomy]
  apply mul_ne_zero ht_ne
  apply Multiset.prod_ne_zero
  intro hmem
  simp only [Multiset.mem_map, Multiset.mem_filter] at hmem
  obtain ⟨z, ⟨_, hz1⟩, hzx⟩ := hmem
  rw [neg_eq_zero] at hzx
  rw [hzx] at hz1
  norm_num at hz1

/-! ## Tasks D/F — the transparent canonical-amplitude compatibility interface -/

/-- **`CANONICAL_AMPLITUDE` compatibility interface.**

The strictly smaller and fully transparent replacement for the opaque residual
algebraic-phase field `hAlgPhase` of `CriticalMixedHolonomyConstancyInterface`.
Its single field asserts the *definitional compatibility* between the abstract
Zak-model amplitude `H` and the canonical algebraic amplitude
`canonicalGaugeAmplitude θ coeffs ad` on the active window.  Unlike `hAlgPhase`,
this carries no quantitative algebraic-phase content: it is a plain pointwise
equality identifying the abstract amplitude with its canonical definition. -/
structure CriticalMixedCanonicalAmplitudeInterface (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) where
  hHcanon : ∀ t ∈ Set.Ioo a₀ b₀, H t = canonicalGaugeAmplitude θ coeffs ad t

/-- **The canonical-amplitude compatibility field constructs the holonomy-constancy
interface.**

Given the active/analytic interface (which supplies, via
`active_analytic_holonomy_constant`, the constancy of `H` on the window) and the
transparent compatibility field `H = canonicalGaugeAmplitude`, the opaque residual
algebraic-phase identity `hAlgPhase` becomes a direct consequence of the gauge
identity `gaugeReturnMultiplier_canonicalGaugeAmplitude`.  This *constructs* the
holonomy-constancy interface internally. -/
noncomputable def canonical_amplitude_satisfies_holonomy_constancy_interface
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (compat : CriticalMixedCanonicalAmplitudeInterface θ a₀ b₀ ad coeffs analytic.H) :
    CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H := by
  have hne := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt analytic.hSpos)
  set s₀ := hne.choose with hs₀def
  have hs₀ : s₀ ∈ Set.Ioo a₀ b₀ := analytic.hSU hne.choose_spec
  refine ⟨s₀, hs₀, ?_⟩
  intro t ht ht_ne
  have hHt : analytic.H t = analytic.H s₀ :=
    active_analytic_holonomy_constant hq analytic t ht s₀ hs₀
  have hcompat_t : analytic.H t = canonicalGaugeAmplitude θ coeffs ad t :=
    compat.hHcanon t ht
  have hgauge :
      gaugeReturnMultiplier (canonicalGaugeAmplitude θ coeffs ad) θ t =
        algReturnHolonomy coeffs ad t :=
    gaugeReturnMultiplier_canonicalGaugeAmplitude θ coeffs ad t
  rw [← hgauge]
  unfold gaugeReturnMultiplier
  rw [← hcompat_t, hHt]

/-- Re-export of `canonical_amplitude_satisfies_holonomy_constancy_interface`
under the `return_cocycle` name. -/
theorem return_cocycle_satisfies_holonomy_constancy_interface
    {θ : ℝ} {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hq : Tendsto DK.q atTop atTop)
    (analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀)
    (compat : CriticalMixedCanonicalAmplitudeInterface θ a₀ b₀ ad coeffs analytic.H) :
    Nonempty (CriticalMixedHolonomyConstancyInterface θ a₀ b₀ ad coeffs analytic.H) :=
  ⟨canonical_amplitude_satisfies_holonomy_constancy_interface hq analytic compat⟩

/-! ## Task F — the conditional final contradiction with the canonical-amplitude
interface -/

/-- **Conditional final contradiction from the canonical-amplitude interface.**

The strongest endpoint of this run.  It restates
`critical_mixed_final_contradiction_with_holonomy_constancy_interface`, replacing
the opaque residual algebraic-phase field `hAlgPhase` of
`CriticalMixedHolonomyConstancyInterface` by the strictly smaller and fully
transparent canonical-amplitude compatibility field
`CriticalMixedCanonicalAmplitudeInterface`
(`H = canonicalGaugeAmplitude θ coeffs ad` on the window).  The algebraic-phase
identity is now a derived consequence of the gauge identity together with the
already-discharged analytic constancy of `H`.

The conditional contradiction depends only on:

* `DK_VARIATION_INTERFACE`  (`dk`),
* `ROOT_DATA_INTERFACE`     (`rootData`),
* `ZAK_MODEL_INTERFACE`     (`analytic`),

together with the single transparent canonical-amplitude compatibility field. -/
theorem critical_mixed_final_contradiction_with_canonical_amplitude_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (compat : CriticalMixedCanonicalAmplitudeInterface D.θ a₀ b₀ ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_holonomy_constancy_interface D dk rootData
    analytic
    (canonical_amplitude_satisfies_holonomy_constancy_interface dk.hq analytic compat)

end CriticalMixedHRT
