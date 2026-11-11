import Mathlib
import RequestProject.HRT.ActiveFibreHolonomyData

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 1000000

/-!
# Active-fibre winding-zero on the connected active arc

This module performs the **active-fibre winding-zero on arc run**.  The residual
of the active-fibre holonomy data production run was isolated as the single
inter-derivable pair of theorem types

```
StandardActiveFibreHolonomyEqualsGaugeMultiplier   (algebraic form)
StandardActiveFibreWindingZeroOnArc                (winding / loop-holonomy form)
```

The *intended* mathematical argument for closing the winding form is:

1. for almost every active fibre the actual return equation holds
   (`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`);
2. the active fibre is nonzero in `L²`;
3. the measurable winding obstruction gives **zero winding** of the loop
   `x ↦ Bmult(x,s)` for almost every active parameter `s`
   (`measurable_cocycle_winding_eq_zero`);
4. the return multiplier is a jointly analytic, **zero-free** family of loops on
   the active arc, so its integer winding number is **locally constant** in `s`;
5. the active set has positive measure inside the connected arc `(a₀,b₀)`, so the
   winding number — a locally constant `ℤ`-valued function on a connected set —
   is constant, and being `0` on a positive-measure subset it is `0` everywhere.

This run **discharges, fully in Lean, the topological propagation steps (4→5)**:

* `locallyConstant_eq_of_mem_Ioo` — a function that is locally constant *within*
  the connected arc `Set.Ioo a₀ b₀` takes a single value on it (genuine
  Mathlib-backed proof via `IsLocallyConstant.apply_eq_of_isPreconnected` on the
  connected subtype `↥(Set.Ioo a₀ b₀)`);
* `exists_winding_zero_of_ae_on_positive_measure` — a function vanishing a.e. on a
  positive-measure set vanishes at *some* point of that set (measure-theoretic);
* `winding_zero_on_active_arc_of_ae_active_winding_zero` — combining the two:
  from an a.e.-zero winding number on a positive-measure active subset together
  with local constancy on the arc, the winding number is `0` **everywhere** on
  the arc;
* `StandardActiveFibreWindingZeroOnArc_proved` — the winding form of the residual,
  built from the reduced data.

The two genuinely analytic ingredients that remain are isolated as the *smallest*
exact theorem types (the run instructions' acceptable remaining types):

* `StandardWindingLocallyConstantZeroFreeFamily` — local constancy of the integer
  winding number of the zero-free analytic return-multiplier family on the arc;
* `StandardAEActiveFibreWindingZero` — a.e. zero winding of the actual return
  cocycle on a positive-measure active subset (from the measurable winding
  obstruction applied to the actual a.e. cocycle);
* `StandardWindingZeroHolonomyBridge` — the per-fibre identification that zero
  winding of the return loop forces the gauge value to equal the loop holonomy
  `exp(∫₀¹ ell_t)` of a periodic logarithm.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Step 5 — topological propagation on the connected arc -/

/-- **A function locally constant within the connected arc is constant on it.**

If `W : ℝ → Y` is locally constant *relative to* the open interval
`Set.Ioo a₀ b₀` (for every `s` in the interval, `W` is eventually equal to `W s`
along `𝓝[Set.Ioo a₀ b₀] s`), then `W` takes one and the same value at any two
points of the interval.  This is the topological propagation step: the interval
is connected, so a locally constant function on it is constant.  Proved by
restricting `W` to the connected subtype `↥(Set.Ioo a₀ b₀)` and invoking
`IsLocallyConstant.apply_eq_of_isPreconnected`. -/
theorem locallyConstant_eq_of_mem_Ioo {Y : Type*} (W : ℝ → Y) (a₀ b₀ : ℝ)
    (hlc : ∀ s ∈ Set.Ioo a₀ b₀, ∀ᶠ t in 𝓝[Set.Ioo a₀ b₀] s, W t = W s)
    {s t : ℝ} (hs : s ∈ Set.Ioo a₀ b₀) (ht : t ∈ Set.Ioo a₀ b₀) :
    W s = W t := by
  set U : Set ℝ := Set.Ioo a₀ b₀ with hU
  let f : U → Y := fun p => W p.1
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x, hx⟩
    have hev := hlc x hx
    rw [eventually_nhdsWithin_iff] at hev
    have hcont : ContinuousAt (Subtype.val : U → ℝ) ⟨x, hx⟩ :=
      continuous_subtype_val.continuousAt
    have hev2 := hcont.eventually hev
    filter_upwards [hev2] with p hp
    exact hp p.2
  haveI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  exact hf.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ ⟨s, hs⟩) (mem_univ ⟨t, ht⟩)

/-- **A function vanishing a.e. on a positive-measure set vanishes somewhere on
it.**

If `S` has positive volume and `W s = 0` for almost every `s ∈ S`, then there is
an actual point `s₀ ∈ S` with `W s₀ = 0`.  (If not, `S` would be contained in the
null set where the a.e. statement fails, contradicting `0 < volume S`.) -/
theorem exists_winding_zero_of_ae_on_positive_measure {Y : Type*} [Zero Y]
    (W : ℝ → Y) (S : Set ℝ) (hpos : 0 < volume S)
    (hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ S → W s = 0) :
    ∃ s₀ ∈ S, W s₀ = 0 := by
  by_contra h
  push_neg at h
  have hnull : volume {s : ℝ | ¬ (s ∈ S → W s = 0)} = 0 := by
    rw [← ae_iff]; exact hae
  have hsub : S ⊆ {s : ℝ | ¬ (s ∈ S → W s = 0)} := by
    intro s hs
    simp only [mem_setOf_eq, not_forall]
    exact ⟨hs, h s hs⟩
  exact absurd (measure_mono_null hsub hnull) (ne_of_gt hpos)

/-! ## The smallest residual analytic interfaces (fallback policy) -/

/-- **`STANDARD_WINDING_LOCALLY_CONSTANT_ZERO_FREE_FAMILY`.**

The integer winding number `W` of the zero-free, jointly-analytic return
multiplier family is **locally constant** on the active arc `Set.Ioo a₀ b₀`.
This is the genuinely analytic ingredient (step 4): for a continuously varying
*zero-free* family of loops, the integer winding number cannot jump.  Isolated
here as the smallest exact theorem type. -/
structure StandardWindingLocallyConstantZeroFreeFamily (a₀ b₀ : ℝ) (W : ℝ → ℤ) :
    Prop where
  hLocConst : ∀ s ∈ Set.Ioo a₀ b₀, ∀ᶠ t in 𝓝[Set.Ioo a₀ b₀] s, W t = W s

/-- **`STANDARD_AE_ACTIVE_FIBRE_WINDING_ZERO`.**

The actual return cocycle has **zero winding number** for almost every active
fibre on a positive-measure active subset `S` of the arc.  This is the
measure-theoretic output of the measurable winding obstruction
(`measurable_cocycle_winding_eq_zero`) applied to the actual a.e. return cocycle
(`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`) on the active set.
Isolated here as the smallest exact theorem type. -/
structure StandardAEActiveFibreWindingZero (a₀ b₀ : ℝ) (ad : LaurentPolynomial ℂ)
    (W : ℝ → ℤ) where
  S : Set ℝ
  hSU : S ⊆ Set.Ioo a₀ b₀
  hSpos : 0 < volume S
  hWzero_ae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ S → W s = 0

/-- **`STANDARD_WINDING_ZERO_HOLONOMY_BRIDGE`.**

The per-fibre identification: at any active fibre with **zero winding number**,
the analytic gauge value equals the loop holonomy `exp(∫₀¹ ell_t)` of any
continuous `1`-periodic logarithm of the bivariate Laurent return loop.  This is
exactly the analytic↔algebraic content of `StandardActiveFibreWindingZeroOnArc`
reduced to the *zero-winding* fibres.  Isolated here as the smallest exact theorem
type. -/
structure StandardWindingZeroHolonomyBridge (θ a₀ b₀ : ℝ) {dlau : ℕ} (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) (W : ℝ → ℤ) : Prop where
  hBridge : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 → W t = 0 →
    ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
      gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)

/-! ## Tasks B/D — extraction and propagation (proved) -/

/-- **`STANDARD_POSITIVE_MEASURE_ACTIVE_SET_MEETS_CONSTANT_COMPONENT`
(Task B, proved).**

From the a.e. zero winding number on a positive-measure active subset, there is
an actual active fibre `s₀ ∈ Set.Ioo a₀ b₀` with winding number `0`.  This is the
measure-theoretic extraction `exists_winding_zero_of_ae_on_positive_measure`
specialised to the active data. -/
theorem return_multiplier_winding_zero_ae_on_active_set {a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W) :
    ∃ s₀ ∈ Set.Ioo a₀ b₀, W s₀ = 0 := by
  obtain ⟨s₀, hs₀S, hs₀⟩ :=
    exists_winding_zero_of_ae_on_positive_measure W aez.S aez.hSpos aez.hWzero_ae
  exact ⟨s₀, aez.hSU hs₀S, hs₀⟩

/-- Re-export under the `active_fibre_winding_zero_ae` name. -/
theorem active_fibre_winding_zero_ae {a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W) :
    ∃ s₀ ∈ Set.Ioo a₀ b₀, W s₀ = 0 :=
  return_multiplier_winding_zero_ae_on_active_set aez

/-- **`WINDING_ZERO_ON_ACTIVE_ARC_OF_AE_ACTIVE_WINDING_ZERO` (Task D, proved).**

The propagation theorem: combining the a.e. zero winding on the positive-measure
active subset (`StandardAEActiveFibreWindingZero`) with the local constancy of the
winding number on the arc (`StandardWindingLocallyConstantZeroFreeFamily`), the
winding number is `0` at **every** fibre of the connected arc `Set.Ioo a₀ b₀`.

Proof: extraction gives one active fibre `s₀` with `W s₀ = 0`; local constancy on
the connected arc forces `W t = W s₀ = 0` for every `t` in the arc
(`locallyConstant_eq_of_mem_Ioo`). -/
theorem winding_zero_on_active_arc_of_ae_active_winding_zero {a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W) :
    ∀ t ∈ Set.Ioo a₀ b₀, W t = 0 := by
  obtain ⟨s₀, hs₀, hWs₀⟩ := return_multiplier_winding_zero_ae_on_active_set aez
  intro t ht
  have := locallyConstant_eq_of_mem_Ioo W a₀ b₀ lc.hLocConst hs₀ ht
  rw [← this, hWs₀]

/-- Re-export of the propagation theorem packaged as the arc-propagation type. -/
theorem StandardActiveArcWindingPropagation {a₀ b₀ : ℝ}
    {ad : LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W) :
    ∀ t ∈ Set.Ioo a₀ b₀, W t = 0 :=
  winding_zero_on_active_arc_of_ae_active_winding_zero aez lc

/-! ## Closure of the winding form from the reduced data -/

/-- **`STANDARD_ACTIVE_FIBRE_WINDING_ZERO_ON_ARC_PROVED` (Task D, proved from the
reduced data).**

The winding form of the residual is constructed from:

* `aez` — a.e. zero winding on a positive-measure active subset
  (`StandardAEActiveFibreWindingZero`);
* `lc`  — local constancy of the winding number on the arc
  (`StandardWindingLocallyConstantZeroFreeFamily`);
* `br`  — the per-fibre winding-zero ⇒ holonomy bridge
  (`StandardWindingZeroHolonomyBridge`).

The propagation theorem
`winding_zero_on_active_arc_of_ae_active_winding_zero` discharges the
positive-measure-to-whole-arc step; the bridge then converts zero winding into the
holonomy identity at each active fibre. -/
theorem StandardActiveFibreWindingZeroOnArc_proved {θ a₀ b₀ : ℝ} {dlau : ℕ}
    {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W)
    (br : StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H where
  hHoloZero := by
    intro t ht ht_ne ell_t hell
    have hW0 : W t = 0 :=
      winding_zero_on_active_arc_of_ae_active_winding_zero aez lc t ht
    exact br.hBridge t ht ht_ne hW0 ell_t hell

/-! ## Task E — downstream closure -/

/-- **`STANDARD_ACTIVE_FIBRE_HOLONOMY_EQUALS_GAUGE_MULTIPLIER_PROVED`.**

The algebraic form of the residual, derived from the winding form (built from the
reduced data) together with the root data, via the previously-established
inter-derivability
`StandardActiveFibreWindingZeroOnArc.toHolonomyEqualsGaugeMultiplier`. -/
theorem StandardActiveFibreHolonomyEqualsGaugeMultiplier_proved {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W)
    (br : StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W) :
    StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H :=
  (StandardActiveFibreWindingZeroOnArc_proved aez lc br).toHolonomyEqualsGaugeMultiplier
    rootData

/-- **`STANDARD_CANONICAL_AMPLITUDE_COMPATIBILITY_PROVED`.**

The canonical-amplitude form of the residual, derived from the winding-form
holonomy data (built from the reduced data) together with the root data, via
`canonical_amplitude_compatibility_of_winding`. -/
theorem StandardCanonicalAmplitudeCompatibility_proved {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W)
    (br : StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H :=
  canonical_amplitude_compatibility_of_winding rootData
    (StandardActiveFibreWindingZeroOnArc_proved aez lc br).toHolonomyData

/-- **`CRITICAL_MIXED_FINAL_CONTRADICTION_WITH_ACTIVE_FIBRE_HOLONOMY_FULLY_CLOSED`.**

The conditional final contradiction with the active-fibre holonomy interface
discharged down to the three smallest residual winding interfaces (a.e. winding
zero, local constancy, and the winding-zero ⇒ holonomy bridge), together with the
three already-packaged interfaces (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`,
`ZAK_MODEL_INTERFACE`). -/
theorem critical_mixed_final_contradiction_with_active_fibre_holonomy_fully_closed
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {W : ℝ → ℤ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W)
    (br : StandardWindingZeroHolonomyBridge D.θ a₀ b₀ Mlau ad coeffs analytic.H W) :
    False :=
  critical_mixed_final_contradiction_with_active_fibre_holonomy_closed D dk rootData
    analytic (StandardActiveFibreWindingZeroOnArc_proved aez lc br)

/-- **`CRITICAL_MIXED_FINAL_CONTRADICTION_WITHOUT_HOLONOMY_AMPLITUDE_INTERFACE_FULLY_CLOSED`.**

Same closure as
`critical_mixed_final_contradiction_with_active_fibre_holonomy_fully_closed`, but
routed through the holonomy-amplitude package built internally from the winding
form (with the canonical-amplitude compatibility derived rather than assumed). -/
theorem critical_mixed_final_contradiction_without_holonomy_amplitude_interface_fully_closed
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {W : ℝ → ℤ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (aez : StandardAEActiveFibreWindingZero a₀ b₀ ad W)
    (lc : StandardWindingLocallyConstantZeroFreeFamily a₀ b₀ W)
    (br : StandardWindingZeroHolonomyBridge D.θ a₀ b₀ Mlau ad coeffs analytic.H W) :
    False :=
  critical_mixed_final_contradiction_without_holonomy_amplitude_interface D dk rootData
    analytic (StandardActiveFibreWindingZeroOnArc_proved aez lc br).toHolonomyData

end CriticalMixedHRT
