import Mathlib
import RequestProject.HRT.CanonicalLoopHolonomyAmplitude
import RequestProject.HRT.CanonicalAmplitudeHolonomyCompat

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 1000000

/-!
# Active/analytic amplitude reanchoring run

This run eliminates the residual **opaque-`analytic.H` compatibility**

```
  StandardCanonicalAmplitudeCompatibility D.θ a₀ b₀ ad coeffs analytic.H
```

from the downstream contradiction, by **reanchoring** the active/analytic
interface onto the canonical loop-holonomy amplitude
`canonicalLoopHolonomyAmplitude θ coeffs ad` (which is, definitionally, the
canonical gauge amplitude `canonicalGaugeAmplitude θ coeffs ad`).

## Task B — where `analytic.H` is introduced

The amplitude `analytic.H` is the field `H` of the structure
`CriticalMixedActiveAnalyticInterface θ DK a₀ b₀`
(`ConditionalFinalAssembly.lean`):

* `H : ℝ → ℂ`                                  — **arbitrary data**;
* `hH  : AnalyticOnNhd ℝ H (Ioo a₀ b₀)`        — uses `H`;
* `hHne : ∀ s ∈ Ioo a₀ b₀, H s ≠ 0`           — uses `H`;
* `hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q` — uses `H`.

For the canonical loop-holonomy amplitude:

* `hHne` is **proved** (`canonicalGaugeAmplitude_ne_zero`) on the active arc;
* `StandardCanonicalAmplitudeCompatibility` is **proved** by `rfl`
  (`StandardCanonicalAmplitudeCompatibility_canonical`);
* `hH` (analyticity) and `hSres` (resonance membership of the canonical
  amplitude values on a positive-measure set) are the genuine remaining
  active/analytic content, and are now stated **about the concrete canonical
  amplitude** rather than an opaque `H`.

## Task D/E — the reanchored interface and the opaque-`H`-free endpoint

`StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude` packages an
active/analytic interface whose amplitude `H` **is** the canonical loop-holonomy
amplitude.  For it the compatibility is automatic (`rfl`), so the downstream
contradiction
`critical_mixed_final_contradiction_without_opaque_amplitude` no longer requires
an externally supplied compatibility for an opaque `analytic.H`.

A transparent builder `…ofData` reduces this residual to exactly the genuine
active/analytic content **about the canonical amplitude**: the window is active
(`hActive`), the canonical amplitude is analytic (`hH`), and its values lie in
the resonance group on a positive-measure set (`StandardCanonicalAmplitudeResonanceProperty`).

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task C — the canonical amplitude satisfies the compatibility (already `rfl`) -/

/-- **`canonicalLoopHolonomyAmplitude_satisfies_canonical_compat`.**

The canonical loop-holonomy amplitude satisfies the canonical-amplitude
compatibility interface (definitionally). -/
theorem canonicalLoopHolonomyAmplitude_satisfies_canonical_compat {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs
      (canonicalLoopHolonomyAmplitude θ coeffs ad) :=
  StandardCanonicalAmplitudeCompatibility_canonical

/-- **`StandardOpaqueAnalyticAmplitudeEqualsCanonical`.**

The smallest exact identification residual: an opaque amplitude `H` equals the
canonical loop-holonomy amplitude on the active arc.  This is precisely
`StandardCanonicalAmplitudeCompatibility` (with the canonical amplitude written
in loop-holonomy form), recorded here under its descriptive name. -/
structure StandardOpaqueAnalyticAmplitudeEqualsCanonical (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) where
  hEq : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    H t = canonicalLoopHolonomyAmplitude θ coeffs ad t

/-- An opaque-amplitude identification yields the canonical compatibility. -/
def StandardOpaqueAnalyticAmplitudeEqualsCanonical.toCompat {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ}
    (h : StandardOpaqueAnalyticAmplitudeEqualsCanonical θ a₀ b₀ ad coeffs H) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H where
  hHcanon_active := fun t ht ht_ne => h.hEq t ht ht_ne

/-! ## Task C/F — the resonance residual for the canonical amplitude -/

/-- **`StandardCanonicalAmplitudeResonanceProperty`.**

The genuine remaining active/analytic content, stated about the **concrete**
canonical loop-holonomy amplitude (not an opaque `H`): a positive-measure active
set `S ⊆ (a₀,b₀)` on which the canonical amplitude takes values in the resonance
group of the return times `DK.q`. -/
structure StandardCanonicalAmplitudeResonanceProperty {θ : ℝ}
    (DK : DenjoyKoksmaReturnData θ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) where
  S : Set ℝ
  hSU : S ⊆ Set.Ioo a₀ b₀
  hSpos : 0 < MeasureTheory.volume S
  hSres : ∀ s ∈ S,
    canonicalLoopHolonomyAmplitude θ coeffs ad s ∈ resonanceGroupC DK.q

/-! ## Task D — the reanchored active/analytic interface using the canonical `H` -/

/-- **`StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude`.**

A reanchored active/analytic interface whose amplitude field `H` **is** the
canonical loop-holonomy amplitude.  This is the smallest exact residual: it
asserts that the canonical loop-holonomy amplitude is itself a valid
active/analytic amplitude (analytic, nonvanishing, resonance-valued on a
positive-measure set).  All downstream holonomy compatibility is then automatic
(`compat` below is `rfl`). -/
structure StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude {θ : ℝ}
    (DK : DenjoyKoksmaReturnData θ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) where
  analytic : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀
  hH_canonical : analytic.H = canonicalLoopHolonomyAmplitude θ coeffs ad

/-- **The reanchored interface yields the canonical-amplitude compatibility for
free.**

Because the amplitude of a reanchored interface *is* the canonical loop-holonomy
amplitude, the compatibility statement `analytic.H = canonical` on the active arc
holds by `rfl`, so no opaque-`H` compatibility need be supplied externally. -/
def StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude.compat {θ : ℝ}
    {DK : DenjoyKoksmaReturnData θ} {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (h : StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude DK a₀ b₀ ad coeffs) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs h.analytic.H where
  hHcanon_active := fun t _ _ => by
    rw [h.hH_canonical, canonicalLoopHolonomyAmplitude_eq_canonicalGaugeAmplitude]

/-- **`canonical_active_analytic_interface` / `…ofData` (Task D builder).**

Transparent constructor of the reanchored interface from the genuine remaining
content **about the canonical amplitude**: activeness of the window (`hActive`),
analyticity of the canonical amplitude (`hH`), and its resonance property
(`res`).  The nonvanishing field `hHne` is discharged automatically via
`canonicalGaugeAmplitude_ne_zero`. -/
noncomputable def StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude.ofData {θ : ℝ}
    (DK : DenjoyKoksmaReturnData θ) {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hActive : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0)
    (hH : AnalyticOnNhd ℝ (canonicalLoopHolonomyAmplitude θ coeffs ad) (Set.Ioo a₀ b₀))
    (res : StandardCanonicalAmplitudeResonanceProperty DK a₀ b₀ ad coeffs)
    (E : Set ℝ) (hE : E.Finite) :
    StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude DK a₀ b₀ ad coeffs where
  analytic :=
    { H := canonicalLoopHolonomyAmplitude θ coeffs ad
      hH := hH
      hHne := fun s hs => canonicalGaugeAmplitude_ne_zero θ coeffs ad s (hActive s hs)
      S := res.S
      hSU := res.hSU
      hSpos := res.hSpos
      hSres := res.hSres
      E := E
      hE := hE }
  hH_canonical := rfl

/-- **`canonicalLoopHolonomyAmplitude_satisfies_activeAnalyticInterface`.**

Existence form of the reanchored interface: given the genuine active/analytic
content about the canonical amplitude, there is an active/analytic interface
whose amplitude is the canonical loop-holonomy amplitude. -/
theorem canonicalLoopHolonomyAmplitude_satisfies_activeAnalyticInterface {θ : ℝ}
    (DK : DenjoyKoksmaReturnData θ) {a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (hActive : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0)
    (hH : AnalyticOnNhd ℝ (canonicalLoopHolonomyAmplitude θ coeffs ad) (Set.Ioo a₀ b₀))
    (res : StandardCanonicalAmplitudeResonanceProperty DK a₀ b₀ ad coeffs)
    (E : Set ℝ) (hE : E.Finite) :
    ∃ A : CriticalMixedActiveAnalyticInterface θ DK a₀ b₀,
      A.H = canonicalLoopHolonomyAmplitude θ coeffs ad :=
  let h := StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude.ofData DK hActive hH res E hE
  ⟨h.analytic, h.hH_canonical⟩

/-! ## Task E — the downstream contradiction without opaque `analytic.H` -/

/-- **`critical_mixed_final_contradiction_with_canonical_H`.**

The downstream contradiction with the active/analytic amplitude reanchored to the
canonical loop-holonomy amplitude.  The compatibility is supplied internally by
`StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude.compat` (`rfl`); **no**
opaque-`H` compatibility is required as a hypothesis. -/
theorem critical_mixed_final_contradiction_with_canonical_H
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (canon : StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude
      dk.returnData a₀ b₀ ad coeffs) :
    False :=
  critical_mixed_final_contradiction_with_canonical_amplitude_compat D dk rootData
    canon.analytic canon.compat

/-- Alias of `critical_mixed_final_contradiction_with_canonical_H`. -/
theorem critical_mixed_final_contradiction_without_opaque_amplitude
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (canon : StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude
      dk.returnData a₀ b₀ ad coeffs) :
    False :=
  critical_mixed_final_contradiction_with_canonical_H D dk rootData canon

/-- **`active_analytic_interface_reanchored_to_canonical_H`.**

The fully transparent endpoint: from the DK and root data, the activeness of the
window, the analyticity of the canonical amplitude, and the canonical-amplitude
resonance property, the contradiction follows — with the active/analytic
amplitude reanchored to the canonical loop-holonomy amplitude and **no** opaque
amplitude anywhere. -/
theorem active_analytic_interface_reanchored_to_canonical_H
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (hActive : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0)
    (hH : AnalyticOnNhd ℝ (canonicalLoopHolonomyAmplitude D.θ coeffs ad) (Set.Ioo a₀ b₀))
    (res : StandardCanonicalAmplitudeResonanceProperty dk.returnData a₀ b₀ ad coeffs)
    (E : Set ℝ) (hE : E.Finite) :
    False :=
  critical_mixed_final_contradiction_with_canonical_H D dk rootData
    (StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude.ofData
      dk.returnData hActive hH res E hE)

end CriticalMixedHRT
