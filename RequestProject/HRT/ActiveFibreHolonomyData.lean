import Mathlib
import RequestProject.HRT.CanonicalAmplitudeHolonomyCompat

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Active-fibre holonomy data production run

This module performs the **active-fibre holonomy data production run** for the
conditional final assembly theorem.  After the canonical amplitude / holonomy
compatibility run, the entire conditional contradiction is reduced (modulo the
three already-packaged interfaces `DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`,
`ZAK_MODEL_INTERFACE`) to a single active-fibre holonomy identity.  This run

* discharges the **periodic-log construction** (`active_fibre_periodic_log_exists`)
  from the root data alone — it is *not* a blocker;
* isolates the residual as the exact theorem types
  `StandardActiveFibreHolonomyEqualsGaugeMultiplier` (algebraic form) and
  `StandardActiveFibreWindingZeroOnArc` (winding / loop-holonomy form), proved
  inter-derivable given the root data;
* assembles the downstream closure: from any of these forms, together with the
  three packaged interfaces, `False` follows
  (`critical_mixed_final_contradiction_with_active_fibre_holonomy_closed`,
  `critical_mixed_final_contradiction_without_holonomy_amplitude_interface`).

The audit `ACTIVE_FIBRE_HOLONOMY_DATA_STATUS.md` records the exact Lean type of
the genuinely-missing content and the actual-cocycle provenance
(`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`).

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task D — the periodic-log construction (discharged from root data) -/

/-- **Existence of a continuous 1-periodic logarithm of the return loop on each
active fibre (CLOSED_IN_LEAN).**

For every fibre `t` in the active window with nonzero leading coefficient, the
bivariate Laurent return loop `evalBiLaurentPoly coeffs Mlau t` admits a
continuous, `1`-periodic logarithm.  This is synthesised from the root data alone:
the canonical root factorisation `return_multiplier_local_root_factorization`
followed by `evalBiLaurentPoly_periodic_log_of_roots`.  Hence the periodic-log
construction is **not** a residual blocker. -/
theorem active_fibre_periodic_log_exists
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ ell : ℝ → ℂ, IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t) := by
  intro t ht ht_ne
  obtain ⟨r, hfact, hrootmap⟩ :=
    return_multiplier_local_root_factorization coeffs ad rootData.h_ad_coeff t ht_ne
  have hrootmap' : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val := hrootmap
  obtain ⟨hoff, hM, _hm⟩ := rootData.hroots_min t ht ht_ne
  have hr_off : ∀ i, ‖r i‖ ≠ 1 := root_offcircle_transfer r _ hrootmap' hoff
  have hMint : Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) := by
    rw [hM, root_count_transfer r _ hrootmap' (fun z => ‖z‖ < 1)]
  exact evalBiLaurentPoly_periodic_log_of_roots Mlau coeffs t (evalLaurentCircle ad t)
    ht_ne r hr_off hMint hfact

/-! ## Tasks C/D/F — the exact residual blocker types -/

/-- **`STANDARD_ACTIVE_FIBRE_HOLONOMY_EQUALS_GAUGE_MULTIPLIER` (algebraic form).**

The smallest exact form of the residual active-fibre holonomy identity: on the
active arc, the analytic gauge value equals the choice-free algebraic loop
holonomy.  An alias of the inter-derivable
`StandardGaugeMultiplierEqualsAlgHolonomy` isolated by the previous run. -/
abbrev StandardActiveFibreHolonomyEqualsGaugeMultiplier (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (H : ℝ → ℂ) :=
  StandardGaugeMultiplierEqualsAlgHolonomy θ a₀ b₀ ad coeffs H

/-- **`STANDARD_ACTIVE_FIBRE_WINDING_ZERO_ON_ARC` (winding / loop-holonomy form).**

The winding-form of the residual: on the active arc, the analytic gauge value
equals the loop holonomy `exp(∫₀¹ ell_t)` of **any** continuous `1`-periodic
logarithm of the return loop.  (The independence of the right-hand side from the
choice of `ell_t` is the already-proved
`return_multiplier_holonomy_eq_integral_log`; this datum is the statement that the
return cocycle carries *zero net winding* on the active arc.) -/
structure StandardActiveFibreWindingZeroOnArc (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) where
  hHoloZero : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
      gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)

/-- **`STANDARD_ACTIVE_FIBRE_HOLONOMY_DATA` (full holonomy package).**

The complete active-fibre holonomy interface — the gauge function `J`, its
relation to the analytic amplitude `H`, and the choice-free holonomy
identification.  An alias of `CriticalMixedWindingInterface`. -/
abbrev StandardActiveFibreHolonomyData (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) :=
  CriticalMixedWindingInterface θ a₀ b₀ Mlau ad coeffs H

/-! ## Task C — inter-derivability of the algebraic and winding forms -/

/-- **The algebraic holonomy identity yields winding-zero on the active arc.**

Given the algebraic form (gauge value = `algReturnHolonomy`) and the root data,
the winding form (gauge value = loop holonomy of any periodic log) holds on the
active arc, because the loop holonomy equals `algReturnHolonomy`
(`return_multiplier_holonomy_eq_integral_log`).  This is Task C
(`active_fibre_winding_zero` / `active_arc_zero_winding`). -/
def return_multiplier_winding_zero_on_active_arc
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (alg : StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H where
  hHoloZero := fun t ht ht_ne ell_t hell =>
    return_multiplier_holonomy_identification mlau Mlau ad coeffs rootData.h_ad_coeff
      H θ t ht_ne (rootData.hroots_min t ht ht_ne) (alg.hJalg t ht ht_ne) ell_t hell

/-- Re-export under the `active_fibre_winding_zero` name. -/
def active_fibre_winding_zero
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (alg : StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H :=
  return_multiplier_winding_zero_on_active_arc rootData alg

/-- Re-export under the `active_arc_zero_winding` name. -/
def active_arc_zero_winding
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (alg : StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H :=
  return_multiplier_winding_zero_on_active_arc rootData alg

/-- **Winding-zero on the active arc yields the algebraic holonomy identity.**

The converse direction: given the winding form together with the root data, the
algebraic form follows.  A periodic log exists on each active fibre
(`active_fibre_periodic_log_exists`), and its loop holonomy equals
`algReturnHolonomy` (`return_multiplier_holonomy_eq_integral_log`). -/
def StandardActiveFibreWindingZeroOnArc.toHolonomyEqualsGaugeMultiplier
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (w : StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H) :
    StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs H where
  hJalg := by
    intro t ht ht_ne
    obtain ⟨ell, hell⟩ := active_fibre_periodic_log_exists rootData t ht ht_ne
    rw [w.hHoloZero t ht ht_ne ell hell,
      return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs rootData.h_ad_coeff
        t ht_ne (rootData.hroots_min t ht ht_ne) ell hell]

/-! ## Task D — the holonomy amplitude / gauge identification -/

/-- **The active-fibre holonomy function equals the gauge of the amplitude.**

For the full active-fibre holonomy data, the holonomy function `J` agrees with
the gauge `gaugeReturnMultiplier H θ` of the analytic amplitude on the active
window.  (This is the `hJgauge` content in `gaugeReturnMultiplier` form.) -/
theorem active_fibre_holonomy_eq_gaugeReturnMultiplier
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (holo : StandardActiveFibreHolonomyData θ a₀ b₀ Mlau ad coeffs H) :
    ∀ s ∈ Set.Ioo a₀ b₀, holo.J s = gaugeReturnMultiplier H θ s := by
  intro s hs
  rw [holo.hJgauge s hs, gaugeReturnMultiplier]

/-- **The winding form constructs the full active-fibre holonomy data.**

From the winding-zero datum we build the full holonomy package
`StandardActiveFibreHolonomyData` (`CriticalMixedWindingInterface`), with the
gauge supplied internally as `gaugeReturnMultiplier H θ`. -/
noncomputable def StandardActiveFibreWindingZeroOnArc.toHolonomyData
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (w : StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H) :
    StandardActiveFibreHolonomyData θ a₀ b₀ Mlau ad coeffs H where
  J := gaugeReturnMultiplier H θ
  hJgauge := fun _ _ => rfl
  hJholo := w.hHoloZero

/-- Re-export: `active_fibre_holonomy_amplitude` builds the holonomy package from
the winding-zero datum. -/
noncomputable def active_fibre_holonomy_amplitude
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {H : ℝ → ℂ}
    (w : StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H) :
    StandardActiveFibreHolonomyData θ a₀ b₀ Mlau ad coeffs H :=
  w.toHolonomyData

/-! ## Task E — downstream closure -/

/-- **Conditional final contradiction with the active-fibre holonomy data closed.**

From a normalized critical mixed four-term relation and the three packaged
interfaces (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`, `ZAK_MODEL_INTERFACE`)
together with the active-fibre holonomy data (in winding-zero form), the project
derives `False`. -/
theorem critical_mixed_final_contradiction_with_active_fibre_holonomy_closed
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (holo : StandardActiveFibreWindingZeroOnArc D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_interfaces D dk rootData analytic
    holo.toHolonomyData

/-- **Conditional final contradiction with the active-fibre holonomy data closed
(algebraic form).**

The same closure starting from the smallest exact blocker
`StandardActiveFibreHolonomyEqualsGaugeMultiplier` (gauge value = algebraic loop
holonomy on the active arc). -/
theorem critical_mixed_final_contradiction_with_active_fibre_holonomy_eq_gauge
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (alg : StandardActiveFibreHolonomyEqualsGaugeMultiplier D.θ a₀ b₀ ad coeffs
      analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_active_fibre_holonomy_closed D dk rootData
    analytic (return_multiplier_winding_zero_on_active_arc rootData alg)

/-- **Conditional final contradiction without an explicit holonomy-amplitude
interface.**

The full active-fibre holonomy package (`CriticalMixedWindingInterface`) plus the
three packaged interfaces yields `False`, with the canonical-amplitude
compatibility derived internally rather than assumed.  This certifies that the
residual analytic↔algebraic bridge *is* the content of the active-fibre
return-cocycle holonomy interface (re-export of
`critical_mixed_final_contradiction_with_winding_canonical_amplitude_closed`). -/
theorem critical_mixed_final_contradiction_without_holonomy_amplitude_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (holo : StandardActiveFibreHolonomyData D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_with_winding_canonical_amplitude_closed D dk
    rootData analytic holo

end CriticalMixedHRT
