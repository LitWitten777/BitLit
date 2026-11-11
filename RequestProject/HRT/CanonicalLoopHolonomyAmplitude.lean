import Mathlib
import RequestProject.HRT.ZeroWindingPeriodicLogBridge

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 1000000

/-!
# Canonical loop-holonomy amplitude reanchoring run

The zero-winding periodic-log holonomy bridge run reduced the holonomy layer to
the single blocker

```
StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W
```

whose field `hLoop` quantifies over an **arbitrary** amplitude `H`:

```
  ∀ t ∈ (a₀,b₀), evalLaurentCircle ad t ≠ 0 → W t = 0 →
    ∀ ell, IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t) →
      gaugeReturnMultiplier H θ t = exp(∫₀¹ ell).
```

For an arbitrary `H` this identity is genuinely unprovable: `H` is *a priori*
unrelated to the algebraic return data.  This run therefore **reanchors** the
holonomy layer onto a *canonical* amplitude defined directly by the loop holonomy:

```
  H_loop(t) := exp(2π i θ t) · exp(∫₀¹ ell_t) = exp(2π i θ t) · algReturnHolonomy coeffs ad t,
```

where `ell_t` is a periodic logarithm of the return multiplier loop.  This is
exactly the existing `canonicalGaugeAmplitude`, since (by the already-proved
`return_multiplier_holonomy_eq_integral_log`) `exp(∫₀¹ ell_t)` is independent of
the choice of `ell_t` and equals `algReturnHolonomy coeffs ad t`.

For this canonical amplitude every holonomy / canonical-amplitude compatibility
interface is **proved unconditionally** (given the root data), so the abstract-`H`
loop bridge is superseded: the genuine residual collapses to the transparent
compatibility statement "`H = H_loop` on the active arc"
(`StandardCanonicalAmplitudeCompatibility`), of which the canonical amplitude is
the canonical witness.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task B — the canonical loop-holonomy amplitude -/

/-- **Canonical loop-holonomy amplitude `H_loop`.**

Defined directly from the loop holonomy of the return multiplier:

```
  loopHolonomyAmplitude θ coeffs ad t
    = exp(2π i θ t) · algReturnHolonomy coeffs ad t
    = exp(2π i θ t) · exp(∫₀¹ ell_t)      (for any periodic log ell_t),
```

i.e. the rotation phase times the loop holonomy `exp(∫ ell_t)`.  This reuses the
existing `canonicalGaugeAmplitude`; the second equality is
`loopHolonomyAmplitude_eq_exp_integral`. -/
noncomputable def loopHolonomyAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) : ℂ :=
  canonicalGaugeAmplitude θ coeffs ad t

/-- Active-arc alias for `loopHolonomyAmplitude`. -/
noncomputable def activeLoopHolonomyAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) : ℂ :=
  loopHolonomyAmplitude θ coeffs ad t

/-- Canonical alias for `loopHolonomyAmplitude`. -/
noncomputable def canonicalLoopHolonomyAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) : ℂ :=
  loopHolonomyAmplitude θ coeffs ad t

/-- `canonicalLoopHolonomyAmplitude` is, by definition, `canonicalGaugeAmplitude`. -/
theorem canonicalLoopHolonomyAmplitude_eq_canonicalGaugeAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    canonicalLoopHolonomyAmplitude θ coeffs ad t = canonicalGaugeAmplitude θ coeffs ad t :=
  rfl

/-- Definitional unfolding of the canonical loop-holonomy amplitude as the
rotation phase times the choice-free algebraic loop holonomy. -/
theorem loopHolonomyAmplitude_def {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    loopHolonomyAmplitude θ coeffs ad t =
      Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) * algReturnHolonomy coeffs ad t :=
  rfl

/-- **The canonical loop-holonomy amplitude really is `exp(2π i θ t) · exp(∫ ell)`.**

For any periodic logarithm `ell` of the bivariate return loop at an active fibre
(with the geometric root data), the canonical loop-holonomy amplitude factors as
the rotation phase times the loop holonomy `exp(∫₀¹ ell)`.  This justifies the
intended meaning `H_loop(t) = exp(∫ ell_t)` (up to the rotation gauge phase). -/
theorem loopHolonomyAmplitude_eq_exp_integral {d : ℕ}
    (mlau : ℕ) (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (t : ℝ) (ht_ne : evalLaurentCircle ad t ≠ 0)
    (hroots_min_t :
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (ell : ℝ → ℂ) (hell : IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t)) :
    loopHolonomyAmplitude θ coeffs ad t =
      Complex.exp (2 * π * Complex.I * (θ : ℂ) * (t : ℂ)) *
        Complex.exp (∫ x in (0:ℝ)..1, ell x) := by
  rw [loopHolonomyAmplitude_def,
    return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs h_ad_coeff t ht_ne
      hroots_min_t ell hell]

/-! ## Task C — the gauge identity for the canonical loop-holonomy amplitude -/

/-- **`gaugeReturnMultiplier_eq_loopHolonomyAmplitude`.**

Gauging the canonical loop-holonomy amplitude by the rotation phase recovers the
choice-free algebraic loop holonomy, *definitionally* (no hypotheses).  This is
the gauge identity that makes the canonical amplitude satisfy the holonomy
bridge. -/
theorem gaugeReturnMultiplier_eq_loopHolonomyAmplitude {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    gaugeReturnMultiplier (loopHolonomyAmplitude θ coeffs ad) θ t =
      algReturnHolonomy coeffs ad t :=
  gaugeReturnMultiplier_canonicalGaugeAmplitude θ coeffs ad t

/-- **`loopHolonomyAmplitude_eq_algReturnHolonomy` (Task D).**

The loop holonomy (the gauged value) of the canonical loop-holonomy amplitude
equals the choice-free algebraic loop holonomy. -/
theorem loopHolonomyAmplitude_eq_algReturnHolonomy {d : ℕ}
    (θ : ℝ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    gaugeReturnMultiplier (loopHolonomyAmplitude θ coeffs ad) θ t =
      algReturnHolonomy coeffs ad t :=
  gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t

/-- **`StandardPeriodicLogIntegralEqualsLoopHolonomy_canonical` (Task C).**

The previously-blocking loop-holonomy identity, **proved** for the canonical
loop-holonomy amplitude.  Given the root data, the canonical amplitude satisfies
the gauge = `exp(∫₀¹ ell)` identity at every active fibre and every periodic
logarithm: the left side is `algReturnHolonomy` (definitionally, via the gauge
identity) and the right side equals `algReturnHolonomy` via
`return_multiplier_holonomy_eq_integral_log`. -/
theorem StandardPeriodicLogIntegralEqualsLoopHolonomy_canonical {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) W where
  hLoop := by
    intro t ht ht_ne _hW0 ell hell
    rw [gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t]
    exact (return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs
      rootData.h_ad_coeff t ht_ne (rootData.hroots_min t ht ht_ne) ell hell).symm

/-- Alias of `StandardPeriodicLogIntegralEqualsLoopHolonomy_canonical`. -/
theorem StandardPeriodicLogIntegralEqualsLoopHolonomy_proved_for_canonical_H
    {θ a₀ b₀ : ℝ} {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) W :=
  StandardPeriodicLogIntegralEqualsLoopHolonomy_canonical rootData

/-! ## Task E — the holonomy interfaces, proved for the canonical loop amplitude -/

/-- **`StandardGaugeMultiplierEqualsAlgHolonomy_canonical`.**

The gauge = algebraic-holonomy interface, proved unconditionally for the
canonical loop-holonomy amplitude. -/
theorem StandardGaugeMultiplierEqualsAlgHolonomy_canonical {θ a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} :
    StandardGaugeMultiplierEqualsAlgHolonomy θ a₀ b₀ ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) where
  hJalg := fun t _ _ => gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t

/-- **`StandardActiveFibreHolonomyEqualsGaugeMultiplier_canonical`.**

(`StandardActiveFibreHolonomyEqualsGaugeMultiplier` is an abbreviation for
`StandardGaugeMultiplierEqualsAlgHolonomy`.) -/
theorem StandardActiveFibreHolonomyEqualsGaugeMultiplier_canonical {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} :
    StandardActiveFibreHolonomyEqualsGaugeMultiplier θ a₀ b₀ ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) :=
  StandardGaugeMultiplierEqualsAlgHolonomy_canonical

/-- **`StandardCanonicalAmplitudeCompatibility_canonical`.**

The canonical loop-holonomy amplitude is, by definition, equal to the canonical
algebraic amplitude `canonicalGaugeAmplitude`, so it satisfies the canonical
amplitude compatibility interface trivially (`rfl`). -/
theorem StandardCanonicalAmplitudeCompatibility_canonical {θ a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) where
  hHcanon_active := fun _ _ _ => rfl

/-- **`StandardZeroWindingPeriodicLogHolonomyBridge_canonical`.**

The zero-winding periodic-log holonomy bridge, proved unconditionally for the
canonical loop-holonomy amplitude (its field is exactly the gauge identity). -/
theorem StandardZeroWindingPeriodicLogHolonomyBridge_canonical {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {W : ℝ → ℤ} :
    StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) W where
  hAlg := fun t _ _ _ => gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t

/-- **`StandardWindingZeroHolonomyBridge_canonical`.**

The integral-form winding-zero holonomy bridge for the canonical loop amplitude,
from the root data and the (proved) zero-winding bridge. -/
theorem StandardWindingZeroHolonomyBridge_canonical {θ a₀ b₀ : ℝ} {dlau mlau : ℕ}
    {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) W :=
  StandardWindingZeroHolonomyBridge_proved rootData
    StandardZeroWindingPeriodicLogHolonomyBridge_canonical

/-! ## Task G — the acceptable canonical residual theorems (all proved) -/

/-- **`StandardCanonicalLoopHolonomyAmplitudeExists`.**

The canonical loop-holonomy amplitude exists as a concrete function. -/
theorem StandardCanonicalLoopHolonomyAmplitudeExists {dlau : ℕ}
    (θ : ℝ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ) :
    ∃ H : ℝ → ℂ, H = loopHolonomyAmplitude θ coeffs ad :=
  ⟨loopHolonomyAmplitude θ coeffs ad, rfl⟩

/-- **`StandardGaugeReturnMultiplierForCanonicalLoopAmplitude`.**

The gauge of the canonical loop amplitude is the algebraic loop holonomy. -/
theorem StandardGaugeReturnMultiplierForCanonicalLoopAmplitude {dlau : ℕ}
    (θ : ℝ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (ad : LaurentPolynomial ℂ)
    (t : ℝ) :
    gaugeReturnMultiplier (loopHolonomyAmplitude θ coeffs ad) θ t =
      algReturnHolonomy coeffs ad t :=
  gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t

/-- **`StandardLoopHolonomyAmplitudeEqualsAlgHolonomy`.**

The loop-holonomy identity for the canonical amplitude: the gauged value equals
`exp(∫₀¹ ell)` for any periodic logarithm of the return loop (given root data). -/
theorem StandardLoopHolonomyAmplitudeEqualsAlgHolonomy {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (t : ℝ) (ht : t ∈ Set.Ioo a₀ b₀) (ht_ne : evalLaurentCircle ad t ≠ 0)
    (ell : ℝ → ℂ) (hell : IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t)) :
    gaugeReturnMultiplier (loopHolonomyAmplitude θ coeffs ad) θ t =
      Complex.exp (∫ x in (0:ℝ)..1, ell x) := by
  rw [gaugeReturnMultiplier_eq_loopHolonomyAmplitude θ coeffs ad t]
  exact (return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs
    rootData.h_ad_coeff t ht_ne (rootData.hroots_min t ht ht_ne) ell hell).symm

/-- **`StandardCanonicalLoopAmplitudeSatisfiesCompatibility`.**

The canonical loop amplitude satisfies the canonical amplitude compatibility
interface. -/
theorem StandardCanonicalLoopAmplitudeSatisfiesCompatibility {θ a₀ b₀ : ℝ} {dlau : ℕ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs
      (loopHolonomyAmplitude θ coeffs ad) :=
  StandardCanonicalAmplitudeCompatibility_canonical

/-! ## Task C/E — reanchoring an arbitrary amplitude through the canonical compat -/

/-- **The canonical-amplitude compatibility supersedes the abstract loop bridge.**

If an *arbitrary* amplitude `H` agrees with the canonical loop-holonomy amplitude
on the active arc (i.e. satisfies `StandardCanonicalAmplitudeCompatibility`), then
it satisfies the abstract loop-holonomy bridge
`StandardPeriodicLogIntegralEqualsLoopHolonomy`.  This shows the abstract loop
bridge is reducible to the canonical compatibility, and the canonical amplitude is
its canonical witness. -/
theorem StandardPeriodicLogIntegralEqualsLoopHolonomy_of_compat {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (compat : StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H) :
    StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W where
  hLoop := by
    intro t ht ht_ne _hW0 ell hell
    have hgauge : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t :=
      compat.toGaugeMultiplierEqualsAlg.hJalg t ht ht_ne
    rw [hgauge]
    exact (return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs
      rootData.h_ad_coeff t ht_ne (rootData.hroots_min t ht ht_ne) ell hell).symm

/-- **The zero-winding bridge for an arbitrary amplitude from the canonical
compatibility.** -/
theorem StandardZeroWindingPeriodicLogHolonomyBridge_of_compat {θ a₀ b₀ : ℝ}
    {dlau : ℕ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (compat : StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H) :
    StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W where
  hAlg := fun t ht ht_ne _ => compat.toGaugeMultiplierEqualsAlg.hJalg t ht ht_ne

/-- **`critical_mixed_final_contradiction_holonomy_two_inputs_canonical` (Task E).**

The strongest downstream endpoint, **reanchored** onto the canonical
loop-holonomy amplitude.  The abstract-amplitude loop bridge
`StandardPeriodicLogIntegralEqualsLoopHolonomy` is eliminated and replaced by the
transparent canonical-amplitude compatibility
`StandardCanonicalAmplitudeCompatibility` (the statement that the analytic
amplitude `analytic.H` agrees with the canonical loop-holonomy amplitude on the
active arc).  Together with the two genuine pure-winding inputs

* `StandardMeasurableWindingObstructionForActiveFibres`,
* `StandardWindingHomotopyInvarianceZeroFreeLoops`,

and the three packaged interfaces, this yields the conditional contradiction.

The holonomy side now depends only on the canonical-amplitude compatibility plus
the two winding inputs — *not* on the abstract-amplitude loop bridge.  The
canonical loop-holonomy amplitude is the canonical witness of the compatibility
(`StandardCanonicalAmplitudeCompatibility_canonical`). -/
theorem critical_mixed_final_contradiction_holonomy_two_inputs_canonical
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {W : ℝ → ℤ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres D.θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (compat : StandardCanonicalAmplitudeCompatibility D.θ a₀ b₀ ad coeffs analytic.H) :
    False :=
  critical_mixed_final_contradiction_holonomy_residuals_reduced D dk rootData analytic
    mwo hom (StandardZeroWindingPeriodicLogHolonomyBridge_of_compat compat)

end CriticalMixedHRT
