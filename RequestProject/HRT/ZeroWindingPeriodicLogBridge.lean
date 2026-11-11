import Mathlib
import RequestProject.HRT.HolonomyResidualClosure
import RequestProject.HRT.CanonicalAmplitudeHolonomyCompat

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 1000000

/-!
# Zero-winding periodic-log holonomy bridge run

This module performs the **zero-winding periodic-log holonomy bridge run**.  The
holonomy-residual-closure run reduced the holonomy-amplitude interface to exactly
three upstream blockers, the last of which is the *zero-winding periodic-log
holonomy bridge*

```
StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W
```

whose single field is the choice-free per-fibre identification

```
  ∀ t ∈ (a₀,b₀), evalLaurentCircle ad t ≠ 0 → W t = 0 →
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t.
```

This run **splits that bridge into its two genuine mathematical ingredients** and
proves that they (together with the already-available root data) imply the
bridge, thereby reducing it to the strictly smaller, more canonical blocker.

## Decomposition

The intended proof of the bridge is:

1. **Periodic-log existence** — from zero winding (here, from the explicit root
   factorisation supplied by the root data) the bivariate Laurent return loop
   `evalBiLaurentPoly coeffs Mlau t` admits a continuous `1`-periodic logarithm
   `ell`.  This is the blocker `StandardZeroWindingPeriodicLogExists`, and it is
   **fully proved** here (`StandardZeroWindingPeriodicLogExists_proved`) via the
   already-available `evalBiLaurentPoly_periodic_log_of_roots`.

2. **Loop-holonomy identity** — the analytic gauge value
   `gaugeReturnMultiplier H θ t` equals the loop holonomy `exp(∫₀¹ ell)` of any
   periodic logarithm of the return loop.  This is the blocker
   `StandardPeriodicLogIntegralEqualsLoopHolonomy`; it is the genuine
   analytic↔geometric content (the abstract amplitude `H` is *a priori*
   unrelated to `coeffs`), and is left as the single remaining holonomy input.

3. **Root-product holonomy** — the loop holonomy equals the choice-free algebraic
   holonomy: `exp(∫₀¹ ell) = algReturnHolonomy coeffs ad t`.  This is **already
   proved unconditionally** as `return_multiplier_holonomy_eq_integral_log`.

Chaining (1)–(3) gives `gauge = exp(∫ ell) = algReturnHolonomy`, i.e. the bridge.

## Outcome

* `StandardZeroWindingPeriodicLogHolonomyBridge_proved` — the bridge from the two
  ingredients plus root data.
* `zero_winding_periodic_log_holonomy_bridge` — the bridge reduced to the single
  genuinely-missing blocker `StandardPeriodicLogIntegralEqualsLoopHolonomy`
  (periodic-log existence is discharged internally).
* `StandardWindingZeroHolonomyBridge_fully_proved`,
  `StandardCanonicalAmplitudeCompatibility_with_two_holonomy_inputs`,
  `critical_mixed_final_contradiction_holonomy_two_inputs` — the downstream
  endpoints now consuming the two pure-winding blockers
  (`StandardMeasurableWindingObstructionForActiveFibres`,
  `StandardWindingHomotopyInvarianceZeroFreeLoops`) together with the single
  loop-holonomy input `StandardPeriodicLogIntegralEqualsLoopHolonomy`.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Ingredient 1 — periodic-log existence (fully proved) -/

/-- **`STANDARD_ZERO_WINDING_PERIODIC_LOG_EXISTS`.**

The first ingredient of the bridge: at every active, zero-winding fibre, the
bivariate Laurent return loop `evalBiLaurentPoly coeffs Mlau t` admits a
continuous `1`-periodic logarithm.  (The existence in fact follows from the root
factorisation regardless of the winding value, so the `W t = 0` hypothesis is
kept only to match the bridge interface.) -/
structure StandardZeroWindingPeriodicLogExists (a₀ b₀ : ℝ) {dlau : ℕ} (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (W : ℝ → ℤ) : Prop where
  hExists : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 → W t = 0 →
    ∃ ell : ℝ → ℂ, IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t)

/-- **`STANDARD_ZERO_WINDING_PERIODIC_LOG_EXISTS_PROVED`.**

The periodic-log existence blocker is fully discharged from the root data: the
canonical root factorisation `return_multiplier_local_root_factorization`
together with the off-circle / inside-count root bookkeeping feeds
`evalBiLaurentPoly_periodic_log_of_roots`. -/
theorem StandardZeroWindingPeriodicLogExists_proved {a₀ b₀ : ℝ} {dlau mlau : ℕ}
    {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs) :
    StandardZeroWindingPeriodicLogExists a₀ b₀ Mlau ad coeffs W where
  hExists := by
    intro t ht ht_ne _hW0
    obtain ⟨r, hfact, hrootmap⟩ :=
      return_multiplier_local_root_factorization coeffs ad rootData.h_ad_coeff t ht_ne
    have hrootmap' : (fibrePoly coeffs t).roots = Multiset.map r Finset.univ.val := hrootmap
    obtain ⟨hoff, hM, _hm⟩ := rootData.hroots_min t ht ht_ne
    have hr_off : ∀ i, ‖r i‖ ≠ 1 := root_offcircle_transfer r _ hrootmap' hoff
    have hMint : Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) := by
      rw [hM, root_count_transfer r _ hrootmap' (fun z => ‖z‖ < 1)]
    exact evalBiLaurentPoly_periodic_log_of_roots Mlau coeffs t (evalLaurentCircle ad t)
      ht_ne r hr_off hMint hfact

/-! ## Ingredient 2 — loop-holonomy identity (the single remaining blocker) -/

/-- **`STANDARD_PERIODIC_LOG_INTEGRAL_EQUALS_LOOP_HOLONOMY`.**

The second — and only genuinely missing — ingredient of the bridge: at every
active, zero-winding fibre, the analytic gauge value
`gaugeReturnMultiplier H θ t` equals the loop holonomy `exp(∫₀¹ ell)` of *any*
continuous `1`-periodic logarithm `ell` of the bivariate Laurent return loop.

This is the irreducible analytic↔geometric bridge: the abstract analytic
amplitude `H` is *a priori* unrelated to the algebraic return data `coeffs`/`ad`,
so this identity is the precise remaining input.  It is strictly more canonical
than the previous bridge field, since it is stated purely via the geometric loop
holonomy `exp(∫₀¹ ell)` with no reference to the algebraic root product. -/
structure StandardPeriodicLogIntegralEqualsLoopHolonomy (θ a₀ b₀ : ℝ) {dlau : ℕ}
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) (W : ℝ → ℤ) : Prop where
  hLoop : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 → W t = 0 →
    ∀ ell : ℝ → ℂ, IsPeriodicLog ell (evalBiLaurentPoly coeffs Mlau t) →
      gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0:ℝ)..1, ell x)

/-! ## Task C — the zero-winding periodic-log holonomy bridge -/

/-- **`STANDARD_ZERO_WINDING_PERIODIC_LOG_HOLONOMY_BRIDGE_PROVED` (Task C).**

The bridge `gauge = algReturnHolonomy` at active, zero-winding fibres, assembled
from the two ingredients plus the root data:

1. `existsLog` supplies a periodic logarithm `ell` of the return loop;
2. `loop` identifies `gaugeReturnMultiplier H θ t = exp(∫₀¹ ell)`;
3. `return_multiplier_holonomy_eq_integral_log` identifies
   `exp(∫₀¹ ell) = algReturnHolonomy coeffs ad t`. -/
theorem StandardZeroWindingPeriodicLogHolonomyBridge_proved {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (existsLog : StandardZeroWindingPeriodicLogExists a₀ b₀ Mlau ad coeffs W)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W where
  hAlg := by
    intro t ht ht_ne hW0
    obtain ⟨ell, hell⟩ := existsLog.hExists t ht ht_ne hW0
    have h1 := loop.hLoop t ht ht_ne hW0 ell hell
    have h2 := return_multiplier_holonomy_eq_integral_log mlau Mlau ad coeffs
      rootData.h_ad_coeff t ht_ne (rootData.hroots_min t ht ht_ne) ell hell
    rw [h1, h2]

/-- **`ZERO_WINDING_PERIODIC_LOG_HOLONOMY_BRIDGE` (Task C, reduced form).**

The bridge reduced to the *single* genuinely-missing blocker
`StandardPeriodicLogIntegralEqualsLoopHolonomy`: periodic-log existence is
discharged internally from the root data
(`StandardZeroWindingPeriodicLogExists_proved`), so only the loop-holonomy
identity remains. -/
theorem zero_winding_periodic_log_holonomy_bridge {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W :=
  StandardZeroWindingPeriodicLogHolonomyBridge_proved rootData
    (StandardZeroWindingPeriodicLogExists_proved rootData) loop

/-- Alias matching the `StandardZeroWindingPeriodicLogHolonomyBridge_proved`
project-naming convention but in the reduced (single-blocker) form. -/
theorem StandardZeroWindingPeriodicLogHolonomyBridge_proved_of_loop {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W :=
  zero_winding_periodic_log_holonomy_bridge rootData loop

/-! ## Task D — downstream closure consuming the two pure-winding blockers
       plus the single loop-holonomy input -/

/-- **`STANDARD_WINDING_ZERO_HOLONOMY_BRIDGE_FULLY_PROVED`.**

The winding-zero holonomy bridge (the integral-form residual) from the root data
and the single loop-holonomy blocker. -/
theorem StandardWindingZeroHolonomyBridge_fully_proved {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardWindingZeroHolonomyBridge θ a₀ b₀ Mlau ad coeffs H W :=
  StandardWindingZeroHolonomyBridge_proved rootData
    (zero_winding_periodic_log_holonomy_bridge rootData loop)

/-- **`STANDARD_ACTIVE_FIBRE_WINDING_ZERO_ON_ARC_WITH_TWO_HOLONOMY_INPUTS`.**

The winding-zero-on-arc residual built from the two pure-winding blockers
(`StandardMeasurableWindingObstructionForActiveFibres`,
`StandardWindingHomotopyInvarianceZeroFreeLoops`) together with the single
loop-holonomy input `StandardPeriodicLogIntegralEqualsLoopHolonomy` and the root
data. -/
theorem StandardActiveFibreWindingZeroOnArc_with_two_holonomy_inputs {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardActiveFibreWindingZeroOnArc θ a₀ b₀ Mlau ad coeffs H :=
  StandardActiveFibreWindingZeroOnArc_fully_proved rootData mwo hom
    (zero_winding_periodic_log_holonomy_bridge rootData loop)

/-- **`STANDARD_CANONICAL_AMPLITUDE_COMPATIBILITY_WITH_TWO_HOLONOMY_INPUTS`.**

The canonical amplitude compatibility from the two pure-winding blockers, the
single loop-holonomy input, and the root data. -/
theorem StandardCanonicalAmplitudeCompatibility_with_two_holonomy_inputs {θ a₀ b₀ : ℝ}
    {dlau mlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ} {W : ℝ → ℤ}
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy θ a₀ b₀ Mlau ad coeffs H W) :
    StandardCanonicalAmplitudeCompatibility θ a₀ b₀ ad coeffs H :=
  StandardCanonicalAmplitudeCompatibility_fully_proved rootData mwo hom
    (zero_winding_periodic_log_holonomy_bridge rootData loop)

/-- **`CRITICAL_MIXED_FINAL_CONTRADICTION_HOLONOMY_TWO_INPUTS`.**

The conditional final contradiction with the holonomy-amplitude interface reduced
to the two pure-winding blockers
(`StandardMeasurableWindingObstructionForActiveFibres`,
`StandardWindingHomotopyInvarianceZeroFreeLoops`) together with the single
loop-holonomy input `StandardPeriodicLogIntegralEqualsLoopHolonomy`, plus the
three packaged interfaces (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`,
`ZAK_MODEL_INTERFACE`).  The zero-winding periodic-log holonomy bridge is now
derived internally. -/
theorem critical_mixed_final_contradiction_holonomy_two_inputs
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    {W : ℝ → ℤ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (mwo : StandardMeasurableWindingObstructionForActiveFibres D.θ a₀ b₀ W)
    (hom : StandardWindingHomotopyInvarianceZeroFreeLoops a₀ b₀ W)
    (loop : StandardPeriodicLogIntegralEqualsLoopHolonomy D.θ a₀ b₀ Mlau ad coeffs
      analytic.H W) :
    False :=
  critical_mixed_final_contradiction_holonomy_residuals_reduced D dk rootData analytic
    mwo hom (zero_winding_periodic_log_holonomy_bridge rootData loop)

end CriticalMixedHRT
