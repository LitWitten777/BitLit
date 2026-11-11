import Mathlib
import RequestProject.HRT.ConditionalFinalAssembly
import RequestProject.Rotation.PhaseLiftFromNonvanishing

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Winding-interface discharge run

This module performs the **winding-interface discharge run** for the conditional
final assembly theorem `critical_mixed_final_contradiction_with_interfaces`
(in `ConditionalFinalAssembly.lean`).  Its purpose is to remove or minimize the
`WINDING_INTERFACE` package `CriticalMixedWindingInterface`.

## Task A — inspection of `CriticalMixedWindingInterface`

The structure `CriticalMixedWindingInterface θ a₀ b₀ Mlau ad coeffs H` has the
following fields:

* `J : ℝ → ℂ` — the geometric gauge function.
* `hJgauge : ∀ s ∈ Set.Ioo a₀ b₀, J s = H s * exp(-2π i θ s)` — the relation of
  the gauge to the analytic amplitude `H`.
* `hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = exp(∫₀¹ ell_t)` — the choice-free holonomy identification of the
  gauge value with the loop holonomy `exp(∫₀¹ ell_t)` of any periodic logarithm
  of the bivariate Laurent return loop.

Field classification (recorded in `WINDING_INTERFACE_DISCHARGE_STATUS.md`):

* `J` — **derivable**: it is uniquely pinned by `hJgauge`; we supply it
  internally as `gaugeReturnMultiplier H θ`.
* `hJgauge` — **derivable**: definitional once `J = gaugeReturnMultiplier H θ`.
* `hJholo` — **must remain as an explicit hypothesis**.  This is the genuine
  analytic↔algebraic bridge: it asserts that the *analytic* gauge value
  `H t · exp(-2π i θ t)` coincides with the *algebraic* loop holonomy
  `exp(∫₀¹ ell_t)` (which, by the Jensen holonomy formula
  `complex_jensen_holonomy_product`, equals `ad(t)·∏_{|rᵢ|>1}(-rᵢ)`).  It cannot
  be derived from Stage 3B / Stage 4 / Run C alone, so it is the single
  irreducible field of the minimal winding interface.

## Task B — phase-lift / log adapter for the return loop

`return_multiplier_has_phase_lift_on_active_arc` turns a periodic logarithm of
the bivariate Laurent return loop into a genuine **phase lift** (Run C
`HasPhaseLift`), via `hasPhaseLift_of_continuous_log`.
`return_multiplier_winding_number_integral_eq_phase_degree` records that the
contour winding number of a `C¹` phase lift equals its phase degree, and
`return_multiplier_public_winding_adapter` re-exports the Run C measurable
winding obstruction in winding-number language.

## Task E — minimal winding interface (fallback policy)

`CriticalMixedMinimalWindingInterface` is the strictly smaller winding interface
carrying only the irreducible field `hJholo` (with the gauge supplied internally
as `gaugeReturnMultiplier H θ`).  The theorems
`normalized_critical_mixed_relation_contradiction_with_minimal_winding_interface`
and `critical_mixed_final_contradiction_with_minimal_winding_interface`
strengthen the conditional final assembly to depend only on the three other
interfaces (`ROOT_DATA_INTERFACE`, `ZAK_MODEL_INTERFACE`, `DK_VARIATION_INTERFACE`)
together with this minimal winding field.

No axioms, `sorry`s, or `admit`s are introduced.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task B — phase-lift / log adapter for the return loop -/

/-- **Phase lift of the bivariate Laurent return loop on the active arc.**

For any fibre `t`, a periodic logarithm `ell` of the bivariate Laurent return
loop `evalBiLaurentPoly coeffs M t` (a continuous, `1`-periodic, nonvanishing
loop in the circle variable) yields a genuine Run C phase lift: there is an
integer winding degree `deg` and a `1`-periodic real remainder `g` with
```
  (loop x) / ‖loop x‖ = exp(2π i (deg·x + g x)).
```
This is `hasPhaseLift_of_continuous_log` applied to the periodic logarithm. -/
theorem return_multiplier_has_phase_lift_on_active_arc
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (M : ℤ) (t : ℝ)
    (ell : ℝ → ℂ) (hell : IsPeriodicLog ell (evalBiLaurentPoly coeffs M t)) :
    ∃ (deg : ℤ) (g : ℝ → ℝ), HasPhaseLift (evalBiLaurentPoly coeffs M t) deg g := by
  have hbcont : Continuous (evalBiLaurentPoly coeffs M t) := by
    have hb : evalBiLaurentPoly coeffs M t = fun x => Complex.exp (ell x) :=
      funext (fun x => (hell.exp_eq x).symm)
    rw [hb]; exact Complex.continuous_exp.comp hell.cont
  have hbper : Function.Periodic (evalBiLaurentPoly coeffs M t) 1 := by
    intro x; rw [← hell.exp_eq (x + 1), ← hell.exp_eq x, hell.periodic x]
  exact hasPhaseLift_of_continuous_log (evalBiLaurentPoly coeffs M t)
    hbcont hbper
    (fun x => by rw [← hell.exp_eq x]; exact Complex.exp_ne_zero _)
    ell hell.cont hell.exp_eq

/-- **The contour winding number of a `C¹` phase lift equals its phase degree.**

Specialisation of the Run C identity `windingNumberIntegral_eq_of_phase_lift`
to the return-loop setting: if a loop `b` has a `C¹` phase lift of degree `deg`
with `1`-periodic remainder `g`, then its contour winding number equals `deg`. -/
theorem return_multiplier_winding_number_integral_eq_phase_degree
    (b : ℝ → ℂ) (deg : ℤ) (g g' : ℝ → ℝ)
    (hlift : ∀ x, b x =
        Complex.exp (2 * π * Complex.I * ((deg : ℂ) * (x : ℂ) + (g x : ℂ))))
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg'cont : Continuous g')
    (hper : g 1 = g 0) :
    windingNumberIntegral b = (deg : ℂ) :=
  windingNumberIntegral_eq_of_phase_lift b deg g g' hlift hg hg'cont hper

/-- **Public measurable winding obstruction for the return cocycle.**

Re-export of the Run C public obstruction `measurable_cocycle_winding_eq_zero_public`
under a return-multiplier name: for a measurable unit-modulus `1`-periodic return
cocycle `u` with phase-lift degree `d`, under the translation/oscillation
hypotheses `htrans`/`hosc` and the standard winding-number identification
`hwind : wind = d`, the winding number vanishes. -/
theorem return_multiplier_public_winding_adapter
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (u : ℝ → ℂ) (hu_meas : Measurable u) (hu1 : ∀ x, ‖u x‖ = 1)
    (d : ℤ) (g : ℝ → ℝ)
    (hstep : ∀ x, u (x - θ)
        = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))) * u x)
    (htrans : Tendsto
        (fun n => eLpNorm (fun x => u (x - (D.q n : ℝ) * θ) - u x) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0))
    (hosc : d ≠ 0 →
        Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1,
            Complex.exp (2 * π * Complex.I * windingPhase d g θ (D.q n) x))
          atTop (𝓝 0))
    (wind : ℤ) (hwind : wind = d) :
    wind = 0 :=
  measurable_cocycle_winding_eq_zero_public hθ D u hu_meas hu1 d g hstep htrans
    hosc wind hwind

/-! ## Task E — the minimal winding interface -/

/-- The geometric gauge of the return multiplier, supplied internally:
`gaugeReturnMultiplier H θ s = H s · exp(-2π i θ s)`.  This is exactly the gauge
pinned by the `hJgauge` field of `CriticalMixedWindingInterface`, so that field
becomes definitional. -/
noncomputable def gaugeReturnMultiplier (H : ℝ → ℂ) (θ : ℝ) (s : ℝ) : ℂ :=
  H s * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ))

/-- **Minimal `WINDING_INTERFACE`.**

The strictly smaller winding interface carrying only the irreducible holonomy
identification `hJholo`, with the gauge supplied internally as
`gaugeReturnMultiplier H θ`.  Compared with `CriticalMixedWindingInterface`, the
gauge function `J` and the gauge relation `hJgauge` fields are removed (they are
derivable). -/
structure CriticalMixedMinimalWindingInterface (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) where
  hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
      gaugeReturnMultiplier H θ t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)

/-- The minimal winding interface yields the full `CriticalMixedWindingInterface`,
with the gauge `J := gaugeReturnMultiplier H θ` and the (now definitional) gauge
relation `hJgauge`. -/
noncomputable def CriticalMixedMinimalWindingInterface.toFull
    {θ : ℝ} {a₀ b₀ : ℝ} {dlau : ℕ} {Mlau : ℤ} {ad : LaurentPolynomial ℂ}
    {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ} {H : ℝ → ℂ}
    (w : CriticalMixedMinimalWindingInterface θ a₀ b₀ Mlau ad coeffs H) :
    CriticalMixedWindingInterface θ a₀ b₀ Mlau ad coeffs H where
  J := gaugeReturnMultiplier H θ
  hJgauge := fun _ _ => rfl
  hJholo := w.hJholo

/-- **Conditional final contradiction from the minimal winding interface.**

Strengthening of `normalized_critical_mixed_relation_contradiction_with_interfaces`:
the full `CriticalMixedWindingInterface` is replaced by the strictly smaller
`CriticalMixedMinimalWindingInterface`, whose only field is the irreducible
holonomy identification `hJholo` (the gauge `J` and the relation `hJgauge` are
supplied internally).  The other three interface packages
(`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`, `ZAK_MODEL_INTERFACE`) are
unchanged. -/
theorem normalized_critical_mixed_relation_contradiction_with_minimal_winding_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (wind : CriticalMixedMinimalWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  normalized_critical_mixed_relation_contradiction_with_interfaces D dk rootData
    analytic wind.toFull

/-- **Conditional final assembly theorem with the minimal winding interface.**

The headline winding-discharge endpoint.  It restates
`critical_mixed_final_contradiction_with_interfaces` with the full
`WINDING_INTERFACE` replaced by the strictly smaller
`CriticalMixedMinimalWindingInterface`.  The conditional final contradiction now
depends only on:

* `DK_VARIATION_INTERFACE`  (`dk`),
* `ROOT_DATA_INTERFACE`     (`rootData`),
* `ZAK_MODEL_INTERFACE`     (`analytic`),

together with the single irreducible winding field `hJholo` (the analytic↔
algebraic holonomy identification), the gauge and gauge-relation having been
internally discharged. -/
theorem critical_mixed_final_contradiction_with_minimal_winding_interface
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (wind : CriticalMixedMinimalWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  normalized_critical_mixed_relation_contradiction_with_minimal_winding_interface
    D dk rootData analytic wind

end CriticalMixedHRT
