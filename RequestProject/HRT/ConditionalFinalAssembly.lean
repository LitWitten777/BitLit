import Mathlib
import RequestProject.HRT.RootDataAdapter
import RequestProject.HRT.ZakToNormalizedCocycle

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Conditional final assembly of the critical mixed-arithmetic four-point HRT theorem

This module performs the **conditional final assembly run**: it composes the
strongest available bridge theorems of the project into a single conditional
contradiction theorem, parameterised exactly by the four remaining explicit
interface classes recorded in `FINAL_INTERFACE_AUDIT.md`:

```
  ROOT_DATA_INTERFACE     : hroots_min
  ZAK_MODEL_INTERFACE     : the L2ZakModel `Z` and the active/analytic data
  DK_VARIATION_INTERFACE  : the Denjoy–Koksma return data (deep DK estimate)
  WINDING_INTERFACE       : the holonomy / phase-lift data `hJgauge`, `hJholo`
```

It does **not** touch `critical_mixed_orbit_HRT_L2` (whose proof remains the only
theorem-body `sorry` in the project) and introduces no axioms, `sorry`s, or
`admit`s.

## What is established here

* `zak_relation_feeds_normalized_no_flat_band_root_data_minimal` — the adapter
  that upgrades the Stage 6B endpoint
  `zak_relation_feeds_normalized_no_flat_band` (which fed the *older* Stage 6A
  bridge `normalized_return_cocycle_feeds_no_flat_band_synthesized`, consuming
  the full root-factorisation data `hroots`) to the Run A **root-data-minimal**
  Stage 6A bridge `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`
  (consuming only the minimal geometric interface `hroots_min`).  This combines
  the Stage 6B Zak relation-to-cocycle construction
  (`hrt_relation_to_one_step_zak_equation`) with the Run A root-data-minimal
  bridge.

* `NormalizedCriticalMixedRelationData` — a clean structure bundling a
  normalized nontrivial four-term HRT relation in an `L²` Zak model.  Per Task D,
  we do **not** attempt the affine-symplectic normal form from arbitrary
  `u, v, ν` to the normalized relation; the conditional contradiction is proved
  from this normalized data.

* Interface structures
  `CriticalMixedDKInterface`, `CriticalMixedRootDataInterface`,
  `CriticalMixedActiveAnalyticInterface`, `CriticalMixedWindingInterface`
  packaging the four remaining interface classes as **explicit assumptions**
  (no axioms, no global constants).

* `normalized_critical_mixed_relation_contradiction_with_interfaces` and
  `critical_mixed_final_contradiction_with_interfaces` — the conditional final
  assembly theorems: from the normalized relation data together with the four
  interface packages, derive `False`.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task A — the root-data-minimal Stage 6B endpoint -/

/-- **Stage 6B endpoint driven by the minimal root-data interface.**

This is the root-data-minimal upgrade of `zak_relation_feeds_normalized_no_flat_band`.
The earlier endpoint fed the *older* Stage 6A bridge
`normalized_return_cocycle_feeds_no_flat_band_synthesized`, which consumed the
full root-factorisation existential `hroots`.  Here we instead build the Stage 6A
`NormalizedReturnData` from the relation (via
`hrt_relation_to_one_step_zak_equation`) and feed it into the Run A
root-data-minimal bridge
`normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`, so the only
root datum required is the minimal geometric interface `hroots_min` (the
factorisation identity and root enumeration are synthesised internally via the
fundamental theorem of algebra). -/
theorem zak_relation_feeds_normalized_no_flat_band_root_data_minimal
    (Z : L2ZakModel V)
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : V)
    (hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0)
    (DK : DenjoyKoksmaReturnData ((m : ℝ) * a))
    (hq : Tendsto DK.q atTop atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (E : Set ℝ) (hE : E.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (((m : ℝ) * a : ℝ) : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots_min : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau)
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False :=
  normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (hrt_relation_to_one_step_zak_equation Z m hm p a hθ_irr c₀ c₁ c₂ c₃
      hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel)
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots_min hJholo

/-! ## Task D — the normalized relation data -/

/-- **Normalized critical mixed four-term relation data.**

A clean bundle of a normalized nontrivial four-term HRT relation in an `L²` Zak
model `Z`:

```
  c₀ f + c₁ π(r₁,t₁) f + c₂ π(r₂,t₂) f + c₃ π(a, p/m) f = 0
```

with `m > 0`, `θ = m·a` irrational, the four coefficients nonzero, and
`(r₁,t₁),(r₂,t₂)` a unimodular ℤ²-basis.

Per Task D, the affine-symplectic normal form taking an *arbitrary* mixed orbit
`(u, v, ν)` to this normalized shape is **not** formalised here; the conditional
contradiction is proved starting from this normalized data. -/
structure NormalizedCriticalMixedRelationData (Z : L2ZakModel V) where
  m : ℕ
  hm : 0 < m
  p : ℤ
  a : ℝ
  hθ_irr : Irrational ((m : ℝ) * a)
  c₀ : ℂ
  c₁ : ℂ
  c₂ : ℂ
  c₃ : ℂ
  hc₀ : c₀ ≠ 0
  hc₁ : c₁ ≠ 0
  hc₂ : c₂ ≠ 0
  hc₃ : c₃ ≠ 0
  r₁ : ℤ
  t₁ : ℤ
  r₂ : ℤ
  t₂ : ℤ
  unimodular : r₁ * t₂ - r₂ * t₁ = 1
  f : V
  hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
            + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
            + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0

namespace NormalizedCriticalMixedRelationData

variable {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)

/-- The irrational rotation number `θ = m·a` of the normalized data. -/
def θ : ℝ := (D.m : ℝ) * D.a

/-- The Stage 6A `NormalizedReturnData` built from the normalized relation via
the one-step Zak fibre equation. -/
noncomputable def toReturnData : NormalizedReturnData :=
  hrt_relation_to_one_step_zak_equation Z D.m D.hm D.p D.a D.hθ_irr
    D.c₀ D.c₁ D.c₂ D.c₃ D.hc₀ D.hc₁ D.hc₂ D.hc₃
    D.r₁ D.t₁ D.r₂ D.t₂ D.unimodular D.f D.hrel

end NormalizedCriticalMixedRelationData

/-! ## Task B — the four remaining interface packages -/

/-- **DK_VARIATION_INTERFACE.** The Denjoy–Koksma return data for the rotation
by `θ` together with the divergence `qₙ → ∞` of the return times.  The deep
continued-fraction Denjoy–Koksma estimate is the `dk_bound` field of
`DenjoyKoksmaReturnData`. -/
structure CriticalMixedDKInterface (θ : ℝ) where
  returnData : DenjoyKoksmaReturnData θ
  hq : Tendsto returnData.q atTop atTop

/-- **ROOT_DATA_INTERFACE.** The minimal geometric root data `hroots_min` on the
active window `(a₀, b₀)`: for each fibre with nonzero leading coefficient, the
roots of the canonical fibre polynomial `fibrePoly coeffs t` avoid the unit
circle and have inside / outside counts `Mlau` / `mlau`. -/
structure CriticalMixedRootDataInterface (a₀ b₀ : ℝ) {dlau : ℕ} (mlau : ℕ)
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) where
  had : ad ≠ 0
  h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad
  hroots_min : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
    Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
    ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau

/-- **ZAK_MODEL_INTERFACE (active/analytic side).** The active-fibre and
analytic-rigidity data over the window `(a₀, b₀)`: an analytic, nonvanishing
holonomy amplitude `H`, a positive-measure active set `S` whose `H`-values lie in
the resonance group of the return times, and the finite exceptional set `E`.

(The concrete `L2ZakModel Z` itself — the other half of the Zak model interface —
is supplied as an explicit argument to the assembly theorems, alongside the
fibre-density Fubini regularity that is folded into the model's identities.) -/
structure CriticalMixedActiveAnalyticInterface (θ : ℝ)
    (DK : DenjoyKoksmaReturnData θ) (a₀ b₀ : ℝ) where
  H : ℝ → ℂ
  hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀)
  hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0
  S : Set ℝ
  hSU : S ⊆ Set.Ioo a₀ b₀
  hSpos : 0 < MeasureTheory.volume S
  hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q
  E : Set ℝ
  hE : E.Finite

/-- **WINDING_INTERFACE.** The holonomy / phase-lift data: the geometric gauge
`J`, its relation to the amplitude `H` (`hJgauge`), and the choice-free holonomy
identification `hJholo` of `J t` with the loop value `exp(∫₀¹ ell_t)` for any
periodic logarithm of the bivariate return loop. -/
structure CriticalMixedWindingInterface (θ : ℝ) (a₀ b₀ : ℝ) {dlau : ℕ}
    (Mlau : ℤ) (ad : LaurentPolynomial ℂ)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ) (H : ℝ → ℂ) where
  J : ℝ → ℂ
  hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
    J s = H s * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ))
  hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)

/-! ## Task C — the conditional contradiction theorem -/

/-- **Conditional final contradiction from normalized relation data.**

Starting from a normalized nontrivial four-term HRT relation
(`NormalizedCriticalMixedRelationData`) in an `L²` Zak model `Z`, together with
the four remaining explicit interface packages

* `dk`       — the Denjoy–Koksma return data (`DK_VARIATION_INTERFACE`),
* `rootData` — the minimal root data `hroots_min` (`ROOT_DATA_INTERFACE`),
* `analytic` — the active-fibre / analytic-rigidity data (`ZAK_MODEL_INTERFACE`),
* `wind`     — the holonomy / phase-lift data (`WINDING_INTERFACE`),

the full bridge chain
```
  normalized relation
  -> Zak/polyphase fibre equation       (hrt_relation_to_one_step_zak_equation)
  -> NormalizedReturnData
  -> m-step return cocycle / Laurent return multiplier
  -> finite exceptional set / active arc
  -> root-data-minimal no-flat-band bridge
  -> local Laurent certificate
  -> irrational-character obstruction
  -> False
```
yields a contradiction.  This is the strongest conditional assembly statement of
the project; only the four interface packages above remain to be discharged. -/
theorem normalized_critical_mixed_relation_contradiction_with_interfaces
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (wind : CriticalMixedWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  zak_relation_feeds_normalized_no_flat_band_root_data_minimal
    Z D.m D.hm D.p D.a D.hθ_irr D.c₀ D.c₁ D.c₂ D.c₃ D.hc₀ D.hc₁ D.hc₂ D.hc₃
    D.r₁ D.t₁ D.r₂ D.t₂ D.unimodular D.f D.hrel
    dk.returnData dk.hq
    analytic.H analytic.hH analytic.hHne analytic.S analytic.hSU analytic.hSpos
    analytic.hSres analytic.E analytic.hE
    wind.J wind.hJgauge mlau Mlau ad rootData.had coeffs rootData.h_ad_coeff
    rootData.hroots_min wind.hJholo

/-- **Conditional final assembly theorem.**

This is the headline conditional endpoint of the run.  It restates
`normalized_critical_mixed_relation_contradiction_with_interfaces`: from a
normalized critical mixed four-term relation and the four remaining explicit
interface packages (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`,
`ZAK_MODEL_INTERFACE`, `WINDING_INTERFACE`), the project derives `False`.

What remains toward the unconditional `critical_mixed_orbit_HRT_L2` is no longer
wiring: it is exactly the discharge of these four interfaces (plus the
arbitrary-to-normalized affine-symplectic normal form, deliberately not attempted
here per Task D). -/
theorem critical_mixed_final_contradiction_with_interfaces
    {Z : L2ZakModel V} (D : NormalizedCriticalMixedRelationData Z)
    {a₀ b₀ : ℝ} {dlau : ℕ} {mlau : ℕ} {Mlau : ℤ}
    {ad : LaurentPolynomial ℂ} {coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ}
    (dk : CriticalMixedDKInterface D.θ)
    (rootData : CriticalMixedRootDataInterface a₀ b₀ mlau Mlau ad coeffs)
    (analytic : CriticalMixedActiveAnalyticInterface D.θ dk.returnData a₀ b₀)
    (wind : CriticalMixedWindingInterface D.θ a₀ b₀ Mlau ad coeffs analytic.H) :
    False :=
  normalized_critical_mixed_relation_contradiction_with_interfaces D dk rootData
    analytic wind

end CriticalMixedHRT
