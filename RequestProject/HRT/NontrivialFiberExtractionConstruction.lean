import Mathlib
import RequestProject.HRT.NontrivialAEFiberExtraction
import RequestProject.HRT.AEReturnCocycleToNoFlatBand

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — reducing the nontrivial a.e. fibre extraction to a pure
fibre-construction statement

The honest Zak-side blocker recorded by the previous run is
`StandardNontrivialFiberExtractionTheorem`
(`RequestProject/HRT/NontrivialAEFiberExtraction.lean`):

```
∀ (Z : L2ZakModelAE (Lp ℂ 2 volume) ZakTarget) (m p a c₀ c₁ c₂ c₃) (hc₃ : c₃ ≠ 0)
  (r₁ t₁ r₂ t₂) (f : Lp ℂ 2 volume) (hf : f ≠ 0)
  (hrel : c₀ • f + c₁ • Z.shift r₁ t₁ f + c₂ • Z.shift r₂ t₂ f
            + c₃ • Z.shift a (p/m) f = 0),
  Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
```

A crucial observation about the `NontrivialAEFiberExtraction` structure: its only
tie to the window `f` is

* `window := f`, `h_window_ne := hf`, and
* the Plancherel mass tie `∫₀¹ fiberDensity F s ds = ‖window‖²`.

The fibre function `F` is **not** required to be (a representative of) `Z.Zak f`;
it is only required to be `1`-periodic in `s`, have interval-integrable fibre
density, carry total fibre mass `‖f‖²`, and satisfy the **a.e.** one-step Zak
fibre equation `oneStepEquation … F x s`.  Consequently the abstract model `Z`,
its opaque covariance operators `charLattice`/`charRogue`, and the HRT relation
`hrel` play **no role** in populating the structure: the entire content reduces
to the existence of *some* fibre function `F : ℝ → ℝ → ℂ` with the four listed
properties and an adjustable positive total mass.

This module isolates exactly that residue as the pure functional-equation
proposition `StandardNontrivialFiberConstructionTheorem`, and proves the
reduction

```
StandardNontrivialFiberConstructionTheorem → StandardNontrivialFiberExtractionTheorem
```

(`standardNontrivialFiberExtractionTheorem_of_construction`).  The reduction is
honest plumbing: given a nonzero window `f`, apply the construction at the target
mass `M = ‖f‖² > 0` and assemble the structure with `window := f`.

It also rewires the final Stage 6B contradiction so that, on the Zak side, it
depends **only** on `StandardNontrivialFiberConstructionTheorem` — the abstract
a.e. Zak model, its covariance operators, and the HRT relation no longer appear
as a Zak-side interface
(`critical_mixed_final_contradiction_without_Zak_extraction_interface`).

The remaining Zak-side obligation is therefore the smallest possible exact
statement: construct a single fibre function solving the a.e. one-step Zak fibre
equation with prescribed positive total mass.  This is recorded — *not* as an
axiom — as `StandardNontrivialFiberConstructionTheorem`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-- **The pure fibre-construction obligation (minimal Zak-side interface).**

The residue of `StandardNontrivialFiberExtractionTheorem` after stripping away the
abstract Zak model `Z`, its covariance operators, and the HRT relation: for every
choice of the normalized critical-mixed parameters (with `c₃ ≠ 0`) and every
positive target mass `M`, there exists a fibre function `F : ℝ → ℝ → ℂ` that is

* `1`-periodic in the frequency variable `s`,
* has interval-integrable fibre density on `[0,1]`,
* carries total fibre mass `∫₀¹ fiberDensity F s ds = M`, and
* satisfies the one-step Zak fibre equation **almost everywhere** (a.e. `s`, then
  a.e. `x`).

This is a statement purely about the one-step functional equation on
`ℝ → ℝ → ℂ`; it mentions neither `L2ZakModelAE` nor `ZakTarget` nor any HRT
relation.  It is recorded as a precisely-typed proposition, *not* an axiom.

**DEPRECATED AS FINAL HRT EVIDENCE (actual Zak fibre extraction re-anchoring run).**
Because its fibre function `F` is **model-free** (unrelated to the actual `L²`
Zak transform of the window) and its mass `M` is arbitrary, this construction is
an *artificial fallback only*: it is **not valid evidence for HRT** unless
explicitly tied to the actual Zak transform, and it must **not** be used in final
certification.  The correct, re-anchored interface is
`StandardActualZakFiberExtractionTheorem` /
`StandardActualZakRepresentativeTheorem` in
`RequestProject/HRT/ActualZakFiberExtraction.lean`, whose fibre function is the
actual Zak transform `concreteZakDense g` of the actual window and whose mass tie
is the genuine Zak/Plancherel identity.  This definition is retained (not deleted)
only for documentation and backward compatibility. -/
def StandardNontrivialFiberConstructionTheorem : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (M : ℝ) (_hM : 0 < M),
    ∃ F : ℝ → ℝ → ℂ,
      (∀ x s, F x (s + 1) = F x s) ∧
      IntervalIntegrable (fiberDensity F) volume 0 1 ∧
      (∫ s in (0:ℝ)..1, fiberDensity F s) = M ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s)

/-- **The reduction: pure fibre construction discharges the nontrivial extraction
blocker.**

Given the pure functional-equation construction
`StandardNontrivialFiberConstructionTheorem`, the abstract Zak-side blocker
`StandardNontrivialFiberExtractionTheorem` follows.  For a nonzero window `f` we
apply the construction at the target mass `M = ‖f‖² > 0`; the resulting fibre
function `F` assembles, with `window := f`, into a genuine
`NontrivialAEFiberExtraction` (the Plancherel tie holds by the mass equation, so
the structure is **not** satisfiable by `F = 0`).  The abstract model `Z`, its
covariance operators, and the HRT relation `hrel` are not used. -/
theorem standardNontrivialFiberExtractionTheorem_of_construction
    (hc : StandardNontrivialFiberConstructionTheorem) :
    StandardNontrivialFiberExtractionTheorem := by
  intro Z m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf _hrel
  obtain ⟨F, hper, hint, hmass, hone⟩ :=
    hc m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ (‖f‖ ^ 2) (pow_pos (norm_pos_iff.mpr hf) 2)
  exact ⟨{ window := f
           h_window_ne := hf
           F := F
           hF_periodic_s := hper
           h_density_integrable := hint
           h_plancherel := hmass
           h_one_step_ae := hone }⟩

/-- **Task E — the nontrivial fibre extraction, closed by the pure construction.**

`StandardNontrivialFiberExtractionTheorem`, proved from the minimal residual
obligation `StandardNontrivialFiberConstructionTheorem`.  This is the strongest
no-`sorry` form of the Zak-side extraction blocker produced in this run: the
abstract Zak interface is eliminated and only the pure fibre-construction
statement remains. -/
theorem nontrivial_fiber_extraction_closed
    (hc : StandardNontrivialFiberConstructionTheorem) :
    StandardNontrivialFiberExtractionTheorem :=
  standardNontrivialFiberExtractionTheorem_of_construction hc

/-- **Task E — final Stage 6B contradiction, depending only on the pure fibre
construction on the Zak side.**

The a.e.-refactored Stage 6B contradiction
(`critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade`)
with its Zak-side hypothesis `StandardNontrivialFiberExtractionTheorem` replaced
by the strictly smaller pure functional-equation construction
`StandardNontrivialFiberConstructionTheorem`.  The abstract a.e. Zak model, its
covariance operators, and the HRT relation are no longer a Zak-side *interface*:
they are used internally only through the canonical `concreteAEZakModel` and the
supplied relation `hrel`, while the *open obligation* on the Zak side is now
purely the existence of a fibre solution of the a.e. one-step Zak fibre equation
with prescribed positive total mass.

It still depends — exactly as the previous a.e. bridge does — on the non-Zak
interfaces: the corrected periodic Denjoy–Koksma data (`DK`, `hq`), the
analytic-rigidity / periodic-gauge data (`H`, `J`, …), and the local Laurent
holonomy root data (`ad`, `coeffs`, `hroots`, `hJholo`). -/
theorem critical_mixed_final_contradiction_without_Zak_extraction_interface
    (hc : StandardNontrivialFiberConstructionTheorem)
    {m : ℕ} (hm : 0 < m) {p : ℤ} {a : ℝ}
    (hθ_irr : Irrational ((m : ℝ) * a))
    {c₀ c₁ c₂ c₃ : ℂ}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    {r₁ t₁ r₂ t₂ : ℤ} (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0)
    (DK : DenjoyKoksmaReturnData ((m : ℝ) * a))
    (hq : Tendsto DK.q atTop atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (Efin : Set ℝ) (hE : Efin.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (((m : ℝ) * a : ℝ) : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False :=
  critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade
    (standardNontrivialFiberExtractionTheorem_of_construction hc)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
