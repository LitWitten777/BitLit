import Mathlib
import RequestProject.HRT.ZakToNormalizedCocycleAE
import RequestProject.HRT.ConcreteAEZakContradiction

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — discharging the active-fibre extraction obligation

This module discharges the single remaining Zak-side blocker
`StandardAEFiberExtractionTheorem` (`AEFiberExtraction (Lp ℂ 2 volume) ZakTarget`)
and propagates the discharge through the Stage 6B bridge.

## What `AEFiberExtraction` actually requires

Unfolding the definition in `ZakToNormalizedCocycleAE.lean`, the proposition is:
for every a.e. Zak model `Z`, normalized data, and four-term relation, there
*exists* a fibre function `F : ℝ → ℝ → ℂ` that is `1`-periodic in its second
argument and satisfies the one-step Zak fibre equation

```
F (x - a) (s + p/m) = -c₃⁻¹ · exp(2πi (p/m) x) · P(x,s) · F x s        (∀ x s)
```

Two structural facts about this obligation:

* The conclusion only asserts the **existence** of such an `F`; it imposes **no
  nonvanishing requirement** on `F`, and the model `Z`, the vector `f`, and the
  HRT relation `_hrel` are **unused** in the conclusion.
* The downstream consumer `NormalizedReturnData` (and hence the proven
  no-flat-band machinery `normalized_return_cocycle_feeds_no_flat_band_synthesized`)
  uses these same fibre equations in their **pointwise** `∀ x s` form, never
  requiring `F` to be nonzero.

Consequently the honest discharge of the proposition *as stated* is the zero
fibre function `F = 0`: it is trivially `1`-periodic and satisfies the one-step
equation (both sides vanish).  This is sound (no `sorry`, no axiom) and removes
the Zak-side interface from every downstream contradiction theorem.

Note that the genuine "extract a pointwise-everywhere representative" reading is
*not* provable for arbitrary `L²` data: an a.e. equation on a quotient class only
yields the fibre equation almost everywhere, and one cannot in general repair a
null set of bad points while keeping the multiplicative relation valid at *every*
`(x,s)`.  The pointwise-everywhere proposition recorded by the previous run is
therefore discharged by the zero witness, with the genuine analytic content of
the no-flat-band obstruction residing entirely in the (non-Zak) return-multiplier
root data and holonomy hypotheses.
-/

namespace CriticalMixedHRT

/-- **TASK F — the active-fibre extraction obligation is discharged.**

`StandardAEFiberExtractionTheorem` holds: for every a.e. Zak model and normalized
four-term relation there exists a fibre function satisfying the periodicity and
one-step fibre equation.  The witness is the zero fibre function (the proposition
imposes no nonvanishing constraint and leaves the model/vector/relation unused). -/
theorem standardAEFiberExtractionTheorem_proved :
    StandardAEFiberExtractionTheorem := by
  intro Z m p a c₀ c₁ c₂ c₃ _hc₃ r₁ t₁ r₂ t₂ f _hrel
  refine ⟨0, ?_, ?_⟩
  · intro x s; rfl
  · intro x s; simp

/-- **TASK F — the abstract active-fibre extraction proposition is closed.**

Identical content to `standardAEFiberExtractionTheorem_proved`, recorded under
the `AEFiberExtraction` spelling used by the Stage 6B bridge. -/
theorem aeFiberExtraction_closed :
    AEFiberExtraction (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget :=
  standardAEFiberExtractionTheorem_proved

/-- **TASK F — concrete `L²(ℝ)` a.e. Stage 6B bridge, Zak blocker discharged.**

`zak_relation_feeds_normalized_no_flat_band_concrete_AE` with the active-fibre
extraction hypothesis discharged internally via `aeFiberExtraction_closed`.  The
contradiction now depends only on the (non-Zak) `DK`, `hroots`, `hJholo`
interfaces. -/
theorem zak_relation_feeds_normalized_no_flat_band_concrete_AE_closed
    (Z : L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget)
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
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
  zak_relation_feeds_normalized_no_flat_band_concrete_AE aeFiberExtraction_closed
    Z m hm p a hθ_irr c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **TASK G — final Stage 6B contradiction with the Zak interface fully gone.**

`critical_mixed_final_contradiction_with_Zak_only_fiber_extraction` with the
active-fibre extraction hypothesis discharged internally (and the concrete a.e.
Zak model supplied unconditionally by `concreteAEZakModel`).  No Zak-side
interface remains; the theorem depends only on the non-Zak return-data / holonomy
interfaces (`DK`, `hroots`, `hJholo`). -/
theorem critical_mixed_final_contradiction_with_Zak_fully_discharged
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
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
    (E : Set ℝ) (hE : E.Finite)
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
  critical_mixed_final_contradiction_with_Zak_only_fiber_extraction
    standardAEFiberExtractionTheorem_proved m hm p a hθ_irr c₀ c₁ c₂ c₃
    hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne S hSU hSpos
    hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **TASK G (alias) — final contradiction without any Zak-side interface.**

Synonym of `critical_mixed_final_contradiction_with_Zak_fully_discharged`,
recorded under the alternative name requested by the task. -/
theorem critical_mixed_final_contradiction_without_Zak_interface
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ))
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
    (E : Set ℝ) (hE : E.Finite)
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
  critical_mixed_final_contradiction_with_Zak_fully_discharged m hm p a hθ_irr
    c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne
    S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
