import Mathlib
import RequestProject.Zak.ZakTargetSpace
import RequestProject.Zak.ConcreteZakAEModel
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.ReturnCocycleToNoFlatBand
import RequestProject.HRT.ZakToNormalizedCocycle

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (a.e. rewiring) — from the four-term HRT relation to the normalized
cocycle, through the **honest a.e.-level** Zak model `L2ZakModelAE`

This module rewires the Stage 6B bridge from the (too strong) *pointwise*
`L2ZakModel` interface to the honest a.e.-level `L2ZakModelAE` interface
introduced in `ZakTargetSpace.lean`.

In the a.e. model the Zak transform is a genuine **linear isometry**
`Z.Zak : V →ₗᵢ[ℂ] W` and the time-frequency covariance is expressed as equalities
of `L²` classes (`Z.lattice_cov`, `Z.rogue_cov`).  Applying `Z.Zak` to a
normalized four-term HRT relation therefore yields, *unconditionally and with no
`sorry`*, the **`L²`-class one-step Zak equation**
(`hrt_relation_to_one_step_zak_equation_AE`):
```
  c₀ • Zf + c₁ • charLattice(r₁,t₁)(Zf) + c₂ • charLattice(r₂,t₂)(Zf)
          + c₃ • charRogue(a, p/m)(Zf) = 0      (in W).
```

To drive the Stage 5 / Stage 6A no-flat-band machinery one needs the *pointwise*
fibre data `NormalizedReturnData` (a fibre function `F : ℝ → ℝ → ℂ` with the
one-step fibre equation holding for **every** `(x,s)`).  Passing from the
`L²`-class equation above to such pointwise fibre data is precisely the
**active-fibre extraction**: choose an `L²` representative, restrict to the
full-measure set of fibres on which the equation holds pointwise, and read off
`F`.  This step is isolated — NOT as an axiom — as the precisely-typed
proposition `StandardAEFiberExtractionTheorem` (`AEFiberExtraction`).

Given the extracted fibre data, the bridge
`zak_relation_feeds_normalized_no_flat_band_AE` feeds the Stage 6A
`NormalizedReturnData` into `normalized_return_cocycle_feeds_no_flat_band_synthesized`,
producing the no-flat-band contradiction **without referencing the old pointwise
`L2ZakModel`**.
-/

namespace CriticalMixedHRT

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The `L²`-class one-step Zak equation (a.e. model).**

Applying the a.e.-model Zak isometry `Z.Zak` to the normalized four-term HRT
relation yields the one-step Zak equation as an identity of `L²` classes in `W`.
Proved unconditionally from linearity of the isometry and the `L²`-class
covariance fields `Z.lattice_cov`, `Z.rogue_cov`. -/
theorem hrt_relation_to_one_step_zak_equation_AE
    (Z : L2ZakModelAE V W)
    (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ)
    (r₁ t₁ r₂ t₂ : ℤ)
    (f : V)
    (hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    c₀ • Z.Zak f + c₁ • Z.charLattice r₁ t₁ (Z.Zak f)
      + c₂ • Z.charLattice r₂ t₂ (Z.Zak f)
      + c₃ • Z.charRogue a ((p : ℝ) / (m : ℝ)) (Z.Zak f) = 0 := by
  have h := congrArg Z.Zak hrel
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_zero] at h
  rw [Z.lattice_cov r₁ t₁ f, Z.lattice_cov r₂ t₂ f, Z.rogue_cov a ((p : ℝ) / (m : ℝ)) f] at h
  exact h

/-- **The active-fibre extraction proposition (TASK E blocker, abstract form).**

For an a.e.-level Zak model `Z : L2ZakModelAE V W`, every normalized four-term
HRT relation produces *pointwise* fibre data: a fibre function `F : ℝ → ℝ → ℂ`
that is `1`-periodic in the frequency variable and satisfies the one-step Zak
fibre equation for **every** `(x,s)`.  This is the active-fibre extraction step
(choice of `L²` representative + restriction to the full-measure active fibre
set).  It is *not* an axiom; it is the precisely-typed remaining obligation. -/
def AEFiberExtraction (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] : Prop :=
  ∀ (Z : L2ZakModelAE V W)
    (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (f : V)
    (_hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    ∃ F : ℝ → ℝ → ℂ,
      (∀ x s, F x (s + 1) = F x s) ∧
      (∀ x s, F (x - a) (s + (↑p / ↑m : ℝ)) =
        -c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑p / ↑m : ℂ)) * (↑x : ℂ))
          * Pfun c₀ c₁ c₂ r₁ t₁ r₂ t₂ x s * F x s)

/-- **TASK E — a.e. Stage 6B bridge (from extracted fibre data).**

Given the *extracted* pointwise fibre data (`F` with its frequency periodicity
and one-step fibre equation) — i.e. the conclusion of the active-fibre extraction
applied to a normalized four-term HRT relation in an a.e. Zak model — together
with the full Stage 5 / Stage 6A no-flat-band input data, we obtain the
no-flat-band contradiction.  This routes through the Stage 6A
`NormalizedReturnData` and `normalized_return_cocycle_feeds_no_flat_band_synthesized`,
with **no** reference to the pointwise `L2ZakModel`. -/
theorem zak_relation_feeds_normalized_no_flat_band_AE
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (hext : ∃ F : ℝ → ℝ → ℂ,
      (∀ x s, F x (s + 1) = F x s) ∧
      (∀ x s, F (x - a) (s + (↑p / ↑m : ℝ)) =
        -c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑p / ↑m : ℂ)) * (↑x : ℂ))
          * Pfun c₀ c₁ c₂ r₁ t₁ r₂ t₂ x s * F x s))
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
    False := by
  obtain ⟨F, hFper, hone⟩ := hext
  exact normalized_return_cocycle_feeds_no_flat_band_synthesized
    { m := m, hm := hm, p := p, a := a, θ := (m : ℝ) * a, hθ_eq := rfl, hθ_irr := hθ_irr,
      c₀ := c₀, c₁ := c₁, c₂ := c₂, c₃ := c₃, hc₀ := hc₀, hc₁ := hc₁, hc₂ := hc₂, hc₃ := hc₃,
      r₁ := r₁, t₁ := t₁, r₂ := r₂, t₂ := t₂, unimodular := unimodular,
      F := F, hFper := hFper, hone := hone }
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **TASK E — concrete `L²(ℝ)` a.e. Stage 6B bridge (from the blocker).**

Specialization of `zak_relation_feeds_normalized_no_flat_band_AE` to the concrete
`L²(ℝ)` a.e. Zak model: given the active-fibre extraction proposition
`AEFiberExtraction` for the concrete model, a model `Z`, a normalized four-term
relation, and the full no-flat-band data, the contradiction follows. -/
theorem zak_relation_feeds_normalized_no_flat_band_concrete_AE
    (hext : AEFiberExtraction (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget)
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
  zak_relation_feeds_normalized_no_flat_band_AE m hm p a hθ_irr c₀ c₁ c₂ c₃
    hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular
    (hext Z m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hrel)
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **The isolated active-fibre extraction obligation (TASK H blocker).**

The remaining a.e.-level Zak obligation, for the concrete model: the active-fibre
extraction proposition for `L²(ℝ)` valued in `L²([0,1]²)`.  Recorded as a
precisely-typed proposition; *not* an axiom. -/
def StandardAEFiberExtractionTheorem : Prop :=
  AEFiberExtraction (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget

/-- **TASK F — final contradiction without the pointwise Zak interface.**

The Stage 6B contradiction, driven entirely by the honest a.e.-level Zak model
`L2ZakModelAE` and the active-fibre extraction proposition
`StandardAEFiberExtractionTheorem`.  It does **not** reference the old (too
strong) pointwise `L2ZakModel`.  It still depends — exactly as the pointwise
bridge does — on the open `ROOT_DATA_INTERFACE`, the corrected periodic
Denjoy–Koksma interface, and canonical-amplitude compatibility (the `DK`, `hroots`
and `hJholo` hypotheses). -/
theorem critical_mixed_final_contradiction_without_pointwise_Zak_interface
    (hext : StandardAEFiberExtractionTheorem)
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
  zak_relation_feeds_normalized_no_flat_band_concrete_AE hext Z m hm p a hθ_irr
    c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne
    S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
