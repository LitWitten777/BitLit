import Mathlib
import RequestProject.Zak.ConcreteL2ZakModel
import RequestProject.HRT.ZakToNormalizedCocycle

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — concrete `L²(ℝ)` specialization of the Zak no-flat-band bridge

This module specializes the abstract Stage 6B bridge
`zak_relation_feeds_normalized_no_flat_band` (over an arbitrary inner-product
space `V`) to the concrete Hilbert space `L²(ℝ) = Lp ℂ 2 volume`.

The point of the specialization: every *algebraic / analytic* field of the Zak
interface (`Zak_periodic_s`, `lattice_cov`, `rogue_cov`, the Plancherel identity,
the fibre-density regularity and active-set positivity) has been discharged
concretely and unconditionally in the `RequestProject.Zak.*` modules
(`concreteZakDense_*`, `finiteSupportZak_plancherel`, `concreteZakDense_plancherel`,
`concrete_fiberDensity_integrable`, `concrete_active_set_positive_measure`).  The
*only* remaining Zak-side obligation is to produce the `L2ZakModel` term itself on
`L²(ℝ)`, i.e. `StandardL2ZakModelTheorem` (the standard Hilbert-space completion
of the densely-defined Zak transform).  The theorem below makes this precise:
given such a model `Z` for `L²(ℝ)` (equivalently, given
`StandardL2ZakModelTheorem`), the four-term HRT relation feeds the no-flat-band
contradiction.

It still depends on the *other* open interfaces (`ROOT_DATA_INTERFACE`, the
corrected periodic Denjoy–Koksma interface, canonical-amplitude compatibility),
exactly as the abstract bridge does.
-/

namespace CriticalMixedHRT

/-- **Concrete `L²(ℝ)` Stage 6B bridge.**

Specialization of `zak_relation_feeds_normalized_no_flat_band` to
`V = Lp ℂ 2 volume`.  Producing the model argument `Z` is exactly the content of
`StandardL2ZakModelTheorem`; all other Zak-interface content is already proved
concretely (see module docstring). -/
theorem zak_relation_feeds_normalized_no_flat_band_concrete
    (Z : L2ZakModel (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)))
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))
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
  zak_relation_feeds_normalized_no_flat_band Z m hm p a hθ_irr c₀ c₁ c₂ c₃
    hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne S hSU hSpos
    hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **Concrete `L²(ℝ)` final contradiction with the concrete Zak model.**

Same statement as `zak_relation_feeds_normalized_no_flat_band_concrete`, named to
record that, on the actual Hilbert space `L²(ℝ)`, the Stage 6B contradiction no
longer references the *abstract* `ZAK_MODEL_INTERFACE` over an arbitrary `V`: the
Zak-side input is pinned to a concrete `L²(ℝ)` model (whose existence is exactly
`StandardL2ZakModelTheorem`), while every covariance / Plancherel / active-set
fact it relies on is proved concretely.  It still depends on the open
`ROOT_DATA_INTERFACE`, the corrected periodic Denjoy–Koksma interface, and
canonical-amplitude compatibility, exactly as the abstract bridge does. -/
theorem critical_mixed_final_contradiction_with_concrete_zak_model
    (Z : L2ZakModel (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)))
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))
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
  zak_relation_feeds_normalized_no_flat_band_concrete Z m hm p a hθ_irr c₀ c₁ c₂ c₃
    hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne S hSU hSpos
    hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
