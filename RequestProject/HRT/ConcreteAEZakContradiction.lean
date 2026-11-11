import Mathlib
import RequestProject.Zak.ConcreteZakDenseDataFull
import RequestProject.Zak.CanonicalAEZakModel
import RequestProject.HRT.ZakToNormalizedCocycleAE

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the concrete a.e. Zak model is now unconditional (TASK G)

With `concrete_L2ZakModelAE_closed` (proved in `ConcreteZakDenseDataFull.lean`)
the honest a.e.-level Zak model `L2ZakModelAE (Lp ℂ 2 volume) ZakTarget` exists
*unconditionally* (no `StandardConcreteZakToLpTheorem` hypothesis, no `sorry`,
no axiom).  Consequently the Stage 6B final contradiction
(`critical_mixed_final_contradiction_without_pointwise_Zak_interface`) no longer
needs a Zak model supplied as a hypothesis: it can be instantiated at the
canonical model `concreteAEZakModel`.

The resulting theorem
`critical_mixed_final_contradiction_with_Zak_only_fiber_extraction` therefore
retains, on the Zak side, **only** the active-fibre extraction obligation
`StandardAEFiberExtractionTheorem` — exactly the single remaining Zak blocker.
-/

namespace CriticalMixedHRT

/-- The canonical concrete a.e.-level Zak model on `L²(ℝ)` valued in `L²([0,1]²)`.

This is the **canonical** model `canonicalAEZakModel`, whose target covariance
operators are the *explicitly defined* fibre operators `explicitCharLattice` /
`explicitCharRogue` (multiplication by the lattice character, resp. the rogue
fibre transport).  It replaces the previous opaque `Classical.choice` witness
`concrete_L2ZakModelAE_closed.some`, whose covariance operators were inaccessible.
With this canonical model the target-operator fibre formulas become provable. -/
noncomputable def concreteAEZakModel :
    L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget :=
  canonicalAEZakModel

/-- **TASK G — Stage 6B final contradiction, with the concrete a.e. Zak model
built in.**

This is `critical_mixed_final_contradiction_without_pointwise_Zak_interface`
instantiated at the canonical concrete model `concreteAEZakModel`.  It removes the
Zak-model hypothesis entirely (the model is now constructed unconditionally) and
retains, on the Zak side, only the active-fibre extraction obligation
`StandardAEFiberExtractionTheorem`.  The remaining hypotheses (`DK`, `hroots`,
`hJholo`, …) are the same non-Zak interfaces as before. -/
theorem critical_mixed_final_contradiction_with_Zak_only_fiber_extraction
    (hext : StandardAEFiberExtractionTheorem)
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
  critical_mixed_final_contradiction_without_pointwise_Zak_interface hext
    concreteAEZakModel m hm p a hθ_irr c₀ c₁ c₂ c₃ hc₀ hc₁ hc₂ hc₃
    r₁ t₁ r₂ t₂ unimodular f hrel DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge
    mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
