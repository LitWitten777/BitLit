import Mathlib
import RequestProject.HRT.QuasiperiodicZakSideDischarge
import RequestProject.Zak.CanonicalAEZakModel

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the target-operator fibre formulas, **proved** for the canonical model

Now that `concreteAEZakModel` is the *canonical* a.e.-level Zak model
`canonicalAEZakModel` (whose covariance operators are the explicitly defined
`explicitCharLattice` / `explicitCharRogue`), the two previously-isolated
target-operator fibre formula blockers

```
StandardTargetLatticeOperatorRepresentativeAE
StandardTargetRogueOperatorRepresentativeAE
```

are **provable**, because the explicit operators expose their fibre action by
construction (`explicitCharLattice_coeFn`, `explicitCharRogue_coeFn`).  This file
proves them and feeds them into the quasiperiodic Zak-side discharge machinery
(`QuasiperiodicZakSideDischarge.lean`), so the entire Zak side is discharged
**unconditionally** (no remaining Zak-side hypotheses).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## The two target-operator fibre formulas, proved -/

/-- **Lattice operator fibre formula — proved for the canonical model.**

Since `concreteAEZakModel.charLattice r t = explicitCharLattice r t`
(multiplication by the lattice character `exp(-2π i (t x + r s))`), the lattice
operator formula holds by `explicitCharLattice_coeFn`. -/
theorem StandardTargetLatticeOperatorFormulaQuasiAE_proved :
    StandardTargetLatticeOperatorRepresentativeAE := by
  intro r t G
  have h := explicitCharLattice_coeFn r t G
  filter_upwards [h] with p hp
  simpa [latChar] using hp

/-- **Rogue operator fibre formula — proved for the canonical model.**

Since `concreteAEZakModel.charRogue a b = explicitCharRogue a b` and
`canonicalQuasiRep = zakQuasiPeriodicRep` (identical formula), the rogue operator
formula holds by `explicitCharRogue_coeFn`. -/
theorem StandardTargetRogueOperatorFormulaQuasiAE_proved :
    StandardTargetRogueOperatorRepresentativeAE := by
  intro a b G
  have h := explicitCharRogue_coeFn a b G
  filter_upwards [h] with p hp
  simpa [canonicalQuasiRep, zakQuasiPeriodicRep] using hp

/-! ## Explicit a.e. fibre actions on the quasiperiodic representative -/

/-- **Explicit a.e. lattice-operator fibre action on the quasiperiodic
representative — proved.** -/
theorem explicitCharLattice_apply_quasiRep_ae (r t : ℤ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charLattice r t G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I *
            ((t : ℂ) * (p.1 : ℂ) + (r : ℂ) * (p.2 : ℂ)))
          * zakQuasiPeriodicRep G p.1 p.2) :=
  charLattice_apply_quasiRep_ae_closed StandardTargetLatticeOperatorFormulaQuasiAE_proved r t G

/-- **Explicit a.e. rogue-operator fibre action on the quasiperiodic
representative — proved.** -/
theorem explicitCharRogue_apply_quasiRep_ae (a b : ℝ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charRogue a b G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * zakQuasiPeriodicRep G (p.1 - a) (p.2 + b)) :=
  charRogue_apply_quasiRep_ae_closed StandardTargetRogueOperatorFormulaQuasiAE_proved a b G

/-! ## The Zak side, discharged unconditionally -/

/-- **Target `Lp` one-step relation for the canonical model.** -/
theorem target_Lp_one_step_Zak_relation_canonical
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    c₀ • concreteAEZakModel.Zak f
      + c₁ • concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)
      + c₂ • concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)
      + c₃ • concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ))
          (concreteAEZakModel.Zak f) = 0 :=
  target_Lp_one_step_Zak_relation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ f hrel

/-- **The corrected quasiperiodic blocker is discharged unconditionally** for the
canonical model. -/
theorem StandardActualZakQuasiRepresentativeEquationAE_canonical :
    StandardActualZakQuasiRepresentativeEquationAE :=
  StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas
    StandardTargetLatticeOperatorFormulaQuasiAE_proved
    StandardTargetRogueOperatorFormulaQuasiAE_proved

/-- Alias: the corrected quasiperiodic blocker, proved unconditionally. -/
theorem standardActualZakQuasiRepresentativeEquationAE_proved :
    StandardActualZakQuasiRepresentativeEquationAE :=
  StandardActualZakQuasiRepresentativeEquationAE_canonical

/-- **Final Stage 6B contradiction via the canonical model — Zak side fully
discharged (no Zak-side hypotheses).** -/
theorem critical_mixed_final_contradiction_with_actual_L2_Zak_quasi_canonical
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
  critical_mixed_final_contradiction_with_actual_L2_Zak_quasi
    StandardActualZakQuasiRepresentativeEquationAE_canonical
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **Final Stage 6B contradiction with the Zak-side interface fully removed
(corrected).**  This instantiates
`critical_mixed_final_contradiction_without_Zak_side_interface_corrected` with the
two now-proved target-operator fibre formulas, so it carries **no** Zak-side
hypotheses. -/
theorem critical_mixed_final_contradiction_without_Zak_side_interface_corrected_proved
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
  critical_mixed_final_contradiction_without_Zak_side_interface_corrected
    StandardTargetLatticeOperatorFormulaQuasiAE_proved
    StandardTargetRogueOperatorFormulaQuasiAE_proved
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
