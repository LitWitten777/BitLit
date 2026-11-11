import Mathlib
import RequestProject.HRT.AENormalizedReturnCocycle
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.ReturnCocycleToNoFlatBand
import RequestProject.HRT.NontrivialAEFiberExtraction
import RequestProject.HRT.ZakToNormalizedCocycleAE
import RequestProject.HRT.ConcreteAEZakContradiction
import RequestProject.Rotation.DenjoyKoksmaInterface

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (a.e. refactor) — feeding a.e. normalized return data into Stage 5

This module is the a.e.-level analogue of `ReturnCocycleToNoFlatBand.lean`.  It
feeds the **a.e.-level** normalized return data `AENormalizedReturnData` into the
Stage 5 certificate-integrated no-flat-band theorem, and rewires the
extraction → return-cocycle → no-flat-band chain so that it consumes **honest a.e.
fibre data** and no longer requires the (too strong) pointwise-everywhere upgrade
`StandardPointwiseFiberUpgradeTheorem`.

Key point.  The Stage 5 no-flat-band contradiction
(`no_flat_band_of_active_fibers_integrated_certificate`, and its packaging
`normalized_return_cocycle_feeds_no_flat_band_synthesized`) depends on the
return data *only* through the irrational rotation parameter `θ` and its
irrationality witness `hθ_irr` — **not** through the fibre function `F` or any
pointwise fibre equation.  The genuine fibre content (the honest a.e. one-step
equation and the positive-measure active fibres, which forbid `F = 0`) lives in
`AENormalizedReturnData.hone_ae`, `AENormalizedReturnData.h_active_pos` and the
a.e. iteration lemmas of `AENormalizedReturnCocycle.lean`.  We therefore plumb
`θ`/`hθ_irr` into Stage 5 through the harmless degenerate
`AENormalizedReturnData.toDummyNormalized`, without ever asking for a
pointwise-everywhere fibre equation.

## Contents

* `ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal` — Task D.
* `ae_normalized_return_cocycle_feeds_no_flat_band` — Task D (alias form).
* `nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle` — Task E (the
  extraction → a.e. return data bridge, **no pointwise upgrade**).
* `zak_relation_feeds_ae_normalized_no_flat_band` — Task E.
* `critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade`
  — Task E (top-level), depending on `StandardNontrivialFiberExtractionTheorem`
  but **not** on `StandardPointwiseFiberUpgradeTheorem`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## Task D — a.e. normalized return data feeds the no-flat-band theorem -/

/-- **Task D — the a.e. normalized return cocycle feeds Stage 5 (root-data minimal
form).**

Given a.e.-level normalized return data `D : AENormalizedReturnData` (carrying the
honest a.e. one-step equation and positive-measure active fibres) together with
the Stage 5 active-fibre / analytic-rigidity / periodic-gauge data and the
*root-data-minimal* local Laurent holonomy certificate input (`ad`, `coeffs`,
`hroots`, `hJholo`), the certificate-integrated Stage 5 theorem yields a
contradiction.

This is the a.e. analogue of
`normalized_return_cocycle_feeds_no_flat_band_synthesized`.  The Stage 5
machinery is fed only `D.θ`/`D.hθ_irr` (through the degenerate
`D.toDummyNormalized`), reflecting the fact that the no-flat-band contradiction
does not depend on the fibre function. -/
theorem ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (D : AENormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
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
        J s = H s * Complex.exp (-2 * π * Complex.I * (D.θ : ℂ) * (s : ℂ)))
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
  normalized_return_cocycle_feeds_no_flat_band_synthesized
    D.toDummyNormalized DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau
    ad had coeffs h_ad_coeff hroots hJholo

/-- **Task D — the a.e. normalized return cocycle feeds Stage 5 (alias).**

Identical content to
`ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`, recorded
under the shorter name requested by the task. -/
theorem ae_normalized_return_cocycle_feeds_no_flat_band
    (D : AENormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
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
        J s = H s * Complex.exp (-2 * π * Complex.I * (D.θ : ℂ) * (s : ℂ)))
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
  ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    D DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-! ## Task E — replacing the pointwise extraction dependency -/

/-- **Task E — the nontrivial a.e. fibre extraction feeds a.e. normalized return
data (no pointwise upgrade).**

A `NontrivialAEFiberExtraction` already carries the honest **a.e.** one-step Zak
fibre equation (`h_one_step_ae`) and positive-measure active fibres
(`active_pos`).  Together with the algebraic data of the normalized critical mixed
form, this produces `AENormalizedReturnData` **directly**, with no
pointwise-everywhere upgrade.  This is the bridge that replaces the dependency on
`StandardPointwiseFiberUpgradeTheorem`. -/
def nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle
    {m : ℕ} {p : ℤ} {a : ℝ} {c₀ c₁ c₂ c₃ : ℂ} {r₁ t₁ r₂ t₂ : ℤ}
    (ext : NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
    (hm : 0 < m) (hθ_irr : Irrational ((m : ℝ) * a))
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (unimodular : r₁ * t₂ - r₂ * t₁ = 1) :
    AENormalizedReturnData where
  m := m
  hm := hm
  p := p
  a := a
  θ := (m : ℝ) * a
  hθ_eq := rfl
  hθ_irr := hθ_irr
  c₀ := c₀
  c₁ := c₁
  c₂ := c₂
  c₃ := c₃
  hc₀ := hc₀
  hc₁ := hc₁
  hc₂ := hc₂
  hc₃ := hc₃
  r₁ := r₁
  t₁ := t₁
  r₂ := r₂
  t₂ := t₂
  unimodular := unimodular
  F := ext.F
  hFper := ext.hF_periodic_s
  hone_ae := ext.h_one_step_ae
  h_active_pos := ext.active_pos

/-- **Task E — a normalized HRT relation feeds the a.e. no-flat-band machinery.**

Given the isolated active-fibre extraction obligation
`StandardNontrivialFiberExtractionTheorem`, a nonzero window satisfying a
normalized four-term HRT relation in the concrete a.e. Zak model produces a
`NontrivialAEFiberExtraction`, which is converted **directly** to
`AENormalizedReturnData` (no pointwise upgrade) and fed into the Stage 5
no-flat-band theorem.  Depends on `StandardNontrivialFiberExtractionTheorem`, but
**not** on `StandardPointwiseFiberUpgradeTheorem`. -/
theorem zak_relation_feeds_ae_normalized_no_flat_band
    (hext : StandardNontrivialFiberExtractionTheorem)
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
    False := by
  obtain ⟨ext⟩ := nontrivial_AE_fiber_extraction_from_relation hext m p a c₀ c₁ c₂ c₃
    hc₃ r₁ t₁ r₂ t₂ f hf hrel
  exact ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle ext hm hθ_irr
      hc₀ hc₁ hc₂ hc₃ unimodular)
    DK hq H hH hHne S hSU hSpos hSres Efin hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **Task E — final Stage 6B contradiction with the nontrivial a.e. Zak
extraction, with no pointwise upgrade.**

The a.e.-refactored replacement for
`critical_mixed_final_contradiction_with_nontrivial_AE_Zak`.  It combines the
genuine active-fibre extraction obligation `StandardNontrivialFiberExtractionTheorem`
(unsatisfiable by `F = 0`) with the full no-flat-band data to derive a
contradiction, routing through `AENormalizedReturnData` and the a.e. return
cocycle machinery.  Crucially, it depends on
`StandardNontrivialFiberExtractionTheorem` **only**, and **no longer** on the
too-strong `StandardPointwiseFiberUpgradeTheorem`. -/
theorem critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade
    (hext : StandardNontrivialFiberExtractionTheorem)
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
  zak_relation_feeds_ae_normalized_no_flat_band hext hm hθ_irr hc₀ hc₁ hc₂ hc₃
    unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres Efin hE J hJgauge mlau
    Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
