import Mathlib
import RequestProject.HRT.ActualZakRepresentative
import RequestProject.HRT.NontrivialAEFiberExtraction
import RequestProject.HRT.AEReturnCocycleToNoFlatBand
import RequestProject.Zak.ConcreteZakToLp

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — re-anchoring the nontrivial fibre extraction to the *actual* Zak transform

The previous run reduced the Zak-side blocker to the model-free proposition
`StandardNontrivialFiberConstructionTheorem`
(`RequestProject/HRT/NontrivialFiberExtractionConstruction.lean`): construct *some*
fibre function `F : ℝ → ℝ → ℂ` solving the a.e. one-step Zak fibre equation with a
prescribed positive total mass, **without** using the actual `L²` Zak transform,
the actual window, or the four-term HRT relation.  That reduction is **valid but
artificial**: the assembled `NontrivialAEFiberExtraction` carries `window := f`
but its fibre function `F` is unrelated to `Z.Zak f`, so it is not genuine HRT
evidence and may be unprovable (or false) in exactly the regimes where the
no-flat-band contradiction must apply.

This module re-anchors the fibre data to the **actual concrete Zak transform**
`concreteZakDense g` of an actual (bounded, measurable, compactly supported)
window `g` representing the `L²` class `f`.  The fibre function is *no longer*
model-free: it is the genuine Zak transform of the window, and the Plancherel
mass tie `∫₀¹ fiberDensity (concreteZakDense g) = ‖f‖²` is the actual Zak/Plancherel
identity (`actual_zak_total_fiber_mass_eq_norm_sq`), not a postulated mass.

## What is proved unconditionally here

* `StandardActualZakFiberExtractionTheorem` — the **actual-Zak** extraction
  interface (Task B): from a nonzero `L²` class `f`, a concrete representative
  window `g` (`f =ᵐ g`, bounded, measurable, supported in `[0,N)`), and the a.e.
  one-step Zak fibre equation *for the actual transform* `concreteZakDense g`,
  produce a `NontrivialAEFiberExtraction` whose fibre function is `concreteZakDense g`.
  This is **proved** (`actual_zak_nontrivial_fiber_extraction`): all four
  structure fields come from the actual Zak endpoints
  (`actual_zak_representative_periodic_s`,
  `actual_zak_representative_fiberDensity_integrable`,
  `actual_zak_total_fiber_mass_eq_norm_sq`) plus the supplied a.e. one-step
  equation.  The fibre function is never model-free and never `0`.

* The adapters of Task C, all **proved**:
  `actual_zak_representative_represents_Lp_Zak` (the actual Zak/Plancherel mass
  tie `∫₀¹ fiberDensity = ‖f‖²`), `actual_zak_representative_nonzero_mass`,
  `actual_zak_representative_active_pos`.

## What is isolated as the minimal residual (Task H)

The only genuinely Zak-analytic residue is the passage *from the `L²`-class HRT
relation* to *(a concrete representative window `g` of `f` together with) the a.e.
one-step Zak fibre equation for `concreteZakDense g`*.  This is isolated — **not as
an axiom** — as `StandardActualZakRepresentativeTheorem`, and the Task D
conversion `actual_zak_Lp_relation_to_ae_fiber_equation` extracts the a.e. fibre
equation from it.

## Downstream rewiring (Task F)

`actual_zak_nontrivial_fiber_extraction_from_relation`,
`zak_relation_feeds_ae_normalized_no_flat_band_actual_Zak`, and
`critical_mixed_final_contradiction_with_actual_Zak_fiber_extraction` route the
final Stage 6B contradiction through the **actual-Zak** residual
`StandardActualZakRepresentativeTheorem` and the existing a.e. return-cocycle
machinery (`nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle`,
`ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`).  They do
**not** depend on `StandardNontrivialFiberConstructionTheorem`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## Task C / Task B — actual Zak representative adapters -/

/-- **Task C — the actual Zak/Plancherel mass tie.**

For a bounded measurable window `g` supported in `[0,N)` that represents the `L²`
class `f` (`f =ᵐ g`), the total fibre mass of the **actual** Zak transform
`concreteZakDense g` equals `‖f‖²`:
`∫₀¹ fiberDensity (concreteZakDense g) s ds = ‖f‖²`.

This is the honest Zak/Plancherel isometry identity
(`actual_zak_total_fiber_mass_eq_norm_sq` combined with `Lp_two_norm_sq`), tying
the actual fibre mass to the window's `L²`-mass.  It is the field that forbids the
degenerate `F = 0` witness. -/
theorem actual_zak_representative_represents_Lp_Zak
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) (g : ℝ → ℂ)
    (hrep : (f : ℝ → ℂ) =ᵐ[volume] g)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0)
    (hmeas : Measurable g)
    (hbdd : ∃ C, ∀ t, ‖g t‖ ≤ C) :
    (∫ s in (0:ℝ)..1, fiberDensity (concreteZakDense g) s) = ‖f‖ ^ 2 := by
  rw [actual_zak_total_fiber_mass_eq_norm_sq N g hsupp hmeas hbdd, Lp_two_norm_sq f]
  exact MeasureTheory.integral_congr_ae (by filter_upwards [hrep] with t ht; rw [ht])

/-- **Task C — nonzero actual fibre mass from a nonzero window.**

If `f ≠ 0` (and `g` is a representative window as above), the total fibre mass of
the actual Zak transform `concreteZakDense g` is strictly positive. -/
theorem actual_zak_representative_nonzero_mass
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0) (g : ℝ → ℂ)
    (hrep : (f : ℝ → ℂ) =ᵐ[volume] g)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0)
    (hmeas : Measurable g)
    (hbdd : ∃ C, ∀ t, ‖g t‖ ≤ C) :
    0 < ∫ s in (0:ℝ)..1, fiberDensity (concreteZakDense g) s := by
  rw [actual_zak_representative_represents_Lp_Zak N f g hrep hsupp hmeas hbdd]
  exact pow_pos (norm_pos_iff.mpr hf) 2

/-- **Task C — positive-measure active fibres for the actual Zak transform.**

For a nonzero window the actual Zak transform `concreteZakDense g` has
positive-measure active fibres, the honest non-vacuity content. -/
theorem actual_zak_representative_active_pos
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0) (g : ℝ → ℂ)
    (hrep : (f : ℝ → ℂ) =ᵐ[volume] g)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0)
    (hmeas : Measurable g)
    (hbdd : ∃ C, ∀ t, ‖g t‖ ≤ C) :
    0 < MeasureTheory.volume (activeSet (concreteZakDense g) ∩ Set.Ioc (0:ℝ) 1) :=
  active_set_positive_from_L2Zak_isometry (concreteZakDense g)
    (actual_zak_representative_nonzero_mass N f hf g hrep hsupp hmeas hbdd)

/-! ## Task B — the actual Zak fibre extraction theorem -/

/-- **Task B — the actual Zak fibre extraction interface.**

This is the **correct** re-anchored extraction target.  Unlike the model-free
`StandardNontrivialFiberConstructionTheorem`, its fibre function is the *actual*
Zak transform `concreteZakDense g` of an actual window `g` representing the `L²`
class `f`, and the Plancherel tie is the genuine Zak/Plancherel identity.  The
single Zak-analytic input it asks for is the **a.e. one-step Zak fibre equation
for the actual transform** `concreteZakDense g` (the honest `L²`-class content of
the four-term HRT relation).

It produces a `NontrivialAEFiberExtraction` (Task B requirements: (1) `F`
represents the actual Zak transform of `f`; (2) `F` satisfies the a.e. one-step
equation; (3) the fibre mass identity is Plancherel `∫ fibreDensity = ‖f‖²`;
(4) active set has positive measure because `f ≠ 0`).  No model-free `F` is
allowed. -/
def StandardActualZakFiberExtractionTheorem : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (N : ℕ) (g : ℝ → ℂ)
    (_hrep : (f : ℝ → ℂ) =ᵐ[volume] g)
    (_hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0)
    (_hmeas : Measurable g)
    (_hbdd : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (_h_one_step :
      ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (concreteZakDense g) x s),
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)

/-- **Task E — the actual Zak fibre extraction theorem is *proved*.**

The actual-Zak extraction interface holds unconditionally: assembling the
`NontrivialAEFiberExtraction` with `window := f` and `F := concreteZakDense g`,
the four structure fields are supplied by the actual Zak endpoints
(periodicity, fibre-density interval-integrability, the Zak/Plancherel mass tie)
together with the provided a.e. one-step equation.  The fibre function is the
genuine Zak transform of the window — never model-free, never `0`. -/
theorem actual_zak_nontrivial_fiber_extraction :
    StandardActualZakFiberExtractionTheorem := by
  intro m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ f hf N g hrep hsupp hmeas hbdd h_one_step
  exact ⟨{ window := f
           h_window_ne := hf
           F := concreteZakDense g
           hF_periodic_s := actual_zak_representative_periodic_s g
           h_density_integrable :=
             actual_zak_representative_fiberDensity_integrable N g hsupp hmeas hbdd
           h_plancherel :=
             actual_zak_representative_represents_Lp_Zak N f g hrep hsupp hmeas hbdd
           h_one_step_ae := h_one_step }⟩

/-! ## Task H — the minimal actual-Zak residual -/

/-- **Task H — the minimal actual-Zak residual.**

**DEPRECATED — `TOO_STRONG_FOR_GENERAL_L2`.**  This residual demands, for an
*arbitrary* `L²` class `f`, a window `g : ℝ → ℂ` that is bounded, measurable,
compactly supported in `[0,N)` **and** satisfies `f =ᵐ g`.  Such a representative
exists only for the dense subclass of bounded compactly supported functions, not
for a general `L²` equivalence class, so this proposition is too strong to be the
correct Zak-side blocker.  It is **superseded** by the corrected `L²`-level
residual `StandardActualL2ZakRepresentativeTheorem`
(`RequestProject/HRT/ActualL2ZakFiberExtraction.lean`), which selects a
representative of the **target** class `Z.Zak f` (which always exists) instead of
a compactly supported representative of `f`.  This definition and its downstream
lemmas are retained only for documentation/back-compat; new Stage 6B endpoints
route through the corrected `L²`-level residual.

The single genuinely Zak-analytic obligation remaining after re-anchoring: from a
nonzero `L²` class `f` satisfying the normalized four-term HRT relation in the
concrete a.e. Zak model, produce

* a concrete window `g` (bounded, measurable, supported in `[0,N)`) representing
  `f` (`f =ᵐ g`), and
* the a.e. one-step Zak fibre equation **for the actual transform**
  `concreteZakDense g`.

This is exactly the actual-Zak content (existence of a genuine window
representative carrying the `L²`-class relation as an a.e. fibre equation of the
*actual* Zak transform).  It is recorded as a precisely-typed proposition, **not**
an axiom, and **not** the model-free `StandardNontrivialFiberConstructionTheorem`. -/
def StandardActualZakRepresentativeTheorem : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    ∃ (N : ℕ) (g : ℝ → ℂ),
      ((f : ℝ → ℂ) =ᵐ[volume] g) ∧
      (∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0) ∧
      Measurable g ∧ (∃ C, ∀ t, ‖g t‖ ≤ C) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (concreteZakDense g) x s)

/-- **Task D — extracting the a.e. fibre equation from the `L²`-class relation.**

Given the actual-Zak residual `StandardActualZakRepresentativeTheorem`, the
`L²`-class one-step Zak relation (encoded by the four-term HRT relation `hrel` in
the concrete a.e. Zak model) yields a concrete window representative `g` of `f`
together with the a.e. one-step Zak fibre equation for the **actual** transform
`concreteZakDense g`:
`∀ᵐ s, ∀ᵐ x, oneStepEquation … (concreteZakDense g) x s`.

This is the precise Task D conversion (`L²`-class relation → a.e. fibre equation)
for an actual representative of the Zak transform. -/
theorem actual_zak_Lp_relation_to_ae_fiber_equation
    (hrep_thm : StandardActualZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∃ (N : ℕ) (g : ℝ → ℂ),
      ((f : ℝ → ℂ) =ᵐ[volume] g) ∧
      (∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → g t = 0) ∧
      Measurable g ∧ (∃ C, ∀ t, ‖g t‖ ≤ C) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (concreteZakDense g) x s) :=
  hrep_thm m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-! ## Task E — genuine nontrivial extraction from the actual Zak transform -/

/-- **Task E — genuine `NontrivialAEFiberExtraction` from the actual Zak
transform.**

Combining the actual-Zak residual `StandardActualZakRepresentativeTheorem` (which
supplies the concrete window `g` representing `f` and the a.e. one-step equation
for `concreteZakDense g`) with the *proved* extraction interface
`actual_zak_nontrivial_fiber_extraction`, a nonzero window satisfying the
normalized HRT relation in the concrete a.e. Zak model produces a genuine
`NontrivialAEFiberExtraction` whose fibre function is the **actual** Zak transform
`concreteZakDense g`.  No model-free construction is used. -/
theorem actual_zak_nontrivial_fiber_extraction_from_relation
    (hrep_thm : StandardActualZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) := by
  obtain ⟨N, g, hrep, hsupp, hmeas, hbdd, hone⟩ :=
    hrep_thm m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  exact actual_zak_nontrivial_fiber_extraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
    f hf N g hrep hsupp hmeas hbdd hone

/-! ## Task F — rewiring the downstream bridge through the actual Zak transform -/

/-- **Task F — actual Zak relation feeds the a.e. no-flat-band machinery.**

Given the actual-Zak residual `StandardActualZakRepresentativeTheorem`, a nonzero
window satisfying a normalized four-term HRT relation in the concrete a.e. Zak
model produces a genuine `NontrivialAEFiberExtraction` (fibre function = actual
Zak transform), which is converted **directly** to `AENormalizedReturnData` (no
pointwise upgrade) and fed into the Stage 5 no-flat-band theorem.

This depends on `StandardActualZakRepresentativeTheorem` (the actual-Zak
residual), and **not** on the model-free `StandardNontrivialFiberConstructionTheorem`. -/
theorem zak_relation_feeds_ae_normalized_no_flat_band_actual_Zak
    (hrep_thm : StandardActualZakRepresentativeTheorem)
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
  obtain ⟨ext⟩ := actual_zak_nontrivial_fiber_extraction_from_relation hrep_thm
    m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  exact ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle ext hm hθ_irr
      hc₀ hc₁ hc₂ hc₃ unimodular)
    DK hq H hH hHne S hSU hSpos hSres Efin hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **Task F — final Stage 6B contradiction with the actual Zak fibre extraction.**

The re-anchored replacement for
`critical_mixed_final_contradiction_without_Zak_extraction_interface`.  On the Zak
side it depends **only** on the actual-Zak residual
`StandardActualZakRepresentativeTheorem` — the fibre function is the genuine Zak
transform `concreteZakDense g` of the actual window, and the Plancherel mass tie
is the actual Zak/Plancherel identity.  It does **not** depend on the model-free
`StandardNontrivialFiberConstructionTheorem`.

The remaining hypotheses are the same non-Zak interfaces as the previous bridges:
the corrected periodic Denjoy–Koksma data (`DK`, `hq`), the analytic-rigidity /
periodic-gauge data (`H`, `J`, …), and the local Laurent holonomy root data
(`ad`, `coeffs`, `hroots`, `hJholo`). -/
theorem critical_mixed_final_contradiction_with_actual_Zak_fiber_extraction
    (hrep_thm : StandardActualZakRepresentativeTheorem)
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
  zak_relation_feeds_ae_normalized_no_flat_band_actual_Zak hrep_thm hm hθ_irr
    hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres Efin hE
    J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT
