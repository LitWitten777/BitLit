import Mathlib
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.FiberOperator
import RequestProject.HRT.ReturnCocycleToNoFlatBand
import RequestProject.HRT.ZakToNormalizedCocycleAE
import RequestProject.HRT.ConcreteAEZakContradiction
import RequestProject.Zak.ZakFubiniRegularity
import RequestProject.Zak.ConcreteZakPlancherel

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the *nontrivial* a.e. fibre extraction (repair run)

The previously discharged `StandardAEFiberExtractionTheorem`
(`AEFiberExtraction (Lp ℂ 2 volume) ZakTarget`) is a pure **existence** statement
with **no nonvanishing constraint** on the extracted fibre function, and with the
model `Z`, window `f` and HRT relation `_hrel` all unused in the conclusion.
Consequently it is satisfied by the **zero fibre function** `F = 0`, so it does
not connect a nonzero `L²` window to nonzero active fibres or to genuine
return-cocycle data: it is *formally valid but too weak*.

This module formulates the honest strengthening:

* `oneStepEquation` — the one-step Zak fibre equation as a predicate of `(x,s)`.
* `NontrivialAEFiberExtraction` — a strengthened extraction structure carrying a
  **nonzero window**, the Plancherel/isometry tie `∫₀¹ (fibre density) = ‖window‖²`
  (so `F` genuinely represents the `L²` Zak transform's mass, ruling out `F = 0`),
  the **a.e.** one-step fibre equation, and (derived) **positive-measure active
  fibres**.
* `PointwiseNontrivialFiberData` — the variant carrying the *pointwise* one-step
  equation consumed downstream by `NormalizedReturnData`, again with the nonzero
  Plancherel tie (so still not satisfiable by `F = 0`).

We prove:

* the basic `Lp`/a.e. extraction lemmas that the zero-function shortcut skipped
  (TASK C);
* active-set positivity from a nonzero window via the concrete Zak Plancherel
  identity (TASK D);
* that the strengthened structures are **not** satisfiable by `F = 0`
  (`NontrivialAEFiberExtraction.window_ne_zero_forces_F_ne_zero`);
* the **genuine, non-vacuous downstream bridge** from `PointwiseNontrivialFiberData`
  to the Stage 5 no-flat-band contradiction (TASK F);
* the precise isolation of the two remaining analytic obligations as Lean
  propositions (TASK H): producing the nontrivial extraction from a nonzero
  window/relation, and upgrading the a.e. one-step equation to the pointwise data
  consumed downstream.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.  The weak
zero-witness theorem is left in place (documented as insufficient); **none** of
the strengthened results below use it, and the zero function is never used as a
witness for any strengthened statement.
-/

namespace CriticalMixedHRT

/-! ## TASK C — basic `Lp` / a.e. extraction lemmas -/

variable {α E : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [NormedAddCommGroup E]

/-- Equal `Lp` classes have a.e.-equal representatives. -/
theorem Lp_eq_implies_ae_eq_representatives
    (f g : Lp E 2 μ) (h : f = g) : (f : α → E) =ᵐ[μ] (g : α → E) :=
  h ▸ Filter.EventuallyEq.rfl

/-
A zero `Lp` class has an a.e.-zero representative.
-/
theorem Lp_zero_implies_ae_zero_representative
    (f : Lp E 2 μ) (h : f = 0) : (f : α → E) =ᵐ[μ] 0 := by
  convert MeasureTheory.Lp.coeFn_zero E 2 μ

/-
An `Lp` linear relation descends to an a.e.-pointwise relation between
representatives.
-/
theorem Lp_linear_relation_implies_ae_pointwise_relation
    {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c₀ c₁ : 𝕜) (f g : Lp E 2 μ)
    (h : c₀ • f + c₁ • g = 0) :
    (fun x => c₀ • (f : α → E) x + c₁ • (g : α → E) x) =ᵐ[μ] 0 := by
  have h_ae : (c₀ • f + c₁ • g : Lp E 2 μ) =ᵐ[μ] 0 := by
    convert Lp_zero_implies_ae_zero_representative _ h using 1;
  filter_upwards [ h_ae, MeasureTheory.Lp.coeFn_add ( c₀ • f ) ( c₁ • g ), MeasureTheory.Lp.coeFn_smul c₀ f, MeasureTheory.Lp.coeFn_smul c₁ g ] with x hx₁ hx₂ hx₃ hx₄ using by aesop;

omit [NormedAddCommGroup E] in
/-- An a.e. equality on a product measure descends to: for a.e. first
coordinate, the equality holds for a.e. second coordinate. -/
theorem ae_product_eq_to_ae_fibre_eq
    {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β} [SFinite ν]
    {f g : α × β → E} (h : f =ᵐ[μ.prod ν] g) :
    ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[ν] (fun y => g (x, y)) :=
  MeasureTheory.Measure.ae_ae_of_ae_prod h

/-- A predicate holding a.e. on a product measure holds, for a.e. first
coordinate, a.e. in the second coordinate. -/
theorem ae_fiberwise_of_ae_prod
    {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β} [SFinite ν]
    {P : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, P z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, P (x, y) :=
  MeasureTheory.Measure.ae_ae_of_ae_prod h

/-! ## TASK D — active-set positivity from a nonzero window -/

/-- **TASK D — nonzero window ⇒ positive-measure active fibres (concrete model).**

For a bounded measurable window supported in `[0,N)` with positive `L²`-mass, the
concrete Zak active fibre set has positive Lebesgue measure.  This is the honest
Plancherel/isometry content: total fibre mass `= ∫ ‖f‖² > 0`, and a nonnegative
density cannot vanish a.e.  Thin wrapper around
`concrete_active_set_positive_measure`. -/
theorem nonzero_window_has_positive_active_fibres (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hf : 0 < ∫ t, ‖f t‖ ^ 2) :
    0 < MeasureTheory.volume (activeSet (concreteZakDense f) ∩ Set.Ioc (0:ℝ) 1) :=
  concrete_active_set_positive_measure N f hsupp hmeas hbdd hf

/-- **TASK D — concrete a.e. Zak active-set positivity (named alias).**

The concrete a.e. Zak model's active fibre set has positive measure for a nonzero
bounded window supported in `[0,N)`.  Same content as
`nonzero_window_has_positive_active_fibres`, recorded under the name requested by
the task. -/
theorem concrete_AE_Zak_active_set_positive (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hf : 0 < ∫ t, ‖f t‖ ^ 2) :
    0 < MeasureTheory.volume (activeSet (concreteZakDense f) ∩ Set.Ioc (0:ℝ) 1) :=
  nonzero_window_has_positive_active_fibres N f hsupp hmeas hbdd hf

/-
**TASK D — active-set positivity from the abstract `L²` Plancherel identity.**

If the total fibre mass `∫₀¹ (fibre density) ds` is positive, then the active
fibre set has positive measure.  This is the model-independent core: a
nonnegative density with positive integral has positive-measure support.
-/
theorem active_set_positive_from_L2Zak_isometry
    (F : ℝ → ℝ → ℂ)
    (hpos : 0 < ∫ s in (0:ℝ)..1, fiberDensity F s) :
    0 < MeasureTheory.volume (activeSet F ∩ Set.Ioc (0:ℝ) 1) := by
  contrapose! hpos;
  rw [ intervalIntegral.integral_of_le zero_le_one ];
  rw [ MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ];
  filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( le_antisymm hpos ( zero_le _ ) ) ] with x hx using fun hx' => le_antisymm ( le_of_not_gt fun hx'' => hx ⟨ hx'', hx' ⟩ ) ( fiberDensity_nonneg F x )

/-! ## The one-step fibre equation predicate -/

/-- The one-step Zak fibre equation in the normalized critical mixed form,
as a predicate of the frequency/time point `(x,s)`. -/
def oneStepEquation (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ) (F : ℝ → ℝ → ℂ) (x s : ℝ) : Prop :=
  F (x - a) (s + (↑p / ↑m : ℝ)) =
    -c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑p / ↑m : ℂ)) * (↑x : ℂ))
      * Pfun c₀ c₁ c₂ r₁ t₁ r₂ t₂ x s * F x s

/-! ## TASK B — the strengthened nontrivial a.e. fibre extraction structure -/

/-- **TASK B — a strengthened a.e. fibre extraction.**

Unlike the weak `AEFiberExtraction` (an unconstrained existence statement
satisfied by `F = 0`), this structure ties the fibre function `F` to a **nonzero
window** through the Plancherel/isometry identity and only asserts the one-step
fibre equation **almost everywhere** (the honest result of applying an `L²`
isometry to a linear relation).  The nonzero window plus the Plancherel tie force
`F ≠ 0` and (TASK D) make the active fibre set positive-measure, so this
structure is **not** satisfiable by the zero fibre function. -/
structure NontrivialAEFiberExtraction (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ) where
  /-- The window whose `L²` Zak transform is represented by `F`. -/
  window : Lp ℂ 2 (volume : Measure ℝ)
  /-- The window is nonzero (a nontrivial HRT relation). -/
  h_window_ne : window ≠ 0
  /-- The extracted fibre function. -/
  F : ℝ → ℝ → ℂ
  /-- `F` is `1`-periodic in the frequency variable. -/
  hF_periodic_s : ∀ x s, F x (s + 1) = F x s
  /-- The fibre density is interval-integrable (Fubini regularity). -/
  h_density_integrable : IntervalIntegrable (fiberDensity F) volume 0 1
  /-- **`F` represents the `L²` Zak transform a.e.**, in the sense that the total
  fibre mass equals `‖window‖²` (the Zak/Plancherel isometry identity). -/
  h_plancherel : (∫ s in (0:ℝ)..1, fiberDensity F s) = ‖window‖ ^ 2
  /-- The one-step Zak fibre equation, holding **almost everywhere**. -/
  h_one_step_ae :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s

namespace NontrivialAEFiberExtraction

variable {m : ℕ} {p : ℤ} {a : ℝ} {c₀ c₁ c₂ c₃ : ℂ} {r₁ t₁ r₂ t₂ : ℤ}
  (ext : NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)

/-
The total fibre mass of a nontrivial extraction is positive.
-/
theorem total_mass_pos : 0 < ∫ s in (0:ℝ)..1, fiberDensity ext.F s := by
  rw [ ext.h_plancherel ] ; exact sq_pos_of_pos ( norm_pos_iff.mpr ext.h_window_ne ) ;

/-- **The extraction is non-vacuous: positive-measure active fibres.**

From the Plancherel tie and `window ≠ 0`, the active fibre set carries positive
Lebesgue measure.  In particular the structure is *not* satisfiable by `F = 0`. -/
theorem active_pos :
    0 < MeasureTheory.volume (activeSet ext.F ∩ Set.Ioc (0:ℝ) 1) :=
  active_set_positive_from_L2Zak_isometry ext.F ext.total_mass_pos

/-
**The strengthening is genuine: a nontrivial extraction forces `F ≠ 0`.**

If `F` vanished identically the total fibre mass would be `0 = ‖window‖²`, forcing
`window = 0`, contradicting `h_window_ne`.  Hence the zero fibre function is never
a witness for `NontrivialAEFiberExtraction`.
-/
theorem F_not_identically_zero : ext.F ≠ fun _ _ => (0 : ℂ) := by
  intro h;
  convert ext.total_mass_pos.ne' _;
  unfold fiberDensity; norm_num [ h ] ;

end NontrivialAEFiberExtraction

/-! ## The pointwise nontrivial fibre data (downstream-feedable form) -/

/-- **Pointwise nontrivial fibre data.**

The variant of `NontrivialAEFiberExtraction` carrying the **pointwise** one-step
equation (the form consumed by `NormalizedReturnData` and the proven Stage 5
no-flat-band machinery), while retaining the nonzero-window Plancherel tie.  Like
the a.e. structure it is **not** satisfiable by `F = 0`. -/
structure PointwiseNontrivialFiberData (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ) where
  /-- The nonzero window represented by `F`. -/
  window : Lp ℂ 2 (volume : Measure ℝ)
  /-- The window is nonzero. -/
  h_window_ne : window ≠ 0
  /-- The extracted fibre function. -/
  F : ℝ → ℝ → ℂ
  /-- `F` is `1`-periodic in the frequency variable. -/
  hF_periodic_s : ∀ x s, F x (s + 1) = F x s
  /-- The fibre density is interval-integrable. -/
  h_density_integrable : IntervalIntegrable (fiberDensity F) volume 0 1
  /-- The Zak/Plancherel isometry tie (forbids `F = 0`). -/
  h_plancherel : (∫ s in (0:ℝ)..1, fiberDensity F s) = ‖window‖ ^ 2
  /-- The one-step Zak fibre equation, holding **for every** `(x,s)`. -/
  hone : ∀ x s, oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s

/-- A `PointwiseNontrivialFiberData` term yields the Stage 6A `NormalizedReturnData`
needed by the Stage 5 no-flat-band machinery.  (The remaining structural data
— `m > 0`, irrationality of `m·a`, nonvanishing of the coefficients, the
unimodular basis — is supplied as hypotheses, exactly as in
`zak_relation_feeds_normalized_no_flat_band_AE`.) -/
def PointwiseNontrivialFiberData.toNormalizedReturnData
    {m : ℕ} {p : ℤ} {a : ℝ} {c₀ c₁ c₂ c₃ : ℂ} {r₁ t₁ r₂ t₂ : ℤ}
    (D : PointwiseNontrivialFiberData m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
    (hm : 0 < m) (hθ_irr : Irrational ((m : ℝ) * a))
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (unimodular : r₁ * t₂ - r₂ * t₁ = 1) :
    NormalizedReturnData :=
  { m := m, hm := hm, p := p, a := a, θ := (m : ℝ) * a, hθ_eq := rfl, hθ_irr := hθ_irr,
    c₀ := c₀, c₁ := c₁, c₂ := c₂, c₃ := c₃, hc₀ := hc₀, hc₁ := hc₁, hc₂ := hc₂, hc₃ := hc₃,
    r₁ := r₁, t₁ := t₁, r₂ := r₂, t₂ := t₂, unimodular := unimodular,
    F := D.F, hFper := D.hF_periodic_s, hone := D.hone }

/-! ## TASK F — the genuine, non-vacuous downstream bridge -/

/-- **TASK F — pointwise nontrivial fibre data feeds the no-flat-band theorem.**

Given genuine *pointwise nontrivial* fibre data `D` (with the nonzero-window
Plancherel tie, so **not** the zero witness) and the full Stage 5 / Stage 6A
no-flat-band input data, the Stage 5 machinery yields the no-flat-band
contradiction.  This routes through `NormalizedReturnData` and
`normalized_return_cocycle_feeds_no_flat_band_synthesized`, and does **not** use
the weak zero-witness theorem. -/
theorem pointwise_nontrivial_fiber_data_feeds_no_flat_band
    {m : ℕ} (hm : 0 < m) {p : ℤ} {a : ℝ}
    (hθ_irr : Irrational ((m : ℝ) * a))
    {c₀ c₁ c₂ c₃ : ℂ}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    {r₁ t₁ r₂ t₂ : ℤ} (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (D : PointwiseNontrivialFiberData m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
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
  normalized_return_cocycle_feeds_no_flat_band_synthesized
    (D.toNormalizedReturnData hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular)
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-! ## TASK H — isolation of the two remaining analytic obligations -/

/-- **Remaining obligation 1 — the genuine nontrivial extraction.**

For the concrete a.e. Zak model, a **nonzero** window satisfying a normalized
four-term HRT relation produces a `NontrivialAEFiberExtraction`.  This is the
honest analytic content skipped by the zero witness: choosing an `L²`
representative of `Z.Zak f`, transferring the `L²`-class one-step equation to the
a.e. fibre equation, and recording the Plancherel tie.  It is *not* an axiom; it
is the precisely-typed remaining proposition.  (It is *unsatisfiable* by `F = 0`,
since the Plancherel tie with `window = f ≠ 0` forces positive fibre mass.) -/
def StandardNontrivialFiberExtractionTheorem : Prop :=
  ∀ (Z : L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget)
    (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)

/-- **Remaining obligation 2 — the a.e.-to-pointwise fibre upgrade.**

**DEPRECATED / AVOIDABLE (AE refactor run).**  `StandardPointwiseFiberUpgradeTheorem`
is *not* the correct target for `L²` data: it asks for an a.e. fibre equation to
be upgraded to a pointwise-everywhere fibre equation, which is generally **too
strong** for an arbitrary `L²` quotient class (representatives are only defined up
to a null set).  It is **replaced** by the a.e.-level normalized return-cocycle
machinery in `AENormalizedReturnCocycle.lean` /
`AEReturnCocycleToNoFlatBand.lean`: the structure `AENormalizedReturnData`
consumes the honest **a.e.** one-step equation directly, the a.e. `m`-step return
cocycle is obtained by a.e. iteration
(`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`), and
`critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade`
derives the no-flat-band contradiction from
`StandardNontrivialFiberExtractionTheorem` alone, **without** this upgrade.  This
definition is retained (not deleted) only for documentation and backward
compatibility; downstream Stage 6B results no longer depend on it.

The Stage 5 no-flat-band machinery consumes the one-step equation **pointwise**
(`NormalizedReturnData.hone : ∀ x s`).  Upgrading the honest **a.e.** one-step
equation of a `NontrivialAEFiberExtraction` to the pointwise
`PointwiseNontrivialFiberData` (repairing the null set of bad fibres while keeping
the multiplicative relation and the Plancherel tie) is isolated here.  Not an
axiom. -/
def StandardPointwiseFiberUpgradeTheorem : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ),
    NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ →
    Nonempty (PointwiseNontrivialFiberData m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)

/-- **TASK E — nontrivial extraction from a relation (conditional reduction).**

Given the isolated obligation `StandardNontrivialFiberExtractionTheorem`, a
nonzero window satisfying a normalized HRT relation in the concrete a.e. Zak model
produces a `NontrivialAEFiberExtraction` — *not merely an arbitrary `F`*. -/
theorem nontrivial_AE_fiber_extraction_from_relation
    (hext : StandardNontrivialFiberExtractionTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) :=
  hext concreteAEZakModel m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-- **TASK F — Stage 6B contradiction from the nontrivial a.e. extraction.**

Given the strengthened extraction `ext : NontrivialAEFiberExtraction` (so **not**
the zero witness) and the a.e.-to-pointwise upgrade obligation
`StandardPointwiseFiberUpgradeTheorem`, together with the full no-flat-band data,
the Stage 5 machinery yields the contradiction.  Compared with the weak
`critical_mixed_final_contradiction_without_Zak_interface`, the fibre input here
is genuinely nonzero (the Plancherel tie forbids `F = 0`). -/
theorem zak_relation_feeds_normalized_no_flat_band_nontrivial_AE
    (hupg : StandardPointwiseFiberUpgradeTheorem)
    {m : ℕ} (hm : 0 < m) {p : ℤ} {a : ℝ}
    (hθ_irr : Irrational ((m : ℝ) * a))
    {c₀ c₁ c₂ c₃ : ℂ}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    {r₁ t₁ r₂ t₂ : ℤ} (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (ext : NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
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
  obtain ⟨D⟩ := hupg m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ ext
  exact pointwise_nontrivial_fiber_data_feeds_no_flat_band hm hθ_irr hc₀ hc₁ hc₂ hc₃
    unimodular D DK hq H hH hHne S hSU hSpos hSres Efin hE J hJgauge mlau Mlau ad
    had coeffs h_ad_coeff hroots hJholo

/-- **TASK F — final Stage 6B contradiction with the nontrivial a.e. Zak
extraction.**

Combining the two isolated obligations with a nonzero window and HRT relation in
the concrete a.e. Zak model, the contradiction follows.  Unlike
`critical_mixed_final_contradiction_without_Zak_interface`, this depends on the
*nontrivial* extraction obligations (unsatisfiable by `F = 0`), not the weak
zero-witness theorem. -/
theorem critical_mixed_final_contradiction_with_nontrivial_AE_Zak
    (hext : StandardNontrivialFiberExtractionTheorem)
    (hupg : StandardPointwiseFiberUpgradeTheorem)
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
  exact zak_relation_feeds_normalized_no_flat_band_nontrivial_AE hupg hm hθ_irr
    hc₀ hc₁ hc₂ hc₃ unimodular ext DK hq H hH hHne S hSU hSpos hSres Efin hE J
    hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT