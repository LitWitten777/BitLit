import Mathlib
import RequestProject.HRT.ActualL2ZakFiberExtraction

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the canonical **frequency-periodic** representative of the actual
`L²`-level Zak target class, and the minimal residual reduction

This module discharges the *generic measure-theoretic* content of the corrected
`L²`-level residual `StandardActualL2ZakRepresentativeTheorem`
(`RequestProject/HRT/ActualL2ZakFiberExtraction.lean`) and reduces that residual
to the single genuinely Zak-analytic obligation, the **a.e. one-step fibre
equation** for the canonical periodic representative.

## Why a periodic representative

The downstream `NontrivialAEFiberExtraction` consumes a fibre function
`F : ℝ → ℝ → ℂ` that is `1`-periodic in the frequency variable.  An arbitrary
`Lp` representative of the target class `concreteAEZakModel.Zak f : ZakTarget` is
only defined a.e. on the fundamental square `(0,1]²` and carries no periodicity.
We therefore build the **canonical periodic representative**
```
zakPeriodicRep G x s := (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s),
```
the periodic extension from the fundamental domain of the chosen `Lp`
representative of `G`.  By construction it is `1`-periodic in *both* variables
(in particular in the frequency variable `s`), and it agrees with `G` almost
everywhere on the fundamental square `(0,1]²` (where `Int.fract` is the identity
off a null set).

## What is proved here (unconditionally, no compact support of `f`)

* `actual_L2_Zak_periodic_representative` — the canonical periodic representative
  exists (its definition `zakPeriodicRep`);
* `actual_L2_Zak_periodic_representative_periodic_s` — `1`-periodicity in the
  frequency variable (Task B);
* `actual_L2_Zak_periodic_representative_ae_eq` — a.e. equality with the chosen
  `Lp` representative on the target measure (Task B);
* `actual_L2_Zak_periodic_representative_memLp` — `L²([0,1]²)` membership of the
  periodic representative (Task B);
* `Lp_eq_to_ae_eq_representatives`, `Lp_relation_to_ae_product_relation`
  — Lp-equality / Lp-relation to a.e. product equality (Task C);
* `ae_product_eq_to_ae_fibre_eq'`, `ae_fiberwise_of_ae_prod'` — product-a.e. to
  fibre-a.e. conversion (Task D).

## The minimal residual reduction (Task E / Task F)

The only content of `StandardActualL2ZakRepresentativeTheorem` *not* discharged
here is the **a.e. one-step fibre equation** for the canonical periodic
representative.  At the level of the abstract a.e. Zak model
`concreteAEZakModel` the lattice/rogue covariance operators are realized by
transport through the isometric extension `zakExt` and carry **no explicit fibre
formula**, so the explicit `oneStepEquation` cannot be read off the abstract
covariance.  This is the genuine remaining Zak-analytic obligation; it is
isolated — *not* as an axiom — as the precisely-typed proposition
`StandardActualZakRepresentativeEquationAE`, the a.e. one-step fibre equation for
`zakPeriodicRep (concreteAEZakModel.Zak f)`.

`standardActualL2ZakRepresentativeTheorem_of_equationAE` then proves the full
residual `StandardActualL2ZakRepresentativeTheorem` from that single blocker by
supplying the canonical periodic representative for the a.e.-representative and
periodicity fields.  The downstream endpoints
`actual_L2_zak_nontrivial_fiber_extraction_closed`,
`zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_closed` and
`critical_mixed_final_contradiction_without_Zak_side_interface` are rewired to
depend on the minimal blocker.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## Task B — the canonical frequency-periodic representative -/

/-- **Task B — the canonical frequency-periodic representative of a target
`L²([0,1]²)` class.**

The periodic extension from the fundamental domain of the chosen `Lp`
representative of `G`:
`zakPeriodicRep G x s = (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s)`.  By
construction it is `1`-periodic in both variables. -/
noncomputable def zakPeriodicRep (G : ZakTarget) : ℝ → ℝ → ℂ :=
  fun x s => (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s)

/-- **Task B — the canonical periodic representative exists** (named wrapper for
its definition). -/
theorem actual_L2_Zak_periodic_representative (G : ZakTarget) :
    ∃ F : ℝ → ℝ → ℂ, F = zakPeriodicRep G :=
  ⟨zakPeriodicRep G, rfl⟩

/-- **Task B — `1`-periodicity in the frequency variable.**

`zakPeriodicRep G x (s + 1) = zakPeriodicRep G x s` for every `x, s`, since
`Int.fract (s + 1) = Int.fract s`. -/
theorem actual_L2_Zak_periodic_representative_periodic_s (G : ZakTarget) (x s : ℝ) :
    zakPeriodicRep G x (s + 1) = zakPeriodicRep G x s := by
  unfold zakPeriodicRep
  rw [Int.fract_add_one]

/-- **Task B — `1`-periodicity in the time variable** (bonus; the construction is
periodic in both variables). -/
theorem actual_L2_Zak_periodic_representative_periodic_x (G : ZakTarget) (x s : ℝ) :
    zakPeriodicRep G (x + 1) s = zakPeriodicRep G x s := by
  unfold zakPeriodicRep
  rw [Int.fract_add_one]

/-
**Task B — the canonical periodic representative agrees a.e. with the chosen
`Lp` representative.**

On the fundamental square `(0,1]²` carrying `zakSquareMeasure`, `Int.fract` is the
identity off the null set `{1} × ℝ ∪ ℝ × {1}`, so the periodic representative
equals the coercion `(G : ℝ × ℝ → ℂ)` almost everywhere.
-/
theorem actual_L2_Zak_periodic_representative_ae_eq (G : ZakTarget) :
    (fun p : ℝ × ℝ => zakPeriodicRep G p.1 p.2)
      =ᵐ[zakSquareMeasure] ((G : ℝ × ℝ → ℂ)) := by
  have hfract : ∀ᵐ p : ℝ × ℝ ∂zakSquareMeasure,
      Int.fract p.1 = p.1 ∧ Int.fract p.2 = p.2 := by
    rw [ MeasureTheory.ae_iff ] ; norm_num;
    erw [ MeasureTheory.Measure.restrict_apply' ];
    · refine' MeasureTheory.measure_mono_null _ _;
      exact Set.Ioc 0 1 ×ˢ { 1 } ∪ { 1 } ×ˢ Set.Ioc 0 1;
      · grind +splitImp;
      · erw [ MeasureTheory.measure_union_null ] <;> norm_num [ MeasureTheory.Measure.volume_eq_prod ];
    · exact measurableSet_Ioc.prod measurableSet_Ioc
  filter_upwards [hfract] with p hp
  unfold zakPeriodicRep
  rw [hp.1, hp.2]

/-- **Task B — the canonical periodic representative is `L²([0,1]²)`.**

It is a.e.-equal to the `Lp` class `G`, which is `MemLp`, so the periodic
representative is `MemLp` for `zakSquareMeasure`. -/
theorem actual_L2_Zak_periodic_representative_memLp (G : ZakTarget) :
    MemLp (fun p : ℝ × ℝ => zakPeriodicRep G p.1 p.2) 2 zakSquareMeasure := by
  refine (MeasureTheory.memLp_congr_ae
    (actual_L2_Zak_periodic_representative_ae_eq G)).mpr ?_
  exact Lp.memLp G

/-! ## Task C — Lp-equality / Lp-relation to a.e. product equality -/

/-- **Task C — equal `Lp` classes have a.e.-equal representatives** (named
wrapper). -/
theorem Lp_eq_to_ae_eq_representatives {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E]
    (f g : Lp E 2 μ) (h : f = g) : (f : α → E) =ᵐ[μ] (g : α → E) :=
  h ▸ Filter.EventuallyEq.rfl

/-- **Task C — an `Lp` four-term linear relation descends to an a.e.-pointwise
relation between representatives.** -/
theorem Lp_relation_to_ae_product_relation {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E]
    {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c₀ c₁ c₂ c₃ : 𝕜) (f₀ f₁ f₂ f₃ : Lp E 2 μ)
    (h : c₀ • f₀ + c₁ • f₁ + c₂ • f₂ + c₃ • f₃ = 0) :
    (fun x => c₀ • (f₀ : α → E) x + c₁ • (f₁ : α → E) x
        + c₂ • (f₂ : α → E) x + c₃ • (f₃ : α → E) x) =ᵐ[μ] 0 := by
  have h_ae : (c₀ • f₀ + c₁ • f₁ + c₂ • f₂ + c₃ • f₃ : Lp E 2 μ) =ᵐ[μ] 0 := by
    rw [h]; exact MeasureTheory.Lp.coeFn_zero E 2 μ
  filter_upwards [h_ae,
    MeasureTheory.Lp.coeFn_add (c₀ • f₀ + c₁ • f₁ + c₂ • f₂) (c₃ • f₃),
    MeasureTheory.Lp.coeFn_add (c₀ • f₀ + c₁ • f₁) (c₂ • f₂),
    MeasureTheory.Lp.coeFn_add (c₀ • f₀) (c₁ • f₁),
    MeasureTheory.Lp.coeFn_smul c₀ f₀, MeasureTheory.Lp.coeFn_smul c₁ f₁,
    MeasureTheory.Lp.coeFn_smul c₂ f₂, MeasureTheory.Lp.coeFn_smul c₃ f₃]
    with x hx hadd1 hadd2 hadd3 hs0 hs1 hs2 hs3
  simp only [Pi.add_apply, Pi.zero_apply] at hx hadd1 hadd2 hadd3 ⊢
  rw [hadd1, hadd2, hadd3, hs0, hs1, hs2, hs3] at hx
  simpa using hx

/-! ## Task D — product-a.e. to fibre-a.e. conversion -/

/-- **Task D — an a.e. equality on a product measure descends to a.e.-fibrewise
a.e. equality** (named wrapper). -/
theorem ae_product_eq_to_ae_fibre_eq' {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite ν]
    [NormedAddCommGroup E]
    {f g : α × β → E} (h : f =ᵐ[μ.prod ν] g) :
    ∀ᵐ x ∂μ, (fun y => f (x, y)) =ᵐ[ν] (fun y => g (x, y)) :=
  MeasureTheory.Measure.ae_ae_of_ae_prod h

/-- **Task D — a predicate holding a.e. on a product measure holds, for a.e.
first coordinate, a.e. in the second coordinate** (named wrapper). -/
theorem ae_fiberwise_of_ae_prod' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite ν]
    {P : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, P z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, P (x, y) :=
  MeasureTheory.Measure.ae_ae_of_ae_prod h

/-! ## Task E / Task F — the minimal residual reduction -/

/-- **The minimal remaining Zak-analytic blocker (Task F).**

The single content of `StandardActualL2ZakRepresentativeTheorem` not discharged
by the generic measure theory above: the **a.e. one-step fibre equation** for the
canonical periodic representative `zakPeriodicRep (concreteAEZakModel.Zak f)` of
the target class.

This is the genuine Zak covariance content: at the abstract level the model's
lattice/rogue covariance operators are realized by transport through the
isometric extension `zakExt` and carry no explicit fibre formula, so the explicit
`oneStepEquation` cannot be read off the abstract covariance.  It is isolated as a
precisely-typed proposition (referring to a **representative of the target class**,
with **no** compact-support / boundedness data on `f`), **not** an axiom. -/
def StandardActualZakRepresentativeEquationAE : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakPeriodicRep (concreteAEZakModel.Zak f)) x s

/-- **Task E — the corrected `L²`-level residual from the minimal blocker.**

Given the minimal a.e. one-step-equation blocker
`StandardActualZakRepresentativeEquationAE`, the full corrected residual
`StandardActualL2ZakRepresentativeTheorem` holds: the canonical periodic
representative `zakPeriodicRep (concreteAEZakModel.Zak f)` simultaneously
represents the target class a.e., is `1`-periodic in the frequency variable, and
(by the blocker) satisfies the a.e. one-step fibre equation. -/
theorem standardActualL2ZakRepresentativeTheorem_of_equationAE
    (h : StandardActualZakRepresentativeEquationAE) :
    StandardActualL2ZakRepresentativeTheorem := by
  intro m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  refine ⟨zakPeriodicRep (concreteAEZakModel.Zak f), ?_, ?_, ?_⟩
  · exact actual_L2_Zak_periodic_representative_ae_eq _
  · exact fun x s => actual_L2_Zak_periodic_representative_periodic_s _ x s
  · exact h m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-! ## Task E — downstream endpoints closed over the minimal blocker -/

/-- **Task E — the genuine `L²`-level nontrivial extraction, closed over the
minimal blocker.**

`actual_L2_zak_nontrivial_fiber_extraction` with the corrected residual
discharged from `StandardActualZakRepresentativeEquationAE`. -/
theorem actual_L2_zak_nontrivial_fiber_extraction_closed
    (h : StandardActualZakRepresentativeEquationAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) :=
  actual_L2_zak_nontrivial_fiber_extraction
    (standardActualL2ZakRepresentativeTheorem_of_equationAE h)
    m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-- **Task E — corrected `L²`-level Zak relation feeds the a.e. no-flat-band
machinery, closed over the minimal blocker.** -/
theorem zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_closed
    (h : StandardActualZakRepresentativeEquationAE)
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
  zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak
    (standardActualL2ZakRepresentativeTheorem_of_equationAE h)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **Task E — final Stage 6B contradiction without a Zak-side interface
hypothesis beyond the minimal blocker.**

The corrected `L²`-level Zak fibre extraction contradiction, with the residual
`StandardActualL2ZakRepresentativeTheorem` discharged from the minimal a.e.
one-step-equation blocker `StandardActualZakRepresentativeEquationAE`.  On the Zak
side this depends **only** on that minimal blocker — the periodic representative,
its a.e. agreement with the target class, the Plancherel mass tie and active
positivity are all proved unconditionally. -/
theorem critical_mixed_final_contradiction_without_Zak_side_interface
    (h : StandardActualZakRepresentativeEquationAE)
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
  critical_mixed_final_contradiction_with_actual_L2_Zak_fiber_extraction
    (standardActualL2ZakRepresentativeTheorem_of_equationAE h)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT