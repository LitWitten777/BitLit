import Mathlib
import RequestProject.HRT.ActualZakFiberExtraction
import RequestProject.HRT.ConcreteAEZakContradiction

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the corrected **`L²`-level** actual-Zak fibre extraction

## Why the previous residual was too strong

The previous run's residual `StandardActualZakRepresentativeTheorem`
(`RequestProject/HRT/ActualZakFiberExtraction.lean`) asks, for an **arbitrary**
`L²` class `f`, for a window
```
g : ℝ → ℂ
```
that is bounded, measurable, compactly supported in `[0,N)` **and** satisfies
`f =ᵐ g`.  Compactly supported bounded functions are dense in `L²`, but a *fixed*
`L²` equivalence class need not contain such a representative: a generic `L²`
function is neither bounded nor compactly supported.  Hence that residual is
`TOO_STRONG_FOR_GENERAL_L2`.

## The correct anchoring

The honest object to choose a representative of is **not** `f` but the **target**
`L²` class produced by the a.e.-level Zak transform,
```
Z.Zak f : ZakTarget = Lp ℂ 2 zakSquareMeasure ,
```
which *always* has a measurable representative `ℝ × ℝ → ℂ` (`Lp.aestronglyMeasurable`).
Its canonical curried fibre function `zakTargetFiber (Z.Zak f) x s = (Z.Zak f)(x,s)`
carries, **with no compact-support hypothesis on `f`**, the genuine
Zak/Plancherel mass identity through the *isometry* field of `L2ZakModelAE`:
```
  ∫₀¹ fiberDensity (zakTargetFiber (Z.Zak f)) s ds = ‖Z.Zak f‖² = ‖f‖² .
```

## What is proved here (unconditionally, no compact support of `f`)

* `Lp_has_measurable_representative`, `zak_Lp_class_has_representative`,
  `actual_L2_Zak_representative_ae_eq` — representative selection for the **target**
  `Lp` class (Task C).
* `zakTarget_fiberDensity_integrable`, `zakTarget_mass_eq_norm_sq` — interval
  integrability of the fibre density and the Zak target mass identity
  `∫₀¹ fiberDensity = ‖G‖²` (Task E, Plancherel core).
* `actual_L2_zak_total_mass_eq_norm_sq`, `actual_L2_zak_active_set_positive_of_nonzero_window`
  — the isometric mass tie `= ‖f‖²` and positive-measure active fibres for `f ≠ 0`,
  using **only** the isometry, never a compactly supported representative of `f`
  (Task E).
* `actual_L2_zak_total_mass_eq_norm_sq_rep`,
  `actual_L2_zak_fiberDensity_integrable_rep` — the same facts transported to an
  arbitrary a.e.-representative of the target class (so a *periodic* fibre
  representative may be used downstream).

## The corrected residual and downstream rewiring

* `StandardActualL2ZakRepresentativeTheorem` — the corrected residual (Task B):
  from `f ≠ 0` and the `L²`-class one-step Zak relation in the concrete a.e. model,
  produce an a.e.-**representative** of the target class `Z.Zak f` that is periodic
  in the frequency variable and satisfies the a.e. one-step fibre equation.  It
  asks for a representative of `Z.Zak f`, **not** of `f`, and carries no
  compact-support data.
* `actual_L2_zak_relation_to_ae_product_equation`,
  `actual_L2_zak_relation_to_ae_fibre_equation` — Task D extraction from the
  corrected residual.
* `actual_L2_zak_nontrivial_fiber_extraction`,
  `actual_L2_zak_nontrivial_fiber_extraction_from_relation` — Task F: genuine
  `NontrivialAEFiberExtraction` whose fibre function represents `Z.Zak f`, with the
  proved Plancherel mass tie.
* `zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak`,
  `critical_mixed_final_contradiction_with_actual_L2_Zak_fiber_extraction` —
  Task G: downstream endpoints depending on the corrected `L²`-level residual,
  **not** on the too-strong compact-support representative theorem.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## Task C — representative selection for the **target** `Lp` class -/

/-- **Task C — every `Lp` class has a measurable representative.**

The canonical coercion `(G : α → ℂ)` of an `L²` class is almost-everywhere
strongly measurable.  This is the honest representative-selection fact; it holds
for *every* `Lp` class (in particular it requires no boundedness or compact
support). -/
theorem Lp_has_measurable_representative {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (G : Lp ℂ 2 μ) :
    AEStronglyMeasurable (G : α → ℂ) μ :=
  Lp.aestronglyMeasurable G

/-- **Task C — the target Zak class has a measurable representative.**

The target class `Z.Zak f : ZakTarget = Lp ℂ 2 zakSquareMeasure` has a measurable
representative `ℝ × ℝ → ℂ`.  This is the class we select a representative of —
**not** `f`. -/
theorem zak_Lp_class_has_representative
    (Z : L2ZakModelAE V ZakTarget) (f : V) :
    AEStronglyMeasurable ((Z.Zak f : ZakTarget) : ℝ × ℝ → ℂ) zakSquareMeasure :=
  Lp.aestronglyMeasurable _

/-- The canonical curried fibre function of a target `L²([0,1]²)` class
`G : ZakTarget`: `zakTargetFiber G x s = G(x,s)`. -/
noncomputable def zakTargetFiber (G : ZakTarget) : ℝ → ℝ → ℂ :=
  fun x s => (G : ℝ × ℝ → ℂ) (x, s)

/-- **Task C — the canonical fibre function represents the target class a.e.**

The curried fibre function `zakTargetFiber (Z.Zak f)` agrees, as a function of
`(x,s)`, with the target representative of `Z.Zak f` almost everywhere on the unit
square.  (It is literally the curried coercion, so the agreement is definitional.) -/
theorem actual_L2_Zak_representative_ae_eq
    (Z : L2ZakModelAE V ZakTarget) (f : V) :
    (fun p : ℝ × ℝ => zakTargetFiber (Z.Zak f) p.1 p.2)
      =ᵐ[zakSquareMeasure] ((Z.Zak f : ZakTarget) : ℝ × ℝ → ℂ) := by
  filter_upwards [] with p; rfl

/-! ## Task E — Plancherel mass and integrability for the target representative -/

/-
**Task E — interval integrability of the target fibre density.**

For a target `L²([0,1]²)` class `G`, the fibre density
`s ↦ ∫₀¹ ‖G(x,s)‖² dx` is interval-integrable on `[0,1]`.  This is the Fubini
regularity of an `L²` function on the unit square.
-/
theorem zakTarget_fiberDensity_integrable (G : ZakTarget) :
    IntervalIntegrable (fiberDensity (zakTargetFiber G)) volume 0 1 := by
  have h_integrable : MeasureTheory.Integrable (fun p : ℝ × ℝ => ‖(G : ℝ × ℝ → ℂ) p‖ ^ 2) (MeasureTheory.Measure.prod (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc 0 1)) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc 0 1))) := by
    convert ( Lp.memLp G ).norm.integrable_sq using 1;
    convert MeasureTheory.Measure.prod_restrict _ _ using 1; all_goals infer_instance;
  rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one ];
  have := h_integrable.integral_prod_right;
  refine' this.congr _;
  filter_upwards [ ] with y using by rw [ fiberDensity, intervalIntegral.integral_of_le zero_le_one ] ; rfl;

/-
**Task E — the Zak target mass identity (Plancherel core).**

For a target `L²([0,1]²)` class `G`, the total fibre mass of its canonical fibre
function equals the squared `L²`-norm of `G`:
`∫₀¹ fiberDensity (zakTargetFiber G) s ds = ‖G‖²`.  This is the honest Plancherel
content (Fubini on the unit square plus `Lp_two_norm_sq`); it needs **no** window
data at all.
-/
theorem zakTarget_mass_eq_norm_sq (G : ZakTarget) :
    (∫ s in (0:ℝ)..1, fiberDensity (zakTargetFiber G) s) = ‖G‖ ^ 2 := by
  -- Write the L2 norm squared using Lp_two_norm_sq.
  have h_norm_sq : ‖G‖^2 = ∫ p in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, ‖G p‖^2 := by
    convert Lp_two_norm_sq G using 1;
  -- Apply Fubini's theorem to rewrite the integral over the product space as an iterated integral.
  have h_fubini : ∫ p in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, ‖G p‖^2 = ∫ s in Set.Ioc (0 : ℝ) 1, ∫ x in Set.Ioc (0 : ℝ) 1, ‖G (x, s)‖^2 := by
    erw [ MeasureTheory.setIntegral_prod ];
    · rw [ MeasureTheory.integral_integral_swap ];
      convert ( Lp.memLp G |> fun h => h.norm |> fun h => h.integrable_sq ) using 1;
      exact MeasureTheory.Measure.prod_restrict _ _;
    · exact MeasureTheory.MemLp.integrable_sq ( MeasureTheory.Lp.memLp _ |> fun h => h.norm );
  simp_all +decide [ intervalIntegral.integral_of_le zero_le_one, fiberDensity, zakTargetFiber ]

/-- **Task E — the isometric mass tie for the target Zak class.**

Combining the Zak target mass identity with the **isometry** field
`‖Z.Zak f‖ = ‖f‖` of `L2ZakModelAE`, the total fibre mass of the canonical fibre
function of `Z.Zak f` equals `‖f‖²`.  This is the corrected Plancherel tie: it
uses only the `L²` isometry, never a compactly supported representative of `f`. -/
theorem actual_L2_zak_total_mass_eq_norm_sq
    (Z : L2ZakModelAE V ZakTarget) (f : V) :
    (∫ s in (0:ℝ)..1, fiberDensity (zakTargetFiber (Z.Zak f)) s) = ‖f‖ ^ 2 := by
  rw [zakTarget_mass_eq_norm_sq, Z.Zak.norm_map]

/-- **Task E — positive-measure active fibres from a nonzero window.**

For `f ≠ 0`, the active fibre set of the canonical fibre function of `Z.Zak f`
has positive Lebesgue measure.  Proof: the total mass is `‖f‖² > 0` by the
isometric tie, and a nonnegative density with positive integral has
positive-measure support.  No compact-support representative of `f` is used. -/
theorem actual_L2_zak_active_set_positive_of_nonzero_window
    (Z : L2ZakModelAE V ZakTarget) (f : V) (hf : f ≠ 0) :
    0 < MeasureTheory.volume
      (activeSet (zakTargetFiber (Z.Zak f)) ∩ Set.Ioc (0:ℝ) 1) := by
  apply active_set_positive_from_L2Zak_isometry
  rw [actual_L2_zak_total_mass_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hf) 2

/-! ## Transport to an arbitrary a.e.-representative of the target class -/

/-- The fibre density of any a.e.-representative of the target class `G` agrees,
for a.e. frequency `s ∈ (0,1]`, with the fibre density of the canonical fibre
function `zakTargetFiber G`. -/
theorem rep_fiberDensity_ae_eq (G : ZakTarget) (F : ℝ → ℝ → ℂ)
    (hF : (fun p : ℝ × ℝ => F p.1 p.2) =ᵐ[zakSquareMeasure] (G : ℝ × ℝ → ℂ)) :
    fiberDensity F
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] fiberDensity (zakTargetFiber G) := by
  set μ := volume.restrict (Set.Ioc (0:ℝ) 1) with hμ
  have hprod : zakSquareMeasure = μ.prod μ := by
    rw [hμ, zakSquareMeasure, Measure.volume_eq_prod, Measure.prod_restrict]
  have hae : (ae zakSquareMeasure) = ae (μ.prod μ) := by rw [hprod]
  rw [hae] at hF
  have hfib : ∀ᵐ s ∂μ, ∀ᵐ x ∂μ, F x s = (G : ℝ × ℝ → ℂ) (x, s) := by
    have hswap : ∀ᵐ q ∂(μ.prod μ),
        (fun p : ℝ × ℝ => F p.1 p.2) (q.2, q.1) = (G : ℝ × ℝ → ℂ) (q.2, q.1) :=
      ((MeasureTheory.Measure.measurePreserving_swap
        (μ := μ) (ν := μ)).quasiMeasurePreserving.tendsto_ae).eventually hF
    exact Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hfib] with s hs
  unfold fiberDensity zakTargetFiber
  rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
  exact MeasureTheory.integral_congr_ae (by filter_upwards [hs] with x hx; rw [hx])

/-- **Task E (transported) — Plancherel mass tie for an arbitrary
representative.**

If `F` is *any* a.e.-representative of the target class `Z.Zak f`, then the total
fibre mass of `F` equals `‖f‖²`.  This lets a periodic representative be used
downstream while keeping the proved Plancherel tie. -/
theorem actual_L2_zak_total_mass_eq_norm_sq_rep
    (Z : L2ZakModelAE V ZakTarget) (f : V) (F : ℝ → ℝ → ℂ)
    (hF : (fun p : ℝ × ℝ => F p.1 p.2) =ᵐ[zakSquareMeasure] (Z.Zak f : ℝ × ℝ → ℂ)) :
    (∫ s in (0:ℝ)..1, fiberDensity F s) = ‖f‖ ^ 2 := by
  rw [← actual_L2_zak_total_mass_eq_norm_sq Z f,
      intervalIntegral.integral_of_le (zero_le_one),
      intervalIntegral.integral_of_le (zero_le_one)]
  exact MeasureTheory.integral_congr_ae (rep_fiberDensity_ae_eq (Z.Zak f) F hF)

/-- **Task E (transported) — interval integrability for an arbitrary
representative. -/
theorem actual_L2_zak_fiberDensity_integrable_rep
    (G : ZakTarget) (F : ℝ → ℝ → ℂ)
    (hF : (fun p : ℝ × ℝ => F p.1 p.2) =ᵐ[zakSquareMeasure] (G : ℝ × ℝ → ℂ)) :
    IntervalIntegrable (fiberDensity F) volume 0 1 := by
  have h := zakTarget_fiberDensity_integrable G
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one)] at h ⊢
  exact h.congr (((rep_fiberDensity_ae_eq G F hF)).symm)

/-! ## Task B — the corrected `L²`-level residual -/

/-- **Task B — the corrected `L²`-level actual-Zak residual.**

The single genuinely Zak-analytic obligation after correcting the anchoring: from
a nonzero `L²` class `f` satisfying the normalized four-term HRT relation in the
concrete a.e. Zak model, produce a fibre function `F : ℝ → ℝ → ℂ` that

* is an a.e.-**representative of the target class** `Z.Zak f`
  (`(fun p => F p.1 p.2) =ᵐ Z.Zak f`),
* is `1`-periodic in the frequency variable, and
* satisfies the a.e. one-step Zak fibre equation.

Crucially this asks for a representative of the **target** class `Z.Zak f`, which
always exists, and carries **no** compact-support or boundedness data on `f`.  It
is recorded as a precisely-typed proposition, **not** an axiom, and is not the
too-strong `StandardActualZakRepresentativeTheorem`. -/
def StandardActualL2ZakRepresentativeTheorem : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    ∃ F : ℝ → ℝ → ℂ,
      ((fun q : ℝ × ℝ => F q.1 q.2)
        =ᵐ[zakSquareMeasure] ((concreteAEZakModel.Zak f : ZakTarget) : ℝ × ℝ → ℂ)) ∧
      (∀ x s, F x (s + 1) = F x s) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s)

/-! ## Task D — extracting the a.e. fibre equation from the corrected residual -/

/-- **Task D — the corrected residual yields a representative carrying the a.e.
product/fibre equation.**

Given the corrected `L²`-level residual, the `L²`-class HRT relation produces a
representative `F` of the target class `Z.Zak f`, periodic in the frequency
variable, satisfying the a.e. one-step fibre equation.  (This is just
destructuring the residual; recorded under the requested name.) -/
theorem actual_L2_zak_relation_to_ae_product_equation
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∃ F : ℝ → ℝ → ℂ,
      ((fun q : ℝ × ℝ => F q.1 q.2)
        =ᵐ[zakSquareMeasure] ((concreteAEZakModel.Zak f : ZakTarget) : ℝ × ℝ → ℂ)) ∧
      (∀ x s, F x (s + 1) = F x s) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s) :=
  hrep_thm m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-- **Task D — the a.e. one-step fibre equation from the corrected residual.**

The fibre-equation projection of `actual_L2_zak_relation_to_ae_product_equation`. -/
theorem actual_L2_zak_relation_to_ae_fibre_equation
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∃ F : ℝ → ℝ → ℂ,
      (∀ x s, F x (s + 1) = F x s) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ F x s) := by
  obtain ⟨F, _, hper, hone⟩ :=
    actual_L2_zak_relation_to_ae_product_equation hrep_thm m p a c₀ c₁ c₂ c₃ hc₃
      r₁ t₁ r₂ t₂ f hf hrel
  exact ⟨F, hper, hone⟩

/-! ## Task F — the genuine `L²`-level nontrivial extraction -/

/-- **Task F — genuine `NontrivialAEFiberExtraction` from the corrected residual.**

From the corrected residual's representative `F` of the target class `Z.Zak f`
(periodic, a.e. one-step), together with the **proved** Plancherel mass tie
(`actual_L2_zak_total_mass_eq_norm_sq_rep`) and interval integrability
(`actual_L2_zak_fiberDensity_integrable_rep`), assemble a genuine
`NontrivialAEFiberExtraction` with `window := f` and fibre function `F`.  The
fibre function is an honest `L²`-level representative of the **target** Zak class;
no compactly supported representative of `f` is used and `F` is never the zero
function. -/
theorem actual_L2_zak_nontrivial_fiber_extraction
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) := by
  obtain ⟨F, hrepF, hper, hone⟩ :=
    actual_L2_zak_relation_to_ae_product_equation hrep_thm m p a c₀ c₁ c₂ c₃ hc₃
      r₁ t₁ r₂ t₂ f hf hrel
  exact ⟨{ window := f
           h_window_ne := hf
           F := F
           hF_periodic_s := hper
           h_density_integrable :=
             actual_L2_zak_fiberDensity_integrable_rep _ F hrepF
           h_plancherel :=
             actual_L2_zak_total_mass_eq_norm_sq_rep concreteAEZakModel f F hrepF
           h_one_step_ae := hone }⟩

/-- **Task F — genuine extraction from a relation (named alias).** -/
theorem actual_L2_zak_nontrivial_fiber_extraction_from_relation
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) :=
  actual_L2_zak_nontrivial_fiber_extraction hrep_thm m p a c₀ c₁ c₂ c₃ hc₃
    r₁ t₁ r₂ t₂ f hf hrel

/-! ## Task G — downstream rewiring through the corrected `L²`-level residual -/

/-- **Task G — corrected `L²`-level Zak relation feeds the a.e. no-flat-band
machinery.**

Given the corrected `L²`-level residual `StandardActualL2ZakRepresentativeTheorem`,
a nonzero window satisfying the normalized four-term HRT relation in the concrete
a.e. Zak model produces a genuine `NontrivialAEFiberExtraction` (fibre function =
representative of the **target** Zak class), converted to `AENormalizedReturnData`
and fed into the Stage 5 no-flat-band theorem.  This depends on the corrected
`L²`-level residual, and **not** on the too-strong compact-support representative
theorem `StandardActualZakRepresentativeTheorem`. -/
theorem zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
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
  obtain ⟨ext⟩ := actual_L2_zak_nontrivial_fiber_extraction_from_relation hrep_thm
    m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  exact ae_normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    (nontrivial_AE_fiber_extraction_feeds_ae_return_cocycle ext hm hθ_irr
      hc₀ hc₁ hc₂ hc₃ unimodular)
    DK hq H hH hHne S hSU hSpos hSres Efin hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

/-- **Task G — final Stage 6B contradiction with the corrected `L²`-level Zak
fibre extraction.**

The corrected replacement for
`critical_mixed_final_contradiction_with_actual_Zak_fiber_extraction`.  On the Zak
side it depends **only** on the corrected `L²`-level residual
`StandardActualL2ZakRepresentativeTheorem` — the fibre function is an honest
`L²`-level representative of the **target** Zak class `Z.Zak f`, and the
Plancherel mass tie is the isometric identity, with **no** compactly supported
representative of `f`.  The remaining hypotheses are the same non-Zak interfaces
as before (Denjoy–Koksma data, analytic-rigidity/periodic-gauge data, and the
local Laurent holonomy root data). -/
theorem critical_mixed_final_contradiction_with_actual_L2_Zak_fiber_extraction
    (hrep_thm : StandardActualL2ZakRepresentativeTheorem)
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
  zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak hrep_thm hm hθ_irr
    hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres Efin hE
    J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT