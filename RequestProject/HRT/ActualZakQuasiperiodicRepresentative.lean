import Mathlib
import RequestProject.HRT.ActualL2ZakTargetRelation

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the **quasiperiodic** representative of the actual `L²`-level Zak
target class, and the corrected residual

## Why a quasiperiodic representative

The previous run anchored the residual on the *doubly periodic* representative
`zakPeriodicRep (concreteAEZakModel.Zak f)`, which is `1`-periodic in **both**
`x` and `s`.  The genuine Zak fibre is `1`-periodic in the frequency variable `s`
but **quasiperiodic** in the time variable `x`:
```
Zf(x+1, s) = e^{2π i s} · Zf(x, s),    Zf(x, s+1) = Zf(x, s).
```
For a doubly-periodic `F`, the all-of-`ℝ` one-step fibre equation is inconsistent
when `m ∤ p` (comparing `x` and `x+1` forces `F ≡ 0`), so the old blocker
`StandardActualZakRepresentativeEquationAE` is **over-strong** (false for
nondegenerate data).

This module builds the correct **quasiperiodic representative**
```
zakQuasiPeriodicRep G x s
  := exp (2π i · ⌊x⌋ · fract s) · (G : ℝ × ℝ → ℂ) (fract x, fract s),
```
which is `1`-periodic in `s`, satisfies `F(x+1,s) = e^{2π i s} · F(x,s)`, agrees
a.e. with the chosen `Lp` representative on the fundamental square, and is
`L²` there.  It is the formally correct object to anchor the residual on.

## What is proved here (unconditionally)

* `zakQuasiPeriodicRep_periodic_s` — `1`-periodicity in the frequency variable;
* `zakQuasiPeriodicRep_quasiperiodic_x` — quasiperiodicity in the time variable
  with the correct phase `e^{2π i s}`;
* `zakQuasiPeriodicRep_ae_eq_on_fundamental_domain` — a.e. agreement with the
  chosen `Lp` representative on the fundamental square;
* `zakQuasiPeriodicRep_memLp_on_fundamental_domain` — `L²([0,1]²)` membership.

## The corrected residual and downstream rewiring

* `StandardActualZakQuasiRepresentativeEquationAE` — the **corrected** minimal
  blocker: the a.e. one-step fibre equation for the *quasiperiodic*
  representative.  Unlike the doubly-periodic blocker it is consistent with Zak
  quasiperiodicity (no `x`-periodicity is imposed or used).
* `standardActualL2ZakRepresentativeTheorem_of_quasiEquationAE` — sound reduction
  of the corrected `L²`-level residual `StandardActualL2ZakRepresentativeTheorem`
  to the corrected blocker, using the quasiperiodic representative as the
  existential witness (it is `s`-periodic and an a.e. representative of the target
  class, as required downstream — which never needs `x`-periodicity).
* `actual_L2_zak_quasi_representative_extraction`,
  `actual_L2_zak_nontrivial_fiber_extraction_quasi` — Task E.
* `zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_quasi`,
  `critical_mixed_final_contradiction_with_actual_L2_Zak_quasi` — Task F downstream
  bridges replacing the doubly-periodic path.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## Task B — the canonical quasiperiodic representative -/

/-- **Task B — the canonical quasiperiodic representative of a target
`L²([0,1]²)` class.**

Pull `(x,s)` back to the fundamental square and insert the `x`-quasiperiodic
phase consistent with `Zf(x+1,s) = e^{2π i s} Zf(x,s)`,
`Zf(x,s+1) = Zf(x,s)`:
```
zakQuasiPeriodicRep G x s
  = exp (2π i · ⌊x⌋ · fract s) · (G : ℝ × ℝ → ℂ) (fract x, fract s).
```
It is `1`-periodic in `s` and quasiperiodic (not periodic) in `x`. -/
noncomputable def zakQuasiPeriodicRep (G : ZakTarget) : ℝ → ℝ → ℂ :=
  fun x s =>
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(⌊x⌋ : ℤ) : ℂ) * (↑(Int.fract s) : ℂ))
      * (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s)

/-- **Task B — `1`-periodicity in the frequency variable.**

`zakQuasiPeriodicRep G x (s + 1) = zakQuasiPeriodicRep G x s`, since
`Int.fract (s + 1) = Int.fract s` (and `⌊x⌋`, `Int.fract x` are unchanged). -/
theorem zakQuasiPeriodicRep_periodic_s (G : ZakTarget) (x s : ℝ) :
    zakQuasiPeriodicRep G x (s + 1) = zakQuasiPeriodicRep G x s := by
  unfold zakQuasiPeriodicRep
  rw [Int.fract_add_one]

/-
**Task B — quasiperiodicity in the time variable.**

`zakQuasiPeriodicRep G (x + 1) s = exp (2π i s) · zakQuasiPeriodicRep G x s`,
matching the genuine Zak convention `Zf(x+1,s) = e^{2π i s} Zf(x,s)`.
-/
theorem zakQuasiPeriodicRep_quasiperiodic_x (G : ZakTarget) (x s : ℝ) :
    zakQuasiPeriodicRep G (x + 1) s
      = Complex.exp (2 * ↑Real.pi * Complex.I * (s : ℂ)) * zakQuasiPeriodicRep G x s := by
  unfold zakQuasiPeriodicRep;
  norm_num [ ← mul_assoc, ← Complex.exp_add ];
  exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ -⌊s⌋, by push_cast [ Int.fract ] ; ring ⟩ )

/-
**Task B — the quasiperiodic representative agrees a.e. with the chosen `Lp`
representative on the fundamental square.**

On `(0,1]²` carrying `zakSquareMeasure`, `Int.fract` is the identity and `⌊x⌋ = 0`
off a null set, so the phase is `1` and the representative equals `(G : ℝ×ℝ→ℂ)`
almost everywhere.
-/
theorem zakQuasiPeriodicRep_ae_eq_on_fundamental_domain (G : ZakTarget) :
    (fun p : ℝ × ℝ => zakQuasiPeriodicRep G p.1 p.2)
      =ᵐ[zakSquareMeasure] ((G : ℝ × ℝ → ℂ)) := by
  have h_ae_eq : ∀ᵐ p : ℝ × ℝ ∂zakSquareMeasure, Int.fract p.1 = p.1 ∧ Int.fract p.2 = p.2 ∧ ⌊p.1⌋ = 0 := by
    have h_ae_eq : ∀ᵐ p : ℝ × ℝ ∂zakSquareMeasure, p.1 ∈ Set.Ioo 0 1 ∧ p.2 ∈ Set.Ioc 0 1 := by
      rw [ MeasureTheory.ae_iff ];
      erw [ MeasureTheory.Measure.restrict_apply' ];
      · rw [ show { a : ℝ × ℝ | ¬ ( a.1 ∈ Set.Ioo 0 1 ∧ a.2 ∈ Set.Ioc 0 1 ) } ∩ Set.Ioc 0 1 ×ˢ Set.Ioc 0 1 = ( { 1 } ×ˢ Set.Ioc 0 1 ) from ?_ ];
        · erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
        · grind;
      · exact measurableSet_Ioc.prod measurableSet_Ioc;
    have h_ae_eq : ∀ᵐ p : ℝ × ℝ ∂zakSquareMeasure, p.2 ≠ 1 := by
      rw [ MeasureTheory.ae_iff ] ; norm_num [ zakSquareMeasure ];
      erw [ MeasureTheory.Measure.restrict_apply' ];
      · erw [ show { a : ℝ × ℝ | a.2 = 1 } ∩ Set.Ioc 0 1 ×ˢ Set.Ioc 0 1 = ( Set.Ioc 0 1 ×ˢ { 1 } ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
      · exact measurableSet_Ioc.prod measurableSet_Ioc;
    filter_upwards [ ‹∀ᵐ p : ℝ × ℝ ∂zakSquareMeasure, p.1 ∈ Set.Ioo 0 1 ∧ p.2 ∈ Set.Ioc 0 1›, h_ae_eq ] with p hp hp' using ⟨ by linarith [ hp.1.1, hp.1.2, Int.fract_add_floor p.1, show ( ⌊p.1⌋ : ℝ ) = 0 from mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num; linarith [ hp.1.1 ], by norm_num; linarith [ hp.1.2 ] ⟩ ], by linarith [ hp.2.1, hp.2.2, Int.fract_add_floor p.2, show ( ⌊p.2⌋ : ℝ ) = 0 from mod_cast Int.floor_eq_iff.mpr ⟨ by norm_num; linarith [ hp.2.1 ], by norm_num; linarith [ hp.2.2, show p.2 < 1 from lt_of_le_of_ne hp.2.2 hp' ] ⟩ ], by norm_num [ show ⌊p.1⌋ = 0 from Int.floor_eq_iff.mpr ⟨ by norm_num; linarith [ hp.1.1 ], by norm_num; linarith [ hp.1.2 ] ⟩ ] ⟩;
  filter_upwards [ h_ae_eq ] with p hp ; unfold zakQuasiPeriodicRep ; simp +decide [ hp ] ;

/-- **Task B — the quasiperiodic representative is `L²([0,1]²)`.** -/
theorem zakQuasiPeriodicRep_memLp_on_fundamental_domain (G : ZakTarget) :
    MemLp (fun p : ℝ × ℝ => zakQuasiPeriodicRep G p.1 p.2) 2 zakSquareMeasure := by
  refine (MeasureTheory.memLp_congr_ae
    (zakQuasiPeriodicRep_ae_eq_on_fundamental_domain G)).mpr ?_
  exact Lp.memLp G

/-! ## Task C — the corrected residual equation (quasiperiodic) -/

/-- **Task C — the corrected minimal Zak-analytic blocker (quasiperiodic).**

The a.e. one-step fibre equation for the **quasiperiodic** representative
`zakQuasiPeriodicRep (concreteAEZakModel.Zak f)` of the target class.  Unlike the
doubly-periodic blocker `StandardActualZakRepresentativeEquationAE`, this requires
only `s`-periodicity, `x`-quasiperiodicity and the a.e. fibre equation — it is
consistent with the genuine Zak quasiperiodicity (no double periodicity in `x`). -/
def StandardActualZakQuasiRepresentativeEquationAE : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0),
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakQuasiPeriodicRep (concreteAEZakModel.Zak f)) x s

/-- **Task C — the a.e. one-step fibre equation for the quasiperiodic
representative, extracted from the corrected blocker.**

This is the explicit one-step Zak fibre equation in quasiperiodic form; it
requires only `s`-periodicity, `x`-quasiperiodicity and the a.e. fibre equation
(all carried by `zakQuasiPeriodicRep`), **not** double periodicity. -/
theorem target_relation_to_quasiRep_equation_ae
    (h : StandardActualZakQuasiRepresentativeEquationAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakQuasiPeriodicRep (concreteAEZakModel.Zak f)) x s :=
  h m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-! ## Task D — narrow target-operator formula blockers (quasiperiodic) -/

/-- **Task D — narrow lattice-operator fibre formula blocker (quasiperiodic).**

The exact missing explicit fibre action of the abstractly transported lattice
covariance operator `concreteAEZakModel.charLattice r t` on the target class,
expressed against the quasiperiodic representative.  Isolated as a precisely-typed
proposition (no axiom). -/
def StandardTargetLatticeOperatorFormulaQuasiAE : Prop :=
  ∀ (r t : ℤ) (G : ZakTarget),
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charLattice r t G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I *
            ((t : ℂ) * (p.1 : ℂ) + (r : ℂ) * (p.2 : ℂ)))
          * zakQuasiPeriodicRep G p.1 p.2)

/-- **Task D — narrow rogue-operator fibre formula blocker (quasiperiodic).**

The exact missing explicit fibre action of the abstractly transported rogue
covariance operator `concreteAEZakModel.charRogue a b` on the target class,
expressed against the quasiperiodic representative.  Isolated as a precisely-typed
proposition (no axiom). -/
def StandardTargetRogueOperatorFormulaQuasiAE : Prop :=
  ∀ (a b : ℝ) (G : ZakTarget),
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charRogue a b G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * zakQuasiPeriodicRep G (p.1 - a) (p.2 + b))

/-- **Task D — explicit a.e. lattice-operator fibre action on the quasiperiodic
representative**, conditional on the narrow lattice-operator blocker. -/
theorem charLattice_apply_quasiRep_ae
    (h : StandardTargetLatticeOperatorFormulaQuasiAE)
    (r t : ℤ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charLattice r t G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I *
            ((t : ℂ) * (p.1 : ℂ) + (r : ℂ) * (p.2 : ℂ)))
          * zakQuasiPeriodicRep G p.1 p.2) :=
  h r t G

/-- **Task D — explicit a.e. rogue-operator fibre action on the quasiperiodic
representative**, conditional on the narrow rogue-operator blocker. -/
theorem charRogue_apply_quasiRep_ae
    (h : StandardTargetRogueOperatorFormulaQuasiAE)
    (a b : ℝ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charRogue a b G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * zakQuasiPeriodicRep G (p.1 - a) (p.2 + b)) :=
  h a b G

/-! ## Task E — the corrected residual reduction and extraction -/

/-- **Task E — the corrected `L²`-level residual from the quasiperiodic blocker.**

The full corrected residual `StandardActualL2ZakRepresentativeTheorem` follows
from the quasiperiodic blocker: the quasiperiodic representative
`zakQuasiPeriodicRep (concreteAEZakModel.Zak f)` is an a.e. representative of the
target class (`zakQuasiPeriodicRep_ae_eq_on_fundamental_domain`), is `1`-periodic
in the frequency variable (`zakQuasiPeriodicRep_periodic_s`), and (by the blocker)
satisfies the a.e. one-step fibre equation.  Downstream consumers never need
`x`-periodicity, so the quasiperiodic representative is a valid witness. -/
theorem standardActualL2ZakRepresentativeTheorem_of_quasiEquationAE
    (h : StandardActualZakQuasiRepresentativeEquationAE) :
    StandardActualL2ZakRepresentativeTheorem := by
  intro m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  refine ⟨zakQuasiPeriodicRep (concreteAEZakModel.Zak f), ?_, ?_, ?_⟩
  · exact zakQuasiPeriodicRep_ae_eq_on_fundamental_domain _
  · exact fun x s => zakQuasiPeriodicRep_periodic_s _ x s
  · exact h m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-- **Task E — the quasiperiodic representative extraction.**

From the corrected quasiperiodic blocker and the `L²`-class HRT relation, the
quasiperiodic representative `F = zakQuasiPeriodicRep (concreteAEZakModel.Zak f)`
simultaneously represents the target class a.e., is `1`-periodic in the frequency
variable, and satisfies the a.e. one-step fibre equation. -/
theorem actual_L2_zak_quasi_representative_extraction
    (h : StandardActualZakQuasiRepresentativeEquationAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ((fun q : ℝ × ℝ => zakQuasiPeriodicRep (concreteAEZakModel.Zak f) q.1 q.2)
        =ᵐ[zakSquareMeasure] ((concreteAEZakModel.Zak f : ZakTarget) : ℝ × ℝ → ℂ)) ∧
      (∀ x s, zakQuasiPeriodicRep (concreteAEZakModel.Zak f) x (s + 1)
                = zakQuasiPeriodicRep (concreteAEZakModel.Zak f) x s) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
        oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
          (zakQuasiPeriodicRep (concreteAEZakModel.Zak f)) x s) :=
  ⟨zakQuasiPeriodicRep_ae_eq_on_fundamental_domain _,
   fun x s => zakQuasiPeriodicRep_periodic_s _ x s,
   h m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel⟩

/-- **Task E — genuine `NontrivialAEFiberExtraction` via the quasiperiodic
representative.**

The downstream `NontrivialAEFiberExtraction` built from the quasiperiodic
representative.  It carries `s`-periodicity (`hF_periodic_s`), the Plancherel mass
tie and the a.e. one-step equation — exactly the data the downstream machinery
consumes — and uses **no** `x`-periodicity. -/
theorem actual_L2_zak_nontrivial_fiber_extraction_quasi
    (h : StandardActualZakQuasiRepresentativeEquationAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) :=
  actual_L2_zak_nontrivial_fiber_extraction
    (standardActualL2ZakRepresentativeTheorem_of_quasiEquationAE h)
    m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-! ## Task F — downstream bridges through the quasiperiodic representative -/

/-- **Task F — corrected `L²`-level Zak relation feeds the a.e. no-flat-band
machinery, via the quasiperiodic representative.**

Replaces the doubly-periodic path: depends only on the corrected quasiperiodic
blocker `StandardActualZakQuasiRepresentativeEquationAE`. -/
theorem zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_quasi
    (h : StandardActualZakQuasiRepresentativeEquationAE)
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
    (standardActualL2ZakRepresentativeTheorem_of_quasiEquationAE h)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **Task F — final Stage 6B contradiction via the quasiperiodic representative.**

The corrected replacement for
`critical_mixed_final_contradiction_without_Zak_side_interface`.  On the Zak side
it depends **only** on the corrected quasiperiodic blocker
`StandardActualZakQuasiRepresentativeEquationAE`; the representative is the
quasiperiodic Zak fibre (consistent with quasiperiodicity in `x`, periodicity in
`s`), not the over-strong doubly-periodic one. -/
theorem critical_mixed_final_contradiction_with_actual_L2_Zak_quasi
    (h : StandardActualZakQuasiRepresentativeEquationAE)
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
    (standardActualL2ZakRepresentativeTheorem_of_quasiEquationAE h)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT