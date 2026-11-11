import Mathlib
import RequestProject.HRT.ActualZakQuasiperiodicRepresentative

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the quasiperiodic target-operator formulas, reduced to their
exact minimal representative interface

This module addresses the two remaining Zak-side target-operator formula blockers
isolated in `ActualZakQuasiperiodicRepresentative.lean`:

```
StandardTargetLatticeOperatorFormulaQuasiAE
StandardTargetRogueOperatorFormulaQuasiAE
```

## Why the blockers are *exactly* the remaining content

The canonical concrete a.e. Zak model `concreteAEZakModel` is obtained as a
`Classical.choice` of `Nonempty (L2ZakModelAE …)`; the abstractly transported
covariance operators `concreteAEZakModel.charLattice` /
`concreteAEZakModel.charRogue` are therefore only known through the **abstract
covariance laws** (`lattice_cov`, `rogue_cov`) of the model.  No explicit
pointwise/fibre representative of these operators is available from the model
structure alone, so the explicit a.e. fibre action of the covariance operators is
the genuinely missing Zak-analytic input.  It is isolated here (NOT as an axiom),
in the smallest exact form.

## What is proved here (no `sorry`, no axiom)

* `StandardTargetLatticeOperatorRepresentativeAE` — the **minimal modulation
  form** of the lattice operator formula: on the fundamental square the lattice
  covariance operator acts as multiplication by the lattice character
  `exp(-2π i (t x + r s))` on the *target class itself* (no quasiperiodic
  representative needed, since the two agree a.e. on the square).
* `StandardTargetRogueOperatorRepresentativeAE` — the minimal rogue form; the
  rogue operator genuinely transports the fibre off the fundamental square, so
  the quasiperiodic representative cannot be eliminated, and this coincides with
  `StandardTargetRogueOperatorFormulaQuasiAE`.
* `StandardTargetLatticeOperatorFormulaQuasiAE_iff_representative` — the lattice
  blocker is **equivalent** to its minimal modulation form (the only difference
  is replacing the target class by its a.e.-equal quasiperiodic representative).
* `StandardTargetRogueOperatorFormulaQuasiAE_iff_representative` — the rogue
  blocker equals its minimal form definitionally.
* `charLattice_apply_quasiRep_ae_closed`,
  `charRogue_apply_quasiRep_ae_closed` — the explicit a.e. fibre actions, now
  derived from the *minimal* representative interface.

These reductions discharge no genuine analytic content on their own (the
representative interface is logically equivalent to the original blocker); their
purpose is to record the blocker in its smallest, most canonical form, tied
directly to the target class and the lattice/rogue characters.
-/

namespace CriticalMixedHRT

/-! ## The minimal representative interface -/

/-- **Minimal modulation form of the lattice operator formula.**

On the fundamental square the abstractly transported lattice covariance operator
`concreteAEZakModel.charLattice r t` acts as pointwise multiplication by the
lattice character `exp(-2π i (t x + r s))` on the target class `G` itself.  This
is the smallest exact form of `StandardTargetLatticeOperatorFormulaQuasiAE`: on
the square the quasiperiodic representative agrees a.e. with `G`, so no
representative is needed on the right-hand side. -/
def StandardTargetLatticeOperatorRepresentativeAE : Prop :=
  ∀ (r t : ℤ) (G : ZakTarget),
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charLattice r t G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I *
            ((t : ℂ) * (p.1 : ℂ) + (r : ℂ) * (p.2 : ℂ)))
          * (G : ℝ × ℝ → ℂ) p)

/-- **Minimal form of the rogue operator formula.**

The rogue covariance operator genuinely transports the fibre off the fundamental
square (the argument is shifted to `(x - a, s + b)`), so the quasiperiodic
representative cannot be reduced to `G`.  The minimal rogue interface therefore
coincides with `StandardTargetRogueOperatorFormulaQuasiAE`. -/
def StandardTargetRogueOperatorRepresentativeAE : Prop :=
  StandardTargetRogueOperatorFormulaQuasiAE

/-! ## The reductions -/

/-- **Lattice blocker ⇐ minimal modulation form.** -/
theorem StandardTargetLatticeOperatorFormulaQuasiAE_of_representative
    (h : StandardTargetLatticeOperatorRepresentativeAE) :
    StandardTargetLatticeOperatorFormulaQuasiAE := by
  intro r t G
  have hrep := h r t G
  have hG := zakQuasiPeriodicRep_ae_eq_on_fundamental_domain G
  filter_upwards [hrep, hG] with p hp hpG
  rw [hp, hpG]

/-- **Lattice blocker ⇒ minimal modulation form.** -/
theorem representative_of_StandardTargetLatticeOperatorFormulaQuasiAE
    (h : StandardTargetLatticeOperatorFormulaQuasiAE) :
    StandardTargetLatticeOperatorRepresentativeAE := by
  intro r t G
  have hrep := h r t G
  have hG := zakQuasiPeriodicRep_ae_eq_on_fundamental_domain G
  filter_upwards [hrep, hG] with p hp hpG
  rw [hp, hpG]

/-- **The lattice blocker is exactly its minimal modulation form.** -/
theorem StandardTargetLatticeOperatorFormulaQuasiAE_iff_representative :
    StandardTargetLatticeOperatorFormulaQuasiAE ↔
      StandardTargetLatticeOperatorRepresentativeAE :=
  ⟨representative_of_StandardTargetLatticeOperatorFormulaQuasiAE,
   StandardTargetLatticeOperatorFormulaQuasiAE_of_representative⟩

/-- **The rogue blocker is exactly its minimal form (definitional).** -/
theorem StandardTargetRogueOperatorFormulaQuasiAE_iff_representative :
    StandardTargetRogueOperatorFormulaQuasiAE ↔
      StandardTargetRogueOperatorRepresentativeAE :=
  Iff.rfl

/-! ## Explicit a.e. fibre actions from the minimal interface -/

/-- **Explicit a.e. lattice-operator fibre action on the quasiperiodic
representative, from the minimal modulation interface.** -/
theorem charLattice_apply_quasiRep_ae_closed
    (h : StandardTargetLatticeOperatorRepresentativeAE)
    (r t : ℤ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charLattice r t G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I *
            ((t : ℂ) * (p.1 : ℂ) + (r : ℂ) * (p.2 : ℂ)))
          * zakQuasiPeriodicRep G p.1 p.2) :=
  charLattice_apply_quasiRep_ae
    (StandardTargetLatticeOperatorFormulaQuasiAE_of_representative h) r t G

/-- **Explicit a.e. rogue-operator fibre action on the quasiperiodic
representative, from the minimal rogue interface.** -/
theorem charRogue_apply_quasiRep_ae_closed
    (h : StandardTargetRogueOperatorRepresentativeAE)
    (a b : ℝ) (G : ZakTarget) :
    (fun p : ℝ × ℝ =>
        (concreteAEZakModel.charRogue a b G : ℝ × ℝ → ℂ) p)
      =ᵐ[zakSquareMeasure]
    (fun p : ℝ × ℝ =>
        Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * zakQuasiPeriodicRep G (p.1 - a) (p.2 + b)) :=
  charRogue_apply_quasiRep_ae h a b G

end CriticalMixedHRT
