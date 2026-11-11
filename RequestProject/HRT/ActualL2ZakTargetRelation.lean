import Mathlib
import RequestProject.HRT.ActualL2ZakRepresentative

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the **target `Lp` one-step Zak relation** (Task C)

This module performs the one genuinely *unconditional* step of the corrected
`L²`-level Zak residual: applying the concrete a.e. Zak isometry
`concreteAEZakModel.Zak` to the normalized four-term HRT relation in the source
`L²(ℝ)` space and using the **abstract covariance fields** of the model
(`lattice_cov` for the two integer-lattice shifts, `rogue_cov` for the rogue
shift `(a, p/m)`) to obtain an equality of target `L²([0,1]²)` classes:
```
c₀ • Zf + c₁ • charLattice r₁ t₁ (Zf) + c₂ • charLattice r₂ t₂ (Zf)
        + c₃ • charRogue a (p/m) (Zf) = 0 .
```

This is the honest "target-side" form of the relation.  It needs **no** explicit
fibre formula for the (abstractly transported) covariance operators — only the
linearity of the isometry and the two covariance fields — so it is proved
unconditionally here.

The remaining content of the minimal blocker
`StandardActualZakRepresentativeEquationAE` is exactly to turn the abstract
covariance operators `charLattice` / `charRogue` appearing here into their
explicit pointwise fibre representatives; that is isolated separately (it is the
genuinely Zak-analytic core, blocked by the abstract transport construction of
the model's covariance operators).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-
**Task C — the target `Lp` one-step Zak relation.**

Apply the concrete a.e. Zak isometry to the source four-term HRT relation.  Using
linearity of the isometry together with the model's abstract lattice covariance
(for the two integer shifts `(r₁,t₁)`, `(r₂,t₂)`) and rogue covariance (for the
shift `(a, p/m)`), the relation descends to an equality of **target** `L²([0,1]²)`
classes in `ZakTarget`:
```
c₀ • Zf + c₁ • charLattice r₁ t₁ Zf + c₂ • charLattice r₂ t₂ Zf
        + c₃ • charRogue a (p/m) Zf = 0 ,   Zf := concreteAEZakModel.Zak f .
```
This is unconditional (no explicit fibre formula for the covariance operators is
used).
-/
theorem target_Lp_one_step_Zak_relation
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    c₀ • concreteAEZakModel.Zak f
      + c₁ • concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)
      + c₂ • concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)
      + c₃ • concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ))
          (concreteAEZakModel.Zak f) = 0 := by
  convert congr_arg ( fun x => ( concreteAEZakModel.Zak ) x ) hrel using 1;
  · simp +decide [ ← concreteAEZakModel.lattice_cov, ← concreteAEZakModel.rogue_cov, map_add, map_smul ];
  · exact Eq.symm ( map_zero _ )

/-! ## Canonicalizing the minimal blocker through the target relation -/

/-- **Canonical remaining Zak-analytic interface (Task G shape
`StandardTargetRelationToRepresentativeEquationAE`).**

The content of the minimal blocker `StandardActualZakRepresentativeEquationAE`
with its source-side hypothesis replaced by the (now unconditionally proved)
*target* `Lp` one-step relation.  Concretely: from a nonzero window `f` whose
target class `Zf := concreteAEZakModel.Zak f` satisfies the explicit target
four-term relation
```
c₀ • Zf + c₁ • charLattice r₁ t₁ Zf + c₂ • charLattice r₂ t₂ Zf
        + c₃ • charRogue a (p/m) Zf = 0 ,
```
the canonical periodic representative `zakPeriodicRep Zf` satisfies the a.e.
one-step fibre equation.

This isolates *exactly* the remaining Zak-analytic content: turning the
abstractly transported covariance operators `charLattice` / `charRogue` (applied
to the target class) into their explicit pointwise fibre representatives on
`zakPeriodicRep Zf`.  It mentions **no** source-side time-frequency shift
operators — it is tied directly to the target representative — and is therefore a
strictly more canonical form of the blocker than
`StandardActualZakRepresentativeEquationAE`. -/
def StandardTargetRelationToRepresentativeEquationAE : Prop :=
  ∀ (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (_hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (_hf : f ≠ 0)
    (_htgt : c₀ • concreteAEZakModel.Zak f
      + c₁ • concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)
      + c₂ • concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)
      + c₃ • concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ))
          (concreteAEZakModel.Zak f) = 0),
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakPeriodicRep (concreteAEZakModel.Zak f)) x s

/-- **Sound reduction of the minimal blocker to the target-relation interface.**

Feeding the unconditionally-proved `target_Lp_one_step_Zak_relation` discharges
the source-side hypothesis of `StandardActualZakRepresentativeEquationAE`, so the
canonical target-relation interface
`StandardTargetRelationToRepresentativeEquationAE` implies the minimal blocker.
Thus the Zak side now reduces to the strictly more canonical interface that no
longer refers to the source-side shift operators. -/
theorem standardActualZakRepresentativeEquationAE_of_targetRelation
    (h : StandardTargetRelationToRepresentativeEquationAE) :
    StandardActualZakRepresentativeEquationAE := by
  intro m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  exact h m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf
    (target_Lp_one_step_Zak_relation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ f hrel)

end CriticalMixedHRT