import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Concrete bounded variation and the Denjoy–Koksma return data (Run C, Task 1)

The Stage 2B interface `DenjoyKoksmaReturnData θ` keeps the analytic notions
(bounded-variation predicate `HasBV`, total-variation functional `variation`,
and period mean `mean`) abstract, carried as structure fields.  This module
makes those three notions **concrete**, instantiating them with the genuine
Mathlib objects:

* `ConcreteHasBV f`  — `BoundedVariationOn f (Set.Icc 0 1)` (finite total
  variation of `f` over one period);
* `concreteVariation f` — the real-valued total variation
  `(eVariationOn f (Set.Icc 0 1)).toReal`;
* `periodMean f` — the period integral `∫ x in Set.Ioc 0 1, f x`.

The Denjoy–Koksma bound itself is still genuinely deep (continued fractions),
so it is **kept as an interface field**, exactly as the run instructions
require.  The contribution here is `DenjoyKoksmaReturnData.ofConcrete`, a
constructor that produces a `DenjoyKoksmaReturnData θ` whose `HasBV`,
`variation`, `mean` are the concrete objects above, taking only the
Denjoy–Koksma estimate (stated in terms of these concrete objects) as input.

This removes the abstractness of three of the four interface fields.
-/

namespace CriticalMixedHRT

/-- Concrete **bounded variation** over one period `[0,1]`. -/
def ConcreteHasBV (f : ℝ → ℂ) : Prop :=
  BoundedVariationOn f (Set.Icc (0 : ℝ) 1)

/-- Concrete real-valued **total variation** of `f` over one period `[0,1]`. -/
noncomputable def concreteVariation (f : ℝ → ℂ) : ℝ :=
  (eVariationOn f (Set.Icc (0 : ℝ) 1)).toReal

/-- Concrete **period mean** of `f`, the integral over one period. -/
noncomputable def periodMean (f : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, f x

/-- The concrete total variation is always nonnegative. -/
theorem concreteVariation_nonneg (f : ℝ → ℂ) : 0 ≤ concreteVariation f :=
  ENNReal.toReal_nonneg

/-- **Concrete Denjoy–Koksma return data.**

Given rotation return data `R` (the continued-fraction return times) and the
Denjoy–Koksma estimate phrased with the *concrete* bounded-variation predicate
`ConcreteHasBV`, total variation `concreteVariation`, and period mean
`periodMean`, this assembles a `DenjoyKoksmaReturnData θ` whose three analytic
fields are exactly these concrete objects.

Only the genuinely deep Denjoy–Koksma inequality remains as input data. -/
noncomputable def DenjoyKoksmaReturnData.ofConcrete {θ : ℝ} (R : RotationReturnData θ)
    (dk : ∀ g : ℝ → ℂ, ConcreteHasBV g → periodMean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range (R.q n), g (x - (j : ℝ) * θ)‖ ≤ concreteVariation g) :
    DenjoyKoksmaReturnData θ where
  toRotationReturnData := R
  HasBV := ConcreteHasBV
  variation := concreteVariation
  mean := periodMean
  dk_bound := dk

@[simp] theorem DenjoyKoksmaReturnData.ofConcrete_HasBV {θ : ℝ}
    (R : RotationReturnData θ) (dk) :
    (DenjoyKoksmaReturnData.ofConcrete R dk).HasBV = ConcreteHasBV := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofConcrete_variation {θ : ℝ}
    (R : RotationReturnData θ) (dk) :
    (DenjoyKoksmaReturnData.ofConcrete R dk).variation = concreteVariation := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofConcrete_mean {θ : ℝ}
    (R : RotationReturnData θ) (dk) :
    (DenjoyKoksmaReturnData.ofConcrete R dk).mean = periodMean := rfl

@[simp] theorem DenjoyKoksmaReturnData.ofConcrete_q {θ : ℝ}
    (R : RotationReturnData θ) (dk) :
    (DenjoyKoksmaReturnData.ofConcrete R dk).q = R.q := rfl

end CriticalMixedHRT
