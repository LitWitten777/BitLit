import RequestProject.Rotation.ConcreteVariation
import RequestProject.Rotation.C1VariationApprox
import RequestProject.Rotation.ConcreteDenjoyKoksma
import RequestProject.Rotation.WindingAdapter
import RequestProject.Rotation.PhaseLiftFromNonvanishing

/-!
# Run C import aggregator

Aggregates the Run C analytic-interface-cleanup modules:

* `ConcreteVariation`        — concrete `HasBV`/`variation`/`mean` and the
  `DenjoyKoksmaReturnData.ofConcrete` constructor (Task 1, target 1).
* `C1VariationApprox`        — `C¹` total-variation bound by the `L¹`-norm of the
  derivative (Task 1, target 2).
* `ConcreteDenjoyKoksma`     — variation approximation reduced to `L¹` density of
  derivatives (Task 1, target 3).
* `WindingAdapter`           — contour winding number, `wind = d` identification,
  and the public obstruction wrapper (Task 2, targets 2/3).
* `PhaseLiftFromNonvanishing`— phase lift of a nonvanishing periodic loop from a
  continuous logarithm (Task 2, target 1).
-/
