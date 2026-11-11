import RequestProject.Zak.IsometryExtension
import RequestProject.Zak.ZakTargetSpace
import RequestProject.Zak.ConcreteL2ZakModel
import RequestProject.HRT.ConcreteZakStage6B

/-!
# L² Zak completion run — import aggregator

Aggregates the modules added/used by the L² Zak completion run so this run can be
checked in isolation with
`lake env lean RequestProject/Zak/L2ZakCompletionImports.lean`.

New modules in this run:

* `RequestProject/Zak/IsometryExtension.lean` — the abstract Hilbert-space
  completion tool (`linear_isometry_extends_from_dense_subspace`,
  `continuous_linear_map_eq_of_eq_on_dense_subspace`).
* `RequestProject/Zak/ZakTargetSpace.lean` — the honest a.e.-level `L²` Zak model
  `L2ZakModelAE` and the dense-data reduction
  (`operator_intertwining_extends_from_dense`, `l2ZakModelAE_of_dense_data`).
-/
