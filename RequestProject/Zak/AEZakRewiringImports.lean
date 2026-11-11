import RequestProject.Zak.ConcreteZakDenseSubspace
import RequestProject.Zak.ConcreteZakAEModel
import RequestProject.HRT.ZakToNormalizedCocycleAE

/-!
# A.e. Zak rewiring run — import aggregator

Aggregates the modules added by the concrete-a.e.-Zak-model and Stage-6B
rewiring run so this run can be checked in isolation with
`lake env lean RequestProject/Zak/AEZakRewiringImports.lean`.

New modules in this run:

* `RequestProject/Zak/ConcreteZakDenseSubspace.lean` (TASK B) — the concrete
  dense test subspace `concreteZakDenseSubspace` of `L²(ℝ)` (continuous
  compactly supported classes), with `concreteZakDenseSubspace_dense` and shift /
  modulation closure.
* `RequestProject/Zak/ConcreteZakAEModel.lean` (TASKs C/D) — the concrete
  a.e.-level Zak model assembly `concrete_L2ZakModelAE_of_data` /
  `concrete_L2ZakModelAE_nonempty`, with the isolated lift obligation
  `StandardConcreteZakToLpTheorem`.
* `RequestProject/HRT/ZakToNormalizedCocycleAE.lean` (TASKs E/F) — the a.e.
  Stage 6B bridge `hrt_relation_to_one_step_zak_equation_AE`,
  `zak_relation_feeds_normalized_no_flat_band_AE`,
  `zak_relation_feeds_normalized_no_flat_band_concrete_AE`,
  `critical_mixed_final_contradiction_without_pointwise_Zak_interface`, with the
  isolated active-fibre extraction obligation `StandardAEFiberExtractionTheorem`.
-/
