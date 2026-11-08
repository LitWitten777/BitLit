# D1 — Status (2026-10-04)

> **Integrated (2026-10-04).** `lean/Equivocation.lean` now lives at
> `QBX/Formal/Equivocation.lean` (unchanged; imported by `QBX/Formal.lean`, built by
> `lake build QBXFormal`), and `tests/test_d1_equivocation.py` at
> `foundation/tests/test_fnd_equivocation.py`. SPEC rows E1–E6, registry H-076, axiom
> audit and README rows were added (log: `QBX/docs/foundation/PHASE_D_INTEGRATION_LOG.md`).
> Paths below refer to the pre-integration layout of this folder.

## Proved (Lean, `lean/Equivocation.lean`)

Checked with `lake env lean QBX/foundation/phase_d/D1_fork_theory/lean/Equivocation.lean`
from the repository root: no errors, no warnings. `#print axioms` on the main
theorems gives only `propext`, `Classical.choice`, `Quot.sound` (the two
equivocation lemmas use only `propext`). The file contains none of the words
rejected by `health.sh`.

Deliverable 1 (equivocation on multigraph ledgers), all three parts:

* disagreeing parallel events give a non-flat ledger —
  `EventLedger.not_isFlat_of_equivocation` (same direction, holonomy `g₁ g₂⁻¹`),
  `EventLedger.not_isFlat_of_equivocation_rev` (opposite directions, `g₁ g₂`);
* flat ⟺ parallel events agree ∧ merged connection flat (plus: self-loops
  trivial) — `EventLedger.isFlat_iff`, for every merged connection that takes each
  pair's transport from some event on it (`EventLedger.exists_represents`: one
  exists). Also `EventLedger.isFlat_iff_isPureGauge`;
* a pair with at least two events is never a bridge —
  `EventLedger.not_isBridgeEvent_of_parallel`.

Beyond the brief:

* `EventLedger.isBridgeEvent_iff` — correctness of the `blind_spots` filter: an
  event is a bridge of the multigraph iff its pair is a bridge of the merged graph
  and carries no other event;
* `EventLedger.perturb_detected_iff_not_isBridgeEvent` — F5 for multigraph
  ledgers;
* self-loops are covered (open item 4 of WS2, for ledgers).

Deliverable 2 (G1): already proved by WS1 (`QBX/Formal/MixedRadixGeometry.lean`,
H-100); cited in `docs/SPEC_D1.md`, not re-proved, so no `HypercubeConvex.lean`.

Deliverable 3: `docs/SPEC_D1.md`.

## Tested numerically (not proofs)

`tests/test_d1_equivocation.py` (9 tests, about 1 s): `consensus_check` agrees
with definition-level computations of E2, E3, E5, E6 on 2 × 300–400 random
ledgers with parallel events and self-loops.

## Open

* Nothing from the brief. The Lean model ties to Python through the statements
  only; there is no step-for-step model of `merge_events`.
* Integration (shared files) is proposed in `integration/MANIFEST.md`, not applied.
