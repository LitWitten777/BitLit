# D1 integration manifest

| Kind | Source | Destination | Action |
|---|---|---|---|
| new | `lean/Equivocation.lean` | `QBX/Formal/Equivocation.lean` | move unchanged; add `public import QBX.Formal.Equivocation` to `QBX/Formal.lean`; `lake build QBXFormal` |
| new | `tests/test_d1_equivocation.py` | `foundation/tests/test_fnd_equivocation.py` (optional) | or leave in place; it runs from `phase_d/` today |
| patch | — | `ws6_certificates/SPEC.md` | new section "Multigraph ledgers — `QBX/Formal/Equivocation.lean` (registry H-076)" with rows E1–E6 of `docs/SPEC_D1.md` (Lean names under `EventLedger.`) |
| patch | — | `ws6_certificates/audit/AxiomAudit.lean` | `import QBX.Formal.Equivocation`; `#print axioms` for the eleven theorems of SPEC_D1 |
| patch | — | `QBX/Formal/HYPOTHESIS_REGISTRY.md` | row H-076: "Multigraph ledgers (Phase D, D1, E1–E6): two disagreeing events on one pair are a fork; a ledger is flat iff self-loops are trivial, parallel events agree and the merged connection (any representative per pair) is flat; flat iff pure gauge; an event is a bridge of the multigraph iff its pair is a merged bridge with no other event (correctness of `blind_spots`); a single-event fork is detected iff the event is not a bridge" — `QBX.Formal.Gauge.EventLedger.isFlat_iff`, `isBridgeEvent_iff`, `perturb_detected_iff_not_isBridgeEvent`, … — `Equivocation.lean` |
| patch | — | `QBX/README.md` formal-layer table | row `Equivocation.lean` |
| patch | — | `ws3_consensus/README.md` | cite E2/E5 next to the equivocation and blind-spot paragraphs |

No contract amendment.
