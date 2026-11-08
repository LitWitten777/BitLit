# D4 — Status (2026-10-04)

> **Integrated (2026-10-04) as layer 9.** `d4_protocol/` now lives at
> `foundation/ws9_protocol/` (package renamed, `sys.path` fallback dropped), the
> docs at `foundation/ws9_protocol/docs/`, the tests at
> `foundation/tests/test_fnd_protocol_{connectivity,scenarios,witness}.py`, plus
> `ws9_protocol/PROPERTIES.md` and `tests/test_prop_protocol.py` (P9.1–P9.3).
> `REPORT.md` was regenerated with `python3 -m ws9_protocol 1000 --seed 2026
> --write` from `QBX/foundation/`: every count is unchanged, only timings moved.
> One code change: `brute_force_edge_connectivity` returned `max_k + 1` on a
> graph without edges while the other two methods return 0; it now returns 0
> (found by P9.2). FA-010 stays a draft here, awaiting the owner's decision.
> Log: `QBX/docs/foundation/PHASE_D_INTEGRATION_LOG.md`. Paths below refer to the
> pre-integration layout of this folder.

All seven deliverables of the brief are in place. Nothing here is a Lean proof;
the witness-rule claim has a paper proof (`docs/WITNESS.md`) plus exhaustive and
sampled tests. Every numerical claim below is from `docs/REPORT.md`, regenerated
by `python3 -m d4_protocol 1000 --seed 2026 --write` (run from this folder;
about 5 minutes). Trial `t` uses `random.Random("2026/t")`, so every number
except the timings is reproducible.

## Done-when criteria

| Criterion | Status | Evidence |
|---|---|---|
| ≥ 100 nodes | met | `Q_2 □ T²_5`, 100 nodes (`network.default_space`) |
| detection 100% for single forks (witness on) | met | 2000 / 2000 (dense + sparse) |
| detection 100% for equivocations, either direction | met | 2000 / 2000 |
| detection 100% for forks on fewer than λ pairs | met | 2000 / 2000 |
| false alarms 0% | met | 0 / 3000 honest runs |
| blind spots: none with the witness rule | met | 0 blind spots in 2000 witness runs; proof in `docs/WITNESS.md` |
| reproducible from a fixed seed | met | per-trial seeds, see above |
| tests under 60 s | met | `tests/test_d4_*.py`: 26 tests, about 5 s |

## Deliverables

1. **Network** (`d4_protocol/network.py`): nodes on `Q_2 □ T²_5`, private states
   in S₄ (non-abelian by default), rounds, per-message loss.
2. **Witness rule** (`d4_protocol/witness.py`, `docs/WITNESS.md`): the square
   rule; every event closes a 4-cycle, so the event graph is bridgeless and each
   component is 2-edge-connected (paper proof; exhaustive test on five small
   spaces, sampled on 100 nodes). Overhead: 3.00 witness messages per payload
   (re-sends included), 0.03% of payloads dropped at loss 0.05.
3. **λ** (`d4_protocol/connectivity.py`): Stoer–Wagner with the cut, unit-capacity
   max flow, brute force; the three agree on 150 random small graphs (test) and
   Stoer–Wagner = max flow on every tenth report trial (100 checks, 0
   mismatches). λ in the dense regime: 2–6 (mostly 4–5); sparse: always 2.
4. **Scenarios** (`d4_protocol/scenarios.py`): honest; single changed event;
   equivocation (both directions); coordinated fork on `t < λ` pairs; whole
   minimum cut (undetected, F6c); witness rule off (blind-spot forks undetected
   and listed); reordering (detected with S₄, invisible with Z/24).
5. **Localization**: for single forks and equivocations the planted pair lies on
   the loop of every entry of `report.forks` (4000 / 4000).
6. **Attack catalogue** (`docs/ATTACKS.md`): no disagreement between
   implementation and theory; five observations, one of which motivates the
   draft amendment FA-010.
7. **Report** (`docs/REPORT.md`).

## Open / limits

* The witness rule guarantees λ ≥ 2 only; in the sparse regime a fork on the two
  pairs of a minimum cut is undetectable, as F6c says it must be.
* λ is computed on the merged simple graph, matching the Lean F6a statement;
  a multigraph version of F6a is not proved.
* Localization uses `merge_events` and `spanning_tree` in addition to the frozen
  report (FA-010 draft would remove this need).
* No Lean file in this workstream.
* Integration proposed in `integration/MANIFEST.md` (new layer `ws9_protocol`),
  not applied.

## Update (2026-10-04, closing run)

FA-010 was **approved by the owner** (recommendation adopted) and applied: `ConsensusReport`
gains `edge_connectivity` and the fork-kind count `n_equivocations`, filled by
`consensus_check(with_connectivity=…)`; `ws9_protocol.connectivity` moved to
`ws3_consensus.connectivity` (layer 3 may not import layer 9) and is re-exported (copy in
`ws6_certificates/amendments/FA-010_report_fork_details.md`). The contract files are queued for the one
Phase D seal; the owner signs with `./seal.sh`. The draft here stays as the record.
