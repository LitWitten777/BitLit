# D4 integration manifest

D4 proposes a new layer for the protocol rather than an extension of
`ws3_consensus` (the protocol imports layers 0–3 and nothing imports it).

| Kind | Source | Destination | Action |
|---|---|---|---|
| new | `d4_protocol/` (all modules) | `foundation/ws9_protocol/` | copy; rename the package to `ws9_protocol` (relative imports only, so only the directory name and the docstrings change); drop the `sys.path` fallback in `__init__.py` (the foundation root is on the path there) |
| new | `tests/test_d4_*.py` | `foundation/tests/test_fnd_protocol_*.py` | copy; replace `d4_protocol` by `ws9_protocol` |
| new | — | `foundation/ws9_protocol/PROPERTIES.md` + `foundation/tests/test_prop_protocol.py` | properties: (P9.1) witness-rule ledgers have `blind_spots == []`; (P9.2) the three λ methods agree; (P9.3) every scenario agrees with theory — the bodies of `test_d4_witness.py::test_random_runs_on_100_nodes_have_no_blind_spots`, `test_d4_connectivity.py::test_random_graphs_three_methods_agree`, `test_d4_scenarios.py::test_report_smoke` |
| patch | — | `ws8_spec/LAYER_MAP.md` | new row: layer `9 Protocol`, directory `ws9_protocol/`, imports from `0–3`, exposes `Network`, `run_with_witness`, `edge_connectivity`, `min_cut`, scenarios, report; formal counterparts F5, F6a–F6c, D1 E1–E6 (exercised by the scenarios) |
| patch | — | `tests/test_fnd_contracts.py` | `LAYERS["ws9_protocol"] = {"contracts", "ws1_geometry", "ws2_gauge", "ws3_consensus"}` (checked against the new LAYER_MAP row by `test_layer_map_matches_rule`) |
| new | `docs/REPORT.md`, `docs/ATTACKS.md`, `docs/WITNESS.md` | `foundation/ws9_protocol/docs/` | copy; regenerate `REPORT.md` with `python3 -m ws9_protocol 1000 --write` |
| amendment | `integration/amendments/FA-010_report_fork_details.md` | `ws6_certificates/amendments/` | optional; apply only if approved (one seal at the end of Phase D integration) |
| patch | — | `phase_d/README.md`, `MASTER_PLAN.md` | Phase D goal 1: evidence = `REPORT.md` (100 nodes; 100% detection of single forks, equivocations and forks on < λ pairs; 0% false alarms; `blind_spots == []`) |

`consensus_check` itself is unchanged.

> **Update 2026-10-04:** FA-010 approved and applied (interface 1.2.0, queued for `./seal.sh`).
