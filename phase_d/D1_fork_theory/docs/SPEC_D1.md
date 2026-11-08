# D1 — Statements, Lean names, Python counterparts

File: `D1_fork_theory/lean/Equivocation.lean` (imports `QBX.Formal.GaugeFlatness`
only; namespace `QBX.Formal.Gauge`, all names new, under `EventLedger`). Checked
with `lake env lean`: no errors, no warnings, standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).

## Model

A ledger is `EventLedger V ι K`: a family of events `i : ι`, each with
`src i`, `dst i : V` and `transport i : K` (`K` a group). Several events may share
a pair of nodes, in either direction, and `src i = dst i` (a self-loop) is
allowed. This is exactly the input of `ws3_consensus.flatness.merge_events`.

A walk is a list of steps `(i, true)` (event `i` from `src i` to `dst i`, transport
`g_i`) or `(i, false)` (backwards, transport `g_i⁻¹`); `IsWalk u l v` says the steps
chain from `u` to `v`. `holonomy l` is the ordered product. The ledger is flat
(`IsFlat`) when every closed walk has trivial holonomy, which is the contract's
definition of `ConsensusReport.flat` ("every loop of the event graph, including the
2-cycles formed by two events on the same pair").

`graph` is the merged simple graph (`u ~ v` iff `u ≠ v` and some event joins
them). `Represents c` says the merged connection `c` takes each pair's transport
from *some* event on that pair, oriented accordingly; `merge_events` takes the
first event seen, which is one such choice.

## Statements

| ID | Lean | Statement | Python counterpart |
|---|---|---|---|
| E1 | `EventLedger.not_isFlat_of_equivocation` | two events `a → b` with `g₁ ≠ g₂` form the 2-cycle `[(i,true),(j,false)]` with holonomy `g₁ g₂⁻¹ ≠ 1`, so the ledger is not flat | `merge_events` reports `((a, b), h · g⁻¹)` |
| E1' | `EventLedger.not_isFlat_of_equivocation_rev` | events `a → b` and `b → a` with `g₁ ≠ g₂⁻¹` form a 2-cycle with holonomy `g₁ g₂ ≠ 1` | `merge_events` orients the later event (`g_ab = inverse(g)`) |
| E1'' | `EventLedger.IsFlat.parallelAgree`, `EventLedger.IsFlat.loopsTrivial` | a flat ledger has agreeing parallel events and trivial self-loops | — |
| E2 | `EventLedger.isFlat_iff` | for every `c` with `Represents c`: flat ⟺ self-loops trivial ∧ parallel events agree ∧ `c` flat | `consensus_check`: `flat = not (equivocations + non-trivial fundamental holonomies)`; self-loops are non-tree edges of the merged connection, so their holonomy is checked there |
| E2' | `EventLedger.exists_represents` | a representing merged connection always exists (so E2 is never vacuous) | the "first event" choice of `merge_events` |
| E3 | `EventLedger.isFlat_iff_isPureGauge` | a ledger is flat iff there are node potentials with `g_i = p(src i)⁻¹ p(dst i)` for every event | `is_pure_gauge` on the merged connection, plus agreement of all events |
| E4 | `EventLedger.not_isBridgeEvent_of_parallel` | an event sharing its pair with another event is not a bridge of the multigraph | `blind = [b for b in bridges(conn) if mult.get(b, 0) < 2]` |
| E5 | `EventLedger.isBridgeEvent_iff` | an event is a bridge of the multigraph (no walk from `src` to `dst` avoids it) iff its pair is a bridge of the merged graph and carries no other event | `report.blind_spots` (correctness of the whole filter) |
| E6 | `EventLedger.perturb_detected_iff_not_isBridgeEvent` | F5 for multigraph ledgers: for a flat ledger and `k ≠ 1`, changing event `i` to `g_i · k` is detected iff `i` is not a bridge of the multigraph | `build_forked_events` on a ledger with parallel events |

Notes.

* "All parallel events agree" (`ParallelAgree`) compares every pair of events.
  `merge_events` compares each later event with the first one only; by
  transitivity of equality the two conditions are the same, so the Python check is
  complete as well as sound.
* Self-loops: `GaugeFlatness.lean` works on a `SimpleGraph`, which has no loops
  (open item 4 of WS2). Here self-loops are part of the model: E2 shows the
  Python treatment (a self-loop is a fork iff its transport is not the identity)
  is correct, and E5 shows they are never blind spots.
* The proofs reduce to `GaugeFlatness.lean` (F1, F5) through two walk-transfer
  lemmas: every ledger walk maps to a merged-graph walk with the same holonomy
  (given E2's right-hand side), and every merged-graph walk lifts to a ledger walk
  with the same holonomy (given `Represents`).

## G1 — geodesic convexity (cited, not re-proved)

Proved by WS1 for every `m` in `QBX/Formal/MixedRadixGeometry.lean`
(`torus_dist_embedBits`, `embedBits_geodesicallyConvex`; registry H-100, SPEC G1).
As the brief instructs, D1 does not re-declare these names, so there is no
`HypercubeConvex.lean`.

## Numerical cross-check (not a proof)

`tests/test_d1_equivocation.py` compares `consensus_check` with definition-level
computations on random ledgers with parallel events and self-loops (`S₃`, `Z/5`):
flat ⟺ potentials exist over events (E3); flat ⟺ loops ∧ parallel ∧ merged flat
(E2); `blind_spots` = pairs of bridge events found by deleting each event (E5);
single-event fork detected ⟺ not a bridge event (E6). A planted bug (dropping the
`mult < 2` filter) makes three of the tests fail.
