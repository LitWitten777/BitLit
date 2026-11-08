# Phase D — Multi-agent plan (6 parallel workstreams)

> **Status (2026-10-04): closed, pending the owner's signature.** All six workstreams are
> integrated (D2 had no remaining target); every manifest is fully applied, including D6's
> `SU(2)_k` proposal; FA-010 and FA-020 are approved and applied (interface 1.2.0, queued). The
> only open action is one `./seal.sh` run by the owner. D3's presentation of `B_n(T²)` has been
> compared with Bellingeri's paper (Theorem 1.2) and matches it; the match is also proved in Lean
> (`QBX/Formal/TorusBraidBellingeri.lean`, H-119; see `D3_torus_braids/STATUS.md`). Log: `QBX/docs/foundation/PHASE_D_INTEGRATION_LOG.md`.

This folder is the work area for Phase D. Each workstream has one folder and
one agent. **Agents write only inside their own folder**; integration into the
main tree is a separate step done afterwards (`INTEGRATION.md`). Because no two
agents can touch the same file, the six branches merge without conflicts.

Read first: `../PREFLIGHT_RESPONSE.md` (what was fixed before Phase D and why
the plan below differs from the pre-flight proposal).

## The Phase D goal (the falsifiable deliverable)

Phase D is done when all four hold:

1. **Protocol.** An end-to-end consensus protocol runs on a simulated network
   of at least 100 nodes. Planted forks — a single changed event, an
   equivocation (two conflicting events on one transition), and coordinated
   forks touching fewer than λ events, where λ is the edge connectivity of the
   event graph — are detected and localized by `consensus_check` alone (no
   quorum, no fork-choice rule) in every trial, with no false alarms on honest
   runs. The report lists its blind spots, and the protocol's witness rule makes
   the event graph 2-edge-connected, so there are none. (D4) — **met**
   (`ws9_protocol/docs/REPORT.md`, integrated 2026-10-04 as layer 9: 1000
   trials per scenario on 100 nodes; 100% detection and localization of single
   forks and equivocations, 100% detection of forks on fewer than λ pairs, 0
   false alarms in 3000 honest runs, `blind_spots == []` in every witness-rule
   run; witness-rule proof in `ws9_protocol/docs/WITNESS.md`).
2. **Soundness proof — met.** Lean proves that detection is sound on
   2-edge-connected event graphs. More generally, on a `k`-edge-connected graph
   every fork touching fewer than `k` edges is detected, and the bound is
   exact: an undetectable fork exists on every edge cut.
   (`QBX/Formal/MultiEdgeFork.lean`, H-075, proved before Phase D.)
3. **Four logical sectors — met.** Lean proves the toric-code rank `2m² − 2`
   and ground-space dimension 4 for every `m ≥ 1` (T3), and the independence of
   the four logicals modulo stabilizers. (`QBX/Formal/ToricRank.lean`, H-102,
   SPEC T3a–T3d; proved by work stream WS4 and integrated 2026-10-04, so D2 has
   no remaining target.)
4. **Integrated.** After integration `./health.sh` is green, and any approved
   contract amendments are sealed with one `./seal.sh` run. — D1 and D4 integrated
   2026-10-04 with `./health.sh` green (log:
   `QBX/docs/foundation/PHASE_D_INTEGRATION_LOG.md`), followed the same day by
   D3, D6 and D5. The amendment drafts — D4's optional FA-010 and D5's FA-020 —
   were approved by the owner on 2026-10-04 and applied together with the WS9
   amendments FA-050 – FA-053 (interface 1.2.0); the contract files are queued,
   and the single Phase D seal is the owner's `./seal.sh` run. — **met except the
   signature**: `./health.sh` is green apart from `frozen` and the three
   signature tests, which turn green when the owner seals.

D3, D5 and D6 extend the foundation and are not part of this gate. All three
handed off and were integrated on 2026-10-04 (D3 → D6 → D5): D3 →
`QBX/Formal/TorusBraid.lean` (H-085, SPEC TB1–TB4) and
`ws5_braid_ops/torus_braid_full/`; D6 → `ws4_toric/surface_code.py` and (closing run)
`QBX/src/qbx_ir/anyon/{su2k,coherence}.py` (`su2k_model`); D5 →
`ws1_geometry/{hyperbolic,cell_complex,curvature,product}.py`,
`ws7_benchmarks/capacity.py`. The integrated code now exists only at its
destination; each folder keeps its brief, `STATUS.md` and manifest as the
record.

## Workstreams

| ID | Folder | Mandate | Kind | Priority |
|---|---|---|---|---|
| D1 | `D1_fork_theory/` | Equivocation on multigraph ledgers (F6–F6c and geodesic convexity of `Q_n ⊂ T^n_m` already proved) | Lean | supporting |
| D2 | `D2_toric_geometry_formal/` | ~~T3 toric rank `2m² − 2` / 4 sectors~~ — **closed**: T3 proved by WS4 (`QBX/Formal/ToricRank.lean`, H-102) | Lean | closed |
| D3 | `D3_torus_braids/` | Full `B_n(T²)` presentation; shadow homomorphism well-defined (Python + Lean) | research | extension |
| D4 | `D4_consensus_protocol/` | 100-node end-to-end protocol, witness rule, fork scenarios, λ, attack catalogue | Python | **critical** |
| D5 | `D5_curvature_hyperbolic/` | Hyperbolic factor `ℍ^j`, graph curvature, capacity table (contract amendment draft) | Python | extension |
| D6 | `D6_codes_anyons/` | Genus-`g` surface codes, `SU(2)_k` anyon data | Python | extension |

**Running fewer than six agents:** drop D6 first, then D5, then D3, then D1.
D4 carries the remaining gate item (D2's target T3 is already proved).

### Why six workstreams, and why these

* **The pre-flight work is done.** The infrastructure the pre-flight proposed
  as standing agents (G4 integration and CI, G5 benchmarks and property tests,
  G6 seal automation) was finished before Phase D: `health.sh`, the CI
  workflow, the pre-commit hook, the property tests, the scale benchmark and
  the seal-queue conflict rules. None of it needs a full-time agent.
  Integration happens after the agents finish, as a single step.
* **The work is split by the gate, not by the old layer map.** The open gate
  items (D2, D4) each get a dedicated agent, so no gate item waits behind an
  extension.
* **T3 gets a dedicated agent.** T3 is the hardest proof left in the plan (a
  rank computation over `ZMod 2` for every `m`). F6–F6c, originally D1's
  mandate, were proved before the run, so D1 takes the smaller formal items
  (equivocation, convexity) and D2 does T3 only.
* **Independent checking moves into D4.** D4 builds the protocol, and its
  attack catalogue tests `consensus_check` only through the frozen contract.
  Separately, the property tests already check every frozen promise
  independently of the implementation.
* **No "reserved" slots.** The pre-flight held G7–G8 in reserve. With
  folder-isolated parallel work there is nothing to wait for, so the Wave 2
  research items (D3, D5, D6) start now. The Wave 3 items are deferred (below).

### Mapping from the pre-flight waves

| Pre-flight item | Where it went |
|---|---|
| T3 in Lean | **proved** by WS4 (`QBX/Formal/ToricRank.lean`, H-102), integrated 2026-10-04 |
| Geodesic convexity | **proved** by WS1 (`QBX/Formal/MixedRadixGeometry.lean`, H-100), integrated 2026-10-04 |
| Multi-edge fork theorem | **proved** (`QBX/Formal/MultiEdgeFork.lean`, statement sharpened) |
| `blind_spots` amendment | done before Phase D (FA-001, folded into the first seal) |
| `is_flat` scale benchmark | done (`ws7_benchmarks/scale.py`; a quadratic slowdown was found and fixed) |
| Property tests per workstream | done (`tests/test_prop_*.py`, `ws*/PROPERTIES.md`) |
| Hyperbolic factor; learned curvature | D5 |
| Higher genus `Σ_g` | D6 (note: genus `g` gives `2g` logical qubits, i.e. `4^g` sectors, not `2g` sectors) |
| Full `B_n(T²)` | D3 |
| More modular tensor categories | D6 (`SU(2)_k`) |
| ZX-calculus layer, HoTT, MBQC, MERA, real PQ signatures | deferred to Phase E (see "Deferred") |

## Hard rules (every agent)

1. **Write only inside your folder** `phase_d/<ID>_*/`. Do not edit
   `contracts/`, any `ws*/` package, `tests/`, `examples/`, `QBX/Formal/`,
   `QBX/agents/**` (including `agents/memory/` and the freeze queue),
   `lakefile.toml`, `health.sh`, this file, `conftest.py` or `INTEGRATION.md`.
2. **To change an existing file, propose it.** Put the full new file, or a
   unified diff, under `<folder>/integration/` and list it in
   `<folder>/integration/MANIFEST.md`.
   Contract changes are amendment drafts
   (`integration/amendments/FA-NNN_<slug>.md`) using only your reserved IDs.
3. **Names are namespaced.** Your Python package is the one named in your
   README. Test files are `tests/test_<id>_*.py` (for example
   `test_d4_protocol.py`), so file names never collide. Lean files live in
   `<folder>/lean/`, import only `Mathlib` and `QBX.Formal.*` (never another
   Phase D file), start with `module`, and use the namespace stated in your
   README.
4. **Reserved IDs** (use only yours):

   | ID | Amendments | Hypothesis registry | Lean namespace |
   |---|---|---|---|
   | D1 | — | H-076 – H-079 | `QBX.Formal.Gauge`, `QBX.Formal.Gates` (new names only) |
   | D2 | — | H-080 – H-084 | `QBX.Formal.Toric` (new names only) |
   | D3 | FA-040 – FA-049 | H-085 – H-089 | `QBX.Formal.TorusBraid` |
   | D4 | FA-010 – FA-019 | — | — |
   | D5 | FA-020 – FA-029 | H-090 – H-094 | — |
   | D6 | FA-030 – FA-039 | H-095 – H-099 | — |

5. **Check before you hand off.** Run `./health.sh --fast` (from `QBX/`)
   before each commit, and the full `./health.sh` before handing off. It picks
   up your `tests/test_*.py` and `lean/*.lean` automatically. Lean files must
   contain no `sorry`, `admit` or `axiom`; the words are rejected even in
   comments.
6. **Respect the frozen contract.** Code against `contracts/` v1.1.0 only. If
   you need something it does not offer, build a local adapter inside your
   folder and draft an amendment.
7. **Report honestly.** Your `STATUS.md` states what is proved, what is only
   tested numerically, and what is open. Never present a numerical check as a
   proof.

## Standard folder layout

```
phase_d/<ID>_<name>/
  README.md          the brief (given; do not edit)
  STATUS.md          your progress and final report (create)
  <package>/         Python code (if any)
  tests/test_<id>_*.py
  lean/*.lean        Lean files (if any)
  docs/              notes, reports, derivations
  integration/
    MANIFEST.md      file → destination → action (new / replace / patch)
    amendments/      FA-NNN drafts (if any)
    patches/         diffs against existing files (if any)
```

`phase_d/conftest.py` puts every workstream folder on `sys.path`, so
`import d4_protocol` works from any test. The foundation packages
(`contracts`, `ws1_geometry`, …) are importable as usual.

## Starting an agent

Give each agent this prompt, with its ID filled in:

> You are workstream `<ID>` of QBX Phase D. Read
> `QBX/foundation/phase_d/README.md` (hard rules) and
> `QBX/foundation/phase_d/<ID>_*/README.md` (your brief), then do the work.
> Write only inside your folder. Run `QBX/health.sh` before handing off. Finish
> with an accurate `STATUS.md` and `integration/MANIFEST.md`.

## Deferred to Phase E (not assigned)

* **ZX-calculus layer.** It depends on the D6 code layer and on a decision
  about which ZX fragment to target.
* **HoTT / higher inductive types.** Lean 4 has definitional proof
  irrelevance and therefore uniqueness of identity proofs, which contradicts
  univalence. HoTT cannot be done inside this Lean project. The practical goal
  behind it, formalizing quotients natively, is already served by Lean's
  built-in `Quot`.
* **Measurement-based QC on the hypercube; MERA tensor networks.**
* **Real post-quantum signatures.** This matters for consensus: holonomy
  detects inconsistent *authenticated* events, while forged events are a
  separate threat. It should be the first Phase E item for the protocol.
