# What the theorem engine actually uses, and what the repository merely contains

This note answers one question: of the files in this repository, which take part in a normal
run of the engine, and which do not?

"A normal run" is taken to be the end-to-end gate, `scripts/audit/run_all_checks.sh`, which is
the only entry point that exercises the whole system:

| step | command | what it reads |
| --- | --- | --- |
| 1 | `python3 scripts/gen_indices.py` | the Lean sources and the two library roots |
| 2 | `lake build` | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, every `.lean` under `Sovereign/` and `RequestProject/` |
| 3 | `lake env lean scripts/audit/TheoremAudit.lean` | the compiled environment of `Sovereign` and `RequestProject` |
| 4 | `lake env lean scripts/audit/CensusVectors.lean` | `Sovereign.Combinatorics.TowerDegreeMomentsPolynomial` |
| 5 | `python3 tests/research/test_lean_python_agreement.py` | `artifacts/CENSUS_VECTORS.json`, `scripts/research/cd_kernel.py`, `src/sedenion/research/w1_census_moments.py` |
| 6 | `python3 scripts/research/run_all.py --engine python` | `scripts/research/{w3,w4,w5}_*.py`, `src/sedenion/research/w1_census_moments.py`, and `logs/research/w*.json` |

Everything below was derived mechanically: the Lean import closure from the two library roots,
the Python import closure from the three entry points above, and a search for the producer and
the consumer of every data file.

The repository tracks 831 files. **Roughly 300 of them take part in a run; the remaining ~530
are agent configuration, one-off outputs, superseded code, and documentation.**

---

## 1. Included in normal operation

### 1.1 Build configuration (3 files)

`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`.

Both Lake targets are declared with a glob (`Sovereign`, `Sovereign.*` and likewise for
`RequestProject`), so every `.lean` file under those directories is compiled whether or not
anything imports it. Section 3.1 explains why that mattered.

### 1.2 The formal libraries (259 modules)

`Sovereign.lean` and `RequestProject.lean`, plus 240 modules under `Sovereign/` and 17 under
`RequestProject/`. **All 259 are compiled, and — after the change described in §3.1 — all 259
are reachable from a library root and therefore audited.** The audit now covers 3328
hand-written theorems (previously 3292), with 0 `sorry` and 0 non-standard axioms.

### 1.3 The audit and the gate (4 files)

- `scripts/audit/run_all_checks.sh` — the entry point above.
- `scripts/audit/TheoremAudit.lean` — the environment-level audit; writes `artifacts/THEOREM_AUDIT.json`.
- `scripts/audit/CensusVectors.lean` — exports ground truth from the Lean definitions; writes `artifacts/CENSUS_VECTORS.json`.
- `scripts/gen_indices.py` — the index closure check (new; see §3.1).

### 1.4 The computational side (7 files)

- `scripts/research/run_all.py` — the workstream driver.
- `src/sedenion/research/w1_census_moments.py` — W1, the only workstream still computed from `src/`.
- `src/sedenion/research/__init__.py` — package marker; needed for the import above.
- `scripts/research/w3_prefix_classes.py`, `w4_graph_counts.py`, `w5_sector_spectra.py` — W3, W4, W5.
- `scripts/research/cd_kernel.py` — the census kernel compared against Lean.
- `tests/research/test_lean_python_agreement.py` — the Lean/Python differential test.

That is the complete Python import closure. **Four of the twenty-six workstreams are computed;
the other twenty-two are replayed from `logs/research/w*.json` and reported as `CACHED`.**

### 1.5 Data the run reads or writes

- `logs/research/w2.json`, `w6.json` … `w26.json` (22 files) — **inputs**: the cached workstream
  results the driver replays. Deleting them does not fail the gate, it silently shrinks it.
- `logs/research/w1.json`, `w3.json`, `w4.json`, `w5.json`, `logs/research/RESULTS.md` — regenerated every run.
- `artifacts/THEOREM_AUDIT.json`, `artifacts/CENSUS_VECTORS.json` — regenerated every run.

---

## 2. Present, coherent, but outside a normal run

| path | files | status |
| --- | --- | --- |
| `haskell/` | 38 | A third implementation of the same kernels (34 modules, `sov-compute`). `run_all.py` **defaults** to `--engine haskell`, but the gate passes `--engine python`, and no Haskell toolchain is required or configured anywhere. Nothing compares it against Lean or Python, so it is the one engine with no differential test. |
| `src/sedenion/__init__.py` | 1 | A 482-line logging/verification framework. Its only importer is `tests/research/test_framework.py`; no workstream in the live path uses it. |
| `tests/research/test_framework.py` | 1 | A pytest suite for that framework. Not invoked by the gate, and `pytest` is not a runtime dependency. |
| `src/sedenion/research/roadmap.py`, `w2_sector_census.py` | 2 | Listed in the package `__all__`, imported by nothing. W2 is replayed from its log instead of being computed by `w2_sector_census.py`. |
| `docs/` | 17 | Documentation, including eight overlapping roadmap versions (`RESEARCH_ROADMAP_V2…V7`, `_NEXT`, plus the root `RESEARCH_ROADMAP.md` and `RESEARCH_COMPUTE_ROADMAP.md`). |
| `README.md`, `ORIGINAL_REQUEST.md`, `FILES_TOUCHED.md`, `ARISTOTLE_SUMMARY.md` | 4 | Provenance notes. |
| `pyproject.toml` | 1 | Packaging and lint configuration. Not read by the gate, and partly stale — see §4. |

---

## 3. Findings, and what was changed

### 3.1 Four modules were compiled but never audited (fixed)

`Sovereign/Combinatorics/Automaton.lean`, `Sovereign/Graph/RamanujanPhaseTransition.lean`,
`Sovereign/Graph/SpectralFieldStabilization.lean` and `Sovereign/Graph/ZeroDivisorFanoTopology.lean`
were compiled by the Lake glob but imported by no cluster index, so they were absent from the
environment `TheoremAudit.lean` elaborates against. Their 36 theorems were therefore never
checked for `sorry`, for non-standard axioms, or for vacuity, and they appeared in no report.
This is the failure mode the glob invites: adding a file makes it build, but only editing an
index makes it audited, and nothing enforced the second step.

They are now imported by `Sovereign/Combinatorics.lean` and `Sovereign/Graph.lean`, the audit
covers 3328 theorems instead of 3292, and it still reports 0 `sorry` and 0 non-standard axioms.

To keep the gap from reopening, `scripts/gen_indices.py` reports (with `--fix`, repairs) any
module that the glob compiles but no library root reaches, and it is now step 1 of
`scripts/audit/run_all_checks.sh`. This also supplies the script the `RequestProject.lean`
module docstring already referred to, which did not previously exist.

### 3.2 Unreachable research scripts (41 files)

Of the 42 Python files in `scripts/research/`, **37 are reachable from no entry point**, along
with `AudioVisualFunctor.hs` and three `.sage` files that no runner invokes. By theme:

- visualisation and "observatory" builders — `build_*.py` (6), `render_*.py` (5), `sedenion_render.py`, `live_dashboard.py`, `tetrachromatic_sedenion.py`, `synesthetic_octave_bridge.py`;
- Chladni figures — `chladni_exact.py`, `chladni_nodal.py`, `verify_chladni_svg.py`, `falsify_svg.py`;
- adversarial probes — `adversarial_attack.py`, `attack.py`, `attack_loops.py`, `attack_res.py`;
- IPC/bridges — `shm_reader.py`, `shm_ws_bridge.py`, `signal_harmonic_bridge.py`, `stiefel_discrete_continuous_bridge.py`, `cross_language_certificate.py`;
- one-off censuses and utilities — `spectral_triple_moduli_census.py`, `glueball_branching.py`, `stiefel_directions_b_to_e.py`, `automated_z3_refactor.py`, `benchmark_simulation_precision.py`, `cd_algebra.py`;
- tests filed outside `tests/` — `test_cd_np.py`, `audio_visual_functor_test.py` (never collected, since `pyproject.toml` sets `testpaths = ["tests"]`);
- `zero_token_theorem_auditor.py` — deliberately retained, with a header marking it superseded by `scripts/audit/TheoremAudit.lean`.

`cd_algebra.py` is a second Cayley–Dickson kernel, distinct from the audited `cd_kernel.py` and
compared against nothing; it is the same drift risk that `cd_kernel.py` already demonstrated.

Recommendation: keep `zero_token_theorem_auditor.py` (its header is the explanation of why the
audit moved into Lean); move the rest to a clearly-marked `scripts/attic/` or delete it, and
either wire `cd_algebra.py` into the differential test or remove it.

### 3.3 `artifacts/` is 3.1 MB, of which the run regenerates two files

26 files. `THEOREM_AUDIT.json` and `CENSUS_VECTORS.json` are live. The rest are one-off outputs:
`sedenion_voxels/` (11 HTML/PNG files plus 616 KB of vendored `three.min.js` and
`OrbitControls.js`), three Chladni SVGs, and `ZERO_TOKEN_THEOREM_AUDIT_REPORT.json`, the output
of the superseded auditor.

Five artifacts have **no producer anywhere in the repository** and cannot be regenerated:
`partition_function_results.json`, `commutant_certificates.json` (only loosely related to
`spectral_triple_moduli_census.py`), `falsification_report.txt`, `grand_tour_multimodal.html`,
`universal_harmonic_webgpu_explorer.html`, and `sovereign_esp32_harmonic_deck.ino`. An artifact
no script can rebuild is not evidence of anything; these should be deleted or given a generator.

### 3.4 A stale duplicate of the workstream logs inside the Lean tree

`Sovereign/research/` holds `RESULTS.md` and `w1.json`–`w5.json` — a second, divergent copy of
the workstream output (a different JSON schema from `logs/research/`, e.g. W1 keyed `M0`, `M1`,
… rather than by workstream metadata). Nothing reads it, and it sits inside the Lean library
directory where a reader will mistake it for current. Delete it, or regenerate it into
`logs/research/`.

Relatedly, `docs/roadmap_complete.json` and `src/docs/roadmap_complete.json` are two copies of
the same report with different contents, both written by the never-executed `roadmap.py`.

### 3.5 Generated caches were tracked in git (fixed)

`scripts/research/__pycache__/` (4 `.pyc`), `src/sedenion/__pycache__/` (1 `.pyc`) and
`src/sedenion.egg-info/` (6 files) were committed. They are now untracked and `.gitignore`
covers `__pycache__/`, `*.py[cod]` and `*.egg-info/`.

### 3.6 `.agents/` is 388 of the 831 tracked files

2.2 MB of assistant configuration (rules, skills, workflows, agent definitions) and
`ecc-install-state.json`. Nothing in the build, the audit or the workstreams reads any of it.
It is nearly half the repository by file count and is unrelated to the engine.

---

## 4. Smaller inconsistencies worth fixing

- `pyproject.toml` declares the console scripts `sedenion = "sedenion.cli:main"` and
  `sedenion-repl = "sedenion.cli:main"`, but there is no `src/sedenion/cli.py`; an install
  produces two entry points that fail on invocation.
- `pyproject.toml` sets `readme = "README_VERIFIED.md"`, a file that does not exist, and lists
  heavy optional dependencies (`torch`, `gudhi`, `z3-solver`, `stim`) that no reachable code
  imports. The runtime dependency list (`numpy`, `networkx`, `sympy`, `scipy`, `rich`, `stim`)
  is also wider than the live path, which imports none of them.
- `run_all.py` defaults to `--engine haskell`, a path that cannot succeed without a Haskell
  toolchain; the gate works only because it passes `--engine python` explicitly. The default
  should be the engine that is actually tested.
- The Haskell engine writes into the same `logs/research/` directory that the Python driver
  replays its cached workstreams from, in a different schema. Running the two engines in
  sequence would silently mix their outputs.

---

## 5. Summary

| category | files | in a normal run? |
| --- | --- | --- |
| build configuration | 3 | yes |
| Lean modules | 259 | yes — compiled and, as of this change, all audited |
| audit and gate scripts | 4 | yes |
| live Python (driver, W1/W3/W4/W5, kernel, differential test) | 7 | yes |
| workstream logs replayed as input | 22 | yes, as input |
| outputs regenerated each run | 7 | yes, as output |
| Haskell engine | 38 | no |
| unreachable research scripts | 41 | no |
| one-off artifacts | 24 | no |
| stale duplicate logs and reports (`Sovereign/research/`, the two `roadmap_complete.json`) | 8 | no |
| documentation and provenance | 22 | no |
| `.agents/` | 388 | no |
