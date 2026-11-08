# D6 — Status (2026-10-04)

All six deliverables are in place. Nothing here is a Lean proof (Lean was out
of scope); every claim below is a numerical check by a named test. Results and
tables: `docs/RESULTS.md`; proposed formal statements: `docs/LEAN_TARGETS.md`.

## Done-when criteria

| Criterion | Status | Evidence |
|---|---|---|
| genus `g = 1, 2, 3` counts match `2^{2g}` | met | `test_counts_match_genus` (polygon, one and two barycentric subdivisions) |
| `g = 1` agrees with `ToricCode` | met | `test_genus_one_agrees_with_toric_code` (`m = 2 … 5`: identical stabilizer sets, rank `2m² − 2`, degeneracy 4, distance `m`) |
| pentagon and hexagons for `SU(2)_k`, `k ≤ 5`, below `1e-10` | met | `test_pentagon_hexagons_unitarity`: all residuals ≤ 1.3e−15, every label assignment |
| all tests under 60 s | met | 47 tests, about 5 s |

## Deliverables

1. `d6_codes/surface_code.py`: cellulations (`polygon_schema`, `barycentric`,
   `subdivide_edge`, `subdivide_face`, `torus_grid`), `SurfaceCode` with
   stabilizers as `ws4_toric.PauliOp`, ranks by `ws4_toric.gf2_rank`.
2. Counting: rank `|V| − 1 + |F| − 1`, `2g` logical qubits, `4^g` sectors;
   homology-basis logicals with pairing `δ_ij`.
3. Code distance (`z_distance`, `x_distance`, `brute_force_distance`), table in
   `docs/RESULTS.md`.
4. `d6_codes/su2k.py` + `d6_codes/coherence.py`: `SU(2)_k` data, residuals,
   gauge invariants (`topological_spins`, `fs_indicators`), `find_gauge`,
   adapter `from_anyon_model` for `qbx_ir.anyon.AnyonModel`.
   * `SU(2)_2` vs Ising: same fusion; `θ_{1/2} = e^{2πi·3/16}` vs
     `θ_σ = e^{2πi/16}`, Frobenius–Schur indicator `−1` vs `+1`; the `ψ` sector
     agrees; not gauge equivalent.
   * `SU(2)_3` integer part = **Fibonacci** (not its conjugate), gauge
     `u^{ττ}_τ = i`.
5. Tests: `tests/test_d6_surface_code.py` (hypothesis: random refinements),
   `tests/test_d6_su2k.py` (hypothesis: random label tuples).
6. `docs/LEAN_TARGETS.md`.

## Limits / open

* The distance search relies on the 3-path condition for homologically
  non-trivial cycles (standard); it is cross-checked by brute force only on
  small instances.
* No decoder (out of scope).
* `SU(2)_k` is proposed for `qbx_ir.anyon` only as a proposal
  (`integration/MANIFEST.md`); nothing under `QBX/src` was changed.

## Integrated (2026-10-04)

Applied as in `integration/MANIFEST.md`: `d6_codes/surface_code.py` → `ws4_toric/surface_code.py`
(exported from `ws4_toric`), tests → `foundation/tests/test_fnd_surface_code.py`,
`docs/RESULTS.md` §1 → `ws4_toric/SURFACE_CODES.md`, `docs/LEAN_TARGETS.md` →
`ws6_certificates/LEAN_TARGETS_D6.md`. Not moved (proposal only, destination outside the
foundation): `d6_codes/su2k.py`, `d6_codes/coherence.py` and `tests/test_d6_su2k.py`, which
keep running under the `phase_d` check of `health.sh`. The code distance `m` of the toric
code (the `g = 1` case of the distance table) is now also proved in Lean
(`QBX/Formal/ToricDistance.lean`, SPEC W6).

## Update (2026-10-04, closing run)

The `SU(2)_k` proposal was adopted (owner decision = recommendation): `d6_codes/su2k.py` and
`d6_codes/coherence.py` moved to `QBX/src/qbx_ir/anyon/su2k.py` and `coherence.py`, with
`su2k_model(k)` returning an `AnyonModel` (labels `"0"`, `"1/2"`, …) and exported from
`qbx_ir.anyon`; `tests/test_d6_su2k.py` moved to `QBX/tests/qbx_ir/test_anyon_su2k.py`. The D6
folder now holds only its record (brief, status, docs, manifest); nothing of D6 runs from
`phase_d/` any more.
