# D6 integration manifest

> **Applied 2026-10-04** except the `SU(2)_k` proposal row (see `../STATUS.md`).

| Kind | Source | Destination | Action |
|---|---|---|---|
| new | `d6_codes/surface_code.py` | `foundation/ws4_toric/surface_code.py` | move; change `from ws4_toric import …` to `from .toric_code import …`; export `Cellulation`, `SurfaceCode`, `polygon_schema`, `barycentric`, `subdivide_edge`, `subdivide_face`, `torus_grid` from `ws4_toric/__init__.py` (layer 4 still imports nothing else) |
| new | `tests/test_d6_surface_code.py` | `foundation/tests/test_fnd_surface_code.py` | move; `d6_codes` → `ws4_toric` |
| new | `docs/RESULTS.md` §1 | `foundation/ws4_toric/SURFACE_CODES.md` | move |
| proposal | `d6_codes/su2k.py`, `d6_codes/coherence.py` | `QBX/src/qbx_ir/anyon/su2k.py` (proposal only) | an `su2k_model(k)` returning an `AnyonModel` could be built from `SU2k(k).F_matrix` / `.R` with labels `"0"`, `"1/2"`, …; outside the foundation, so it is left to the owner. Until then the code stays in this folder (its tests keep running from `phase_d/`) |
| new | `docs/LEAN_TARGETS.md` | `foundation/ws6_certificates/LEAN_TARGETS_D6.md` | move (proposals for a later formal run) |
| patch | — | `ws8_spec/LAYER_MAP.md` row 4 | add `surface_code` to "Exposes" |
| patch | — | `AGENT_WORKSTREAMS.md` backlog rows 6–7 | done (numerical), with pointers |

No contract amendment. No registry rows (nothing proved in Lean); the claims
are numerical (mode V1/V2) and could be listed under "Runtime-checked" in
`QBX/Formal/HYPOTHESIS_REGISTRY.md` if the owner wants them tracked.

> **Update 2026-10-04:** the `SU(2)_k` proposal row was applied as well (`qbx_ir.anyon.su2k`,
> `su2k_model`; tests in `QBX/tests/qbx_ir/test_anyon_su2k.py`). The manifest is fully applied.
