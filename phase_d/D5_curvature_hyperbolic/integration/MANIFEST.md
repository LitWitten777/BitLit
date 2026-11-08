# D5 integration manifest

> **Applied 2026-10-04** without FA-020; `cell_complex.py` kept as a separate module (see `../STATUS.md`).

Apply after D3 and D6 (order D1 → D2 → D3 → D6 → D5 → D4). Rows marked
*needs FA-020* depend on the owner approving the amendment draft; the other
rows can be applied with or without it.

| Kind | Source | Destination | Action |
|---|---|---|---|
| new | `d5_curvature/hyperbolic.py` | `foundation/ws1_geometry/hyperbolic.py` | move (`TreeBall`, `TilingBall`, `edge_length`, `is_hyperbolic`); export from `ws1_geometry/__init__.py`. Depends only on `numpy`, which the foundation already requires |
| new | `d5_curvature/cell_complex.py`, `d5_curvature/curvature.py` | `foundation/ws1_geometry/curvature.py` | merge into one module (layer 1 imports nothing above `contracts`, so it stays a leaf) |
| new | `d5_curvature/product.py` | `foundation/ws1_geometry/product.py` | *without FA-020*: move as is (local `HAddress`/`HEdgeLabel` + adapter). *needs FA-020*: delete `HAddress`/`HEdgeLabel`, use `contracts.types.Address`/`EdgeLabel` directly, drop the adapter |
| new | `d5_curvature/capacity.py` | `foundation/ws7_benchmarks/capacity.py` | move; import paths `ws1_geometry.*` |
| new | `tests/test_d5_hyperbolic.py`, `tests/test_d5_curvature.py`, `tests/test_d5_product.py` | `foundation/tests/test_fnd_hyperbolic.py`, `test_fnd_curvature.py`, `test_fnd_product.py` | move; `d5_curvature.*` → `ws1_geometry.*` / `ws7_benchmarks.capacity` |
| patch | — | `foundation/ws1_geometry/PROPERTIES.md` | add rows P1.6 (P1.1–P1.5 for `TreeBall`/`TilingBall`) and P1.7 (P1.1–P1.4 for `ProductSpace`); executable form = the hyperbolic and product property tests above |
| new | `docs/CAPACITY.md` | `foundation/ws1_geometry/CAPACITY.md` | move; in `MASTER_PLAN.md` replace the qualitative "capacity (curvature)" remark by a pointer to it |
| amendment | `integration/amendments/FA-020_hyperbolic_factor.md` | `foundation/ws6_certificates/amendments/` | **owner decision**. If approved: apply to `contracts/types.py`, bump `INTERFACE_VERSION` 1.1.0 → 1.2.0 (shared with FA-010 if both are approved), history row in `INTERFACE_FREEZE.md`, the two consumer edits listed in the draft (`ws5_braid_ops/gate_action.py`, `ws9_protocol/network.py`), queue with `--amendment FA-020`, one `./seal.sh` |
| patch | — | `ws8_spec/LAYER_MAP.md` row 1 | add `hyperbolic`, `curvature`, `product` to "Exposes" |
| patch | — | `AGENT_WORKSTREAMS.md` backlog | "hyperbolic factor; learned curvature": hyperbolic factor and curvature done (numerical); learned curvature (Ricci flow) open |

**Registry.** Nothing is proved in Lean, so no H-rows are required. If the
owner wants the numerical claims tracked, H-090 – H-094 are reserved; suggested
rows (all mode "runtime-checked"):

* H-090 `κ_LLY(Q_n) = 2/n`, Forman (square complex) `= 2` — `test_hypercube_positive`.
* H-091 `κ_LLY(T^k_m) = 0` iff `m ≥ 6` (`3/(2k), 1/k, 1/(2k)` for `m = 3, 4, 5`); Forman `= 0` for `m ≥ 3` — `test_torus_zero_for_m_at_least_6_and_exceptions`.
* H-092 `{p,q}` interior: Forman `= 16 − 2p − 2q < 0`; `κ_LLY = c_p/q − 2 < 0` (observed) — `test_tiling_negative`.
* H-093 product: Forman local, `κ_LLY` scaled by `d_i/Σd_j` — `test_product_scaling_and_forman_locality`.

A natural Lean target (not attempted, Lean was out of scope for D5): the
Forman locality argument for products and the `16 − 2p − 2q` count are short
combinatorial statements; `κ_LLY(Q_n) = 2/n` needs a transport plan and a
1-Lipschitz dual witness and is harder.

> **Update 2026-10-04:** FA-020 approved; the *needs FA-020* rows were applied (contract types in
> `product.py`, `HAddress` alias kept). Interface 1.2.0 is queued for `./seal.sh`.
