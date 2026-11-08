# D3 integration manifest

> **Applied 2026-10-04** (see `../STATUS.md`).

| Kind | Source | Destination | Action |
|---|---|---|---|
| new | `lean/TorusBraid.lean` | `QBX/Formal/TorusBraid.lean` | move unchanged; add `public import QBX.Formal.TorusBraid` to `QBX/Formal.lean`; `lake build QBXFormal` |
| new | `d3_torus_braid/` | `foundation/ws5_braid_ops/torus_braid_full/` (subpackage) | move; it imports only `ws5_braid_ops` (and nothing from layers other than 0 and 5), so layer 5's import rule is unchanged; change `from ws5_braid_ops import …` to relative imports |
| new | `tests/test_d3_torus_braid.py` | `foundation/tests/test_fnd_torus_braid.py` | move; `d3_torus_braid` → `ws5_braid_ops.torus_braid_full` |
| new | `docs/PRESENTATION.md` | `foundation/ws5_braid_ops/PRESENTATION.md` | move |
| patch | — | `ws5_braid_ops/torus_braid.py` | replace the "Not implemented" text of `BRAID_FULL_TWIST_NOTE` by a pointer to `torus_braid_full` and `QBX/Formal/TorusBraid.lean` (keep the constant, it is exported) |
| patch | — | `ws6_certificates/SPEC.md` | new section "Torus braid group — `QBX/Formal/TorusBraid.lean` (registry H-085)" with rows TB1–TB4: TB1 `shadow_rels`/`shadow` (shadow well defined); TB2 `shadow_ofPlanar` (planar braids: `permHom`, zero winding); TB3 `torusGate_mul`, `torusGate_one`, `torusGate_ofPlanar` (action on `Q_n □ T^k` extending `braidGate`); TB4 `heis_rels`, `tsigma_sq_ne_one`, `ta_tb_ne`, `shadow_not_injective` (what the shadow forgets) |
| patch | — | `ws6_certificates/audit/AxiomAudit.lean` | `import QBX.Formal.TorusBraid`; `#print axioms` for the TB1–TB4 declarations |
| patch | — | `QBX/Formal/HYPOTHESIS_REGISTRY.md` | row H-085 (TB1–TB4); the presentation itself stays a literature citation (Bellingeri 2004), not a registry claim |
| patch | — | `QBX/README.md` formal-layer table, `ws8_spec/LAYER_MAP.md` row 5 formal counterpart | `TorusBraid.lean` |

No contract amendment.
