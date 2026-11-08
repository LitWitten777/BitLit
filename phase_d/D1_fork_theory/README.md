# D1 — Fork theory (Lean): equivocation and hypercube convexity · supporting

**Status of the original mandate: done before Phase D.** The multi-edge fork
theorem and the "sound on 2-edge-connected graphs" statement are proved in
`QBX/Formal/MultiEdgeFork.lean` (registry H-075; SPEC rows F6–F6c):

* `diffEdges_eq_levelCut`, `exists_flat_diffEdges_eq_levelCut` (F6, both
  directions);
* `not_isFlat_of_isEdgeConnected` (F6a);
* `perturb_detected_of_isEdgeConnected_two` (F6b);
* `exists_flat_diffEdges_eq_boundary` and
  `exists_undetectable_fork_of_not_isEdgeReachable` (F6c: the bound is exact).

Gate item 2 of `../README.md` is therefore met. D1 takes over two smaller
formal items, so that D2 can concentrate on T3.

**Kind:** Lean only. **Namespaces:** `QBX.Formal.Gauge`, `QBX.Formal.Gates`
(new names only). **Registry IDs:** H-076 – H-079.

## Read first (read-only)

* `QBX/Formal/GaugeFlatness.lean`, `QBX/Formal/MultiEdgeFork.lean`.
* `foundation/ws3_consensus/flatness.py` (`merge_events`: how the Python side
  treats several events on one pair of nodes).
* `QBX/Formal/HypercubeGates.lean` (`Addr`, `addrDist`) and
  `foundation/ws1_geometry/mixed_radix.py` (`distance`).

## Deliverables

1. **Equivocation (multigraph ledger).** Model a ledger as a family of events
   `ι → (src, dst, transport)`, i.e. a multigraph, and define flatness by
   closed walks over events. Prove three things:
   * two events on the same pair that disagree (after orientation) give a
     2-cycle with holonomy `g₁ g₂⁻¹ ≠ 1`, so the ledger is not flat;
   * a multigraph ledger is flat iff all parallel events agree **and** the
     merged simple-graph connection is flat. This is the correctness of
     `merge_events` + `consensus_check`;
   * a pair with at least two events is never a bridge of the multigraph, so
     it is not a blind spot.
2. **G1 — geodesic convexity** (moved from D2). **Done (integration note,
   2026-10-04):** proved by work stream 1 for every `m`, in
   `QBX/Formal/MixedRadixGeometry.lean` (`torus_dist_embedBits`,
   `embedBits_geodesicallyConvex`; registry H-100, SPEC G1). Cite it; do not
   re-prove it or re-declare its names in `QBX.Formal.Gates`. Original brief: For `m ≥ 3`, the torus
   distance restricted to `{0,1}^n ⊂ T^n_m` is the Hamming distance, and every
   shortest path in `T^n_m` between two points of `{0,1}^n` stays in
   `{0,1}^n`. Use the cycle metric `min(|x−y|, m−|x−y|)` per coordinate,
   matching `MixedRadixSpace.distance`, and tie it to `addrDist` if possible.
3. `docs/SPEC_D1.md`: statements in words, Lean names, and Python
   counterparts.

## Output layout

```
D1_fork_theory/
  lean/Equivocation.lean  lean/HypercubeConvex.lean  docs/SPEC_D1.md  STATUS.md
  integration/MANIFEST.md   → QBX/Formal/{Equivocation,HypercubeConvex}.lean (new),
                              QBX/Formal.lean imports, SPEC.md rows, registry H-076+ (patches)
```

## Done when

Both files check with `lake env lean` (run by `health.sh`), contain no
`sorry`, and use only standard axioms. Anything unfinished is marked open in
`STATUS.md`.
