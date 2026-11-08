# D5 — Hyperbolic factor and graph curvature (Python) · extension

**Mission.** Complete the "capacity ↔ curvature" row of the master plan:
add a negatively curved factor `ℍ^j` next to the flat torus and the hypercube,
and measure curvature on all three.

**Kind:** Python. **Package:** `d5_curvature`. **IDs:** FA-020 – FA-029,
H-090 – H-094.

## Read first (read-only)

* `foundation/MASTER_PLAN.md` (the claim: capacity comes from curvature),
  `foundation/ws1_geometry/` (`MixedRadixSpace`, routing, `PROPERTIES.md`).
* `foundation/contracts/types.py` and `interfaces.py`. **Constraint:** the
  frozen `Address` has only `bits` and `cycles`, and `EdgeLabel.kind` accepts
  only `"bit"` and `"cycle"`, so a hyperbolic coordinate does not fit without
  an amendment.

## Deliverables

1. **Discrete hyperbolic factor** (`d5_curvature/hyperbolic.py`): a finite
   ball of a hyperbolic graph. Recommended: the `{p,q}` tiling with
   `1/p + 1/q < 1/2` (e.g. `{7,3}` or `{5,4}`) grown to radius `R`; or, as the
   simplest case, the Cayley graph of a free group (a tree). Give exact
   distance and routing, plus ball and sphere sizes (exponential growth).
2. **Product space** (`d5_curvature/product.py`):
   `Q_n □ T^k_m □ ℍ^j_R` with the AddressSpace methods (`size`, `vertices`,
   `neighbors`, `step`, `distance`), using a local address type and adapter.
   Also an **amendment draft** `integration/amendments/FA-020_hyperbolic_factor.md`
   proposing the minimal contract change (for example an optional `hyper`
   field on `Address` and an `EdgeLabel` kind `"hyp"`), with backward
   compatibility and the effect on every consumer.
3. **Curvature** (`d5_curvature/curvature.py`): Ollivier–Ricci curvature of
   edges (exact optimal transport on small neighbourhoods, pure Python or
   `numpy`/`scipy` if available) and Forman curvature. Show the expected signs:
   positive on `Q_n`, zero on `T^k_m` for `m ≥ 5` (state the exact convention
   and any small-`m` exceptions you find), negative on the `{p,q}` tiling
   interior.
4. **Capacity table** (`docs/CAPACITY.md`): ball growth, diameter versus
   size, and curvature per factor and for products. This replaces the
   qualitative table in the master plan.
5. Tests `tests/test_d5_*.py`, including hypothesis properties mirroring WS1's
   P1.1–P1.4 for the hyperbolic factor and the product (metric axioms,
   shortest path, greedy routing).
6. **(Stretch) Learned curvature:** discrete Ricci flow on edge weights of a
   small event graph, documented as an experiment, not a claim.

## Output layout

```
D5_curvature_hyperbolic/
  d5_curvature/{hyperbolic,product,curvature}.py  tests/test_d5_*.py
  docs/CAPACITY.md  STATUS.md
  integration/MANIFEST.md + amendments/FA-020_hyperbolic_factor.md
                     → ws1_geometry/hyperbolic.py (new), contracts change only via FA-020
```

## Done when

The tests pass, the curvature signs are demonstrated with their exact
conventions, and the amendment draft is complete enough for the owner to
approve or reject.

## Out of scope

Editing `contracts/` (draft only); continuous hyperbolic geometry; Lean.
