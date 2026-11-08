# D2 — Toric code rank T3 (Lean) · closed

> **Status (2026-10-04): closed, no remaining target.** T3, T3a, T3b and T3c
> were proved for every `m ≥ 1` by work stream WS4 and integrated as
> `QBX/Formal/ToricRank.lean` (registry H-102, SPEC rows T3a–T3d; log
> `QBX/docs/foundation/WS4_LOG.md`). Do not re-declare those names. The
> registry IDs H-080 – H-084 stay reserved for D2 in case it is re-scoped.
> The brief below is kept as the record.

**Mission.** Close the numerically checked claim that is still open in Lean:
**T3**, the toric code on `T²_m` has stabilizer rank `2m² − 2`, so its ground
space has dimension 4 (the "4 logical sectors"). Geodesic convexity (G1) has
moved to D1, so this workstream is T3 only.

**Kind:** Lean only. **Namespaces:** `QBX.Formal.Toric`, `QBX.Formal.Gates`
(new names only). **Registry IDs:** H-080 – H-084.

## Read first (read-only)

* `QBX/Formal/ToricCode.lean`: edges `Bool × ZMod m × ZMod m`, `PauliOp` as
  two `ZMod 2` vectors, `symp`, `star`, `plaquette`, the logicals `ZA ZB XA XB`,
  and T1/T2.
* `foundation/ws4_toric/toric_code.py` (`stabilizer_rank`, `degeneracy`,
  `logicals_independent`) and `tests/test_prop_toric.py` (P4.4, the numerical
  check for m = 2…7).

## Deliverables

1. **T3a — X part.** Over `ZMod 2`, the span of the `m²` star X-supports has
   dimension `m² − 1`. The only relation is "the sum of all stars is 0", which
   is the kernel of the vertex–edge incidence map of the connected torus graph.
2. **T3b — Z part.** The span of the plaquette Z-supports has dimension
   `m² − 1` (the dual statement).
3. **T3 — stabilizer rank.** The stabilizer group has rank `2m² − 2`, so
   `2m² − rank = 2` logical qubits and ground-space dimension `2² = 4`. State
   it as the `finrank` of a `Submodule (ZMod 2)` of the symplectic space
   `(Edge m → ZMod 2) × (Edge m → ZMod 2)`, for every `m ≥ 2`.
4. **T3c — independence.** `ZA, ZB, XA, XB` are linearly independent modulo
   the stabilizer span. Hint: each anticommutes with exactly one of the others
   (T1), and the symplectic form vanishes on the stabilizer span.
5. `docs/SPEC_T3.md`: statements in words, Lean names, and the
   correspondence with `stabilizer_rank()` / `degeneracy()`.

**Suggested route for T3.** A useful general lemma: over a field, the
incidence (coboundary) map `F^V → F^E` of a connected finite graph has kernel
equal to the constants, so its rank is `|V| − 1`. Mathlib may already have
pieces of this (`SimpleGraph.incMatrix`, connectivity). Search before
building. Plaquettes are stars of the dual torus, which has the same shape,
so prove the X statement once and transport it.

## Output layout

```
D2_toric_geometry_formal/
  lean/ToricRank.lean            (module; imports QBX.Formal.ToricCode, Mathlib)
  docs/SPEC_T3.md
  STATUS.md
  integration/MANIFEST.md        → QBX/Formal/ToricRank.lean (new),
                                   QBX/Formal.lean import, SPEC.md T3 rows, registry H-080+ (patches)
```

## Done when

* The Lean file checks with `lake env lean` (run by `health.sh`), contain no
  `sorry`, and use only standard axioms.
* If T3 for all `m` is not finished, deliver whatever is proved (for example
  T3a alone, or the general incidence-rank lemma). Mark the rest open in
  `STATUS.md`. Do **not** substitute a `decide` check for small `m` as "T3";
  label such checks as instances.

## Out of scope

Higher genus (D6 computes it numerically and may propose a Lean target for
later); Python changes.
