# D6 — Higher-genus surface codes and `SU(2)_k` anyons (Python) · extension

**Mission.** Generalise the topological memory beyond the torus, and widen
the anyon library beyond Fibonacci and Ising.

**Kind:** Python. **Package:** `d6_codes`. **IDs:** FA-030 – FA-039,
H-095 – H-099.

## Read first (read-only)

* `foundation/ws4_toric/` (`ToricCode`, `PauliOp`, `commutes`, `gf2_rank`,
  `PROPERTIES.md` P4.x).
* `QBX/src/qbx_ir/anyon/model.py` (`AnyonModel`, Fibonacci, Ising) and
  `QBX/Formal/AnyonCoherence.lean` (pentagon and hexagon conventions:
  `F a b c d e f = [F^{abc}_d]_{ef}`).

## Deliverables

1. **Surface codes on `Σ_g`** (`d6_codes/surface_code.py`): the code on any
   cellulation of a closed orientable surface, given as vertices, edges and
   faces with incidence. Stars are X on the edges at a vertex, plaquettes are
   Z on the edges of a face. Constructions: the `4g`-gon with the standard
   identification `a₁b₁a₁⁻¹b₁⁻¹⋯`, refined (subdivided) so that it is a proper
   cell complex; and the `m × m` torus as `g = 1`, which must agree with
   `ToricCode(m)`.
2. **Counting** — check numerically that the stabilizer rank is
   `|V| − 1 + |F| − 1`, the number of logical qubits is `|E| − rank = 2g`, and
   the ground-space dimension is `2^{2g}` (= `4^g` sectors). Logical operators
   come from a homology basis (`2g` Z-type and `2g` X-type) with the
   symplectic pairing `δ_ij`. Correction to the backlog: genus `g` gives `2g`
   logical **qubits**, not `2g` sectors.
3. **Code distance** for small instances (minimum weight of a non-trivial
   logical, by exhaustive or BFS search on the cellulation), reported per
   genus and refinement.
4. **`SU(2)_k` anyons** (`d6_codes/su2k.py`): labels `0, ½, …, k/2`,
   truncated fusion rules, and F-symbols from quantum `6j` symbols at
   `q = e^{iπ/(k+2)}`, plus R-symbols. Check numerically that the pentagon and
   both hexagons hold for `k = 2…5`, using the conventions of `AnyonModel`.
   Cross-checks against the existing models:
   * `SU(2)_2` has Ising's fusion rules but is a different braided category.
     The topological spin of `½` is `e^{2πi·3/16}`, against `e^{2πi/16}` for
     Ising `σ`. Report which F- and R-data agree up to gauge and which do not.
   * The integer-spin part `{0, 1}` of `SU(2)_3` should match Fibonacci or its
     complex conjugate. Report which, and the gauge used.
5. Tests `tests/test_d6_*.py` (hypothesis where natural: random refinements,
   random label tuples).
6. `docs/LEAN_TARGETS.md`: proposed statements for a later formal run, for
   example the genus-`g` rank formula generalising T3, and pentagon/hexagon
   for `SU(2)_k` at specific `k`. Do not prove them here.

## Output layout

```
D6_codes_anyons/
  d6_codes/{surface_code,su2k}.py  tests/test_d6_*.py  docs/{RESULTS,LEAN_TARGETS}.md
  STATUS.md  integration/MANIFEST.md  → ws4_toric/surface_code.py (new),
                                         QBX/src/qbx_ir/anyon (proposal only: SU(2)_k models)
```

## Done when

* The genus `g = 1, 2, 3` counts match `2^{2g}`, and `g = 1` agrees with
  `ToricCode`.
* Pentagon and hexagon residuals for `SU(2)_k`, `k ≤ 5`, are below `1e-10`.
* All tests pass in under 60 s.

## Out of scope

The ZX-calculus layer (Phase E), Lean proofs, `SU(3)_k`, and decoders.
