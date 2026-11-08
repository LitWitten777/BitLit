# D3 — Braid group of the torus `B_n(T²)` · research / extension

**Mission.** Replace the "permutation shadow only" placeholder
(`ws5_braid_ops.BRAID_FULL_TWIST_NOTE`) with a precise, cited presentation of
the torus braid group, a working implementation of its words, and a proved
homomorphism to the gate action already on the address space.

**Kind:** Python + Lean. **Python package:** `d3_torus_braid`.
**Lean namespace:** `QBX.Formal.TorusBraid`. **IDs:** FA-040 – FA-049,
H-085 – H-089.

## Read first (read-only)

* `foundation/ws5_braid_ops/` (`torus_braid.py`, `gate_action.py`, README) and
  `PROPERTIES.md` (P5.x).
* `QBX/Formal/HypercubeGates.lean` (B1–B3, `braidGate_mul`) and
  `QBX/Formal/Braid.lean` (how the project presents `B_n`).
* Standard sources for the presentation: Birman (1969), "On braid groups",
  and Bellingeri (2004), "On presentations of surface braid groups". Write the
  relations out in full with a citation, and check the conventions carefully.

## Deliverables

1. `docs/PRESENTATION.md`: generators (`σ_1…σ_{n−1}` plus the two torus
   loops `a, b` of one strand) and every relation, including the one that
   replaces the planar full twist. State the conventions (which strand, which
   orientation, left or right action) and how they match `braid_word_perm`.
2. `d3_torus_braid/`: words over the generators, free reduction, the relations
   as rewrite checks, and the **shadow** map
   `B_n(T²) → S_n ⋉ (Z²)ⁿ` (permutation of strands plus net winding of each
   strand around each torus cycle), together with its action on
   `Q_n □ T^k_m` through `ws5_braid_ops.Gate`.
3. Tests `tests/test_d3_*.py`: every relation maps to the identity under the
   shadow, and the shadow is a homomorphism on random words (hypothesis). Also
   show by example where the shadow loses information, as
   `BraidLayers.lean` does for the planar case.
4. **Lean:** define the group as a `PresentedGroup` and prove that the shadow
   map to `Equiv.Perm (Fin n) ⋉ (Fin n → ℤ × ℤ)` (or an equivalent concrete
   group) is a well-defined homomorphism, i.e. every relator maps to 1. Proving
   that the presentation *is* `π₁` of the configuration space is out of scope;
   cite it as background.
5. **(Stretch)** A finer, non-abelian invariant that sees the `[a,b]`-type
   relation, for example a representation into a finite group, verified
   numerically.

## Output layout

```
D3_torus_braids/
  d3_torus_braid/  tests/test_d3_*.py  lean/TorusBraid.lean  docs/PRESENTATION.md
  STATUS.md  integration/MANIFEST.md   → new module ws5_braid_ops/torus_braid_full.py (or keep as
                                          its own layer), QBX/Formal/TorusBraid.lean, SPEC.md rows
```

## Done when

The tests pass and the Lean file checks (both run by `health.sh`). The
presentation document cites its source. `STATUS.md` separates three kinds of
claim: proved in Lean, checked by tests, and taken from the literature.

## Out of scope

Link invariants, the configuration-space topology itself, and anyon
representations (D6).
