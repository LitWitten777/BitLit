# D3 — Status (2026-10-04)

All four deliverables and the stretch item are done. The three kinds of claim
are kept apart below.

## Proved in Lean (`lean/TorusBraid.lean`)

Namespace `QBX.Formal.TorusBraid`; imports only `QBX.Formal.HypercubeGates`.
Checked with `lake env lean` from the repository root: no errors, no
warnings, no `sorry`; `#print axioms` on the main results gives only
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Lean |
|---|---|
| `B_n(T²)` as a `PresentedGroup` (genus-1 Bellingeri relators) | `TorusBraidGroup`, `torusRels`, generators `tsigma`, `ta`, `tb` |
| the shadow `B_n(T²) →* S_n ⋉ (ℤ²)ⁿ` is a well-defined homomorphism (every relator ↦ 1) | `shadow_rels`, `shadow` (`Shadow n = Winding n ⋊[permAct n] Equiv.Perm (Fin n)`), `shadow_tsigma`, `shadow_ta`, `shadow_tb` |
| planar braids embed (as a homomorphism), and there the shadow is `permHom` with zero winding | `ofPlanar`, `shadow_comp_ofPlanar`, `shadow_ofPlanar` |
| the defining relations hold in the group | `tsigma_braid`, `tsigma_comm`, `ta_tb_loop` |
| total winding is a homomorphism `S_n ⋉ (ℤ²)ⁿ →* ℤ²` | `totalWinding` |
| action on `Q_n □ T^k_M` extending `braidGate` | `torusGate`, `torusGate_mul`, `torusGate_one`, `torusGate_ofPlanar`, `torusGate_ta`, `torusGate_tb` |
| a Heisenberg representation `B_n(T²) →* Heis(2n)` | `heis_rels`, `heisRep` |
| the shadow loses information: for `n ≥ 2`, `σ_i² ≠ 1` and `a b ≠ b a` though their shadows agree | `tsigma_sq_ne_one`, `shadow_tsigma_sq`, `ta_tb_ne`, `shadow_ta_tb`, `shadow_not_injective` |

## Checked by tests (`tests/test_d3_torus_braid.py`, 46 tests, about 4 s)

* every relator has trivial shadow and trivial Heisenberg image (`n = 1 … 8`);
* the shadow is a homomorphism on random words, respects free reduction and
  inverses, and is unchanged by inserting a relator (hypothesis, 200 examples
  each);
* the shadow product satisfies the group axioms on random elements;
* on planar words the shadow equals `ws5_braid_ops.braid_word_perm` with zero
  winding; `torus_gate` equals `ws5_braid_ops.braid_gate` there;
* `torus_gate` is an action (`compose`), and every relator acts trivially on
  every address of small spaces;
* where the shadow loses information (`σ_1²`, `[a, b]`, `σ_1` vs `σ_1⁻¹`);
* the abelianization of the presentation is `ℤ² ⊕ ℤ/2` for `n = 2 … 8` and
  `ℤ²` for `n = 1` (Smith normal form of the relation matrix).

A planted bug (dropping the permutation in the winding product) makes two
tests fail.

## Taken from the literature

* The presentation itself (Bellingeri 2004, Theorem 1.2, `g = 1`) and the fact
  that it presents `π₁` of the configuration space. The relations were first
  transcribed without the paper at hand; on 2026-10-04 they were compared line by
  line with the paper (arXiv v2, `QBX/docs/reference/`) and match it. Only the
  citation was wrong (Theorem 1.1, the punctured case, instead of Theorem 1.2).
  `QBX/Formal/TorusBraidBellingeri.lean` (H-119, SPEC TB5) writes Theorem 1.2 out
  for every genus and proves that at `g = 1` it presents the same group.
* The value `H₁(B_n(T²)) = ℤ² ⊕ ℤ/2` used as a sanity check. It is now proved for `n ≥ 2`
  (`abelianizationEquiv` in `QBX/Formal/TorusBraidLCS.lean`, H-120, SPEC TB6). The same file
  shows that `heisRep` is `B_n(T²)/Γ_3` for `n ≥ 3` and is the finest nilpotent invariant.
* For `n = 2`, `QBX/Formal/TorusBraidTwoStrand.lean` (H-121, SPEC TB8) gives a complete invariant:
  a 2-strand torus braid is determined by its image in `ℤ/2 ∗ ℤ/2 ∗ ℤ/2` and its total winding
  (Bellingeri–Godelle, Corollary 4.7).

## Open

* A faithful (or at least braid-detecting for all braids) representation, e.g.
  a torus analogue of Burau, is not attempted.
* Integration is proposed in `integration/MANIFEST.md`.

## Integrated (2026-10-04)

Applied as in `integration/MANIFEST.md`: `lean/TorusBraid.lean` → `QBX/Formal/TorusBraid.lean`
(unchanged apart from the header line; imported by `QBX/Formal.lean`; SPEC TB1–TB4, registry
H-085, 10 declarations added to the axiom audit); `d3_torus_braid/` →
`ws5_braid_ops/torus_braid_full/` (imports made relative); tests →
`foundation/tests/test_fnd_torus_braid.py`; `docs/PRESENTATION.md` →
`ws5_braid_ops/PRESENTATION.md`; `BRAID_FULL_TWIST_NOTE` now points to the new code. The
caveat about comparing the transcribed relations with Bellingeri (2004) was resolved later
the same day (see "Taken from the literature" above and `ws5_braid_ops/PRESENTATION.md`).
