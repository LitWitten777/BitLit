# The equitable twin quotient `B_χ`: non-singularity in every dimension

Everything below is proved in Lean. There is no `sorry`, no `native_decide` and no finite
enumeration. `#print axioms` on the main theorems shows only `propext`, `Classical.choice` and
`Quot.sound`.

## Setting

We work at level `n ≥ 3`, so the algebra has dimension `Dₐ = 2ⁿ⁺¹ ≥ 16`. Fix a charge
`1 ≤ χ < 2ⁿ`.

- **Sector and adjacency matrix.** The charge-`χ` sector of the annihilation graph has
  `4 (2ⁿ − 2)` vertices, the sign-decorated cross-half vectors `±eᵢ ± e_{2ⁿ + (i ⊕ χ)}`
  (`card_sectorVertex`). Its adjacency matrix is `A_χ = sectorAdj n χ`, the existing definition
  in `Sovereign.Graph.SectorAdjacencyMatrix`.
- **Twin classes.** A class is written `(r, b)`:
  - `r` is a *representative cell*: a non-zero index whose bit at the leading position of `χ` is
    clear;
  - `b` is a parity bit.

  There are `2ⁿ − 2 = baseOrder Dₐ` classes (`card_twinClass_eq_baseOrder`).
- **The quotient matrix.** `B_χ = twinQuotient n χ` is a `{0,1}` matrix. Its entry at
  `(r, b), (r', b')` is `1` exactly when two conditions hold:
  - the cells `r` and `r'` interact (`cellAdj`);
  - `b ⊕ b'` equals the cell sign (`cellSgn`).

## Main theorems (`Sovereign/Graph/SectorTwinQuotientRank.lean`)

| statement | Lean name |
|---|---|
| `ker B_χ = {0}` | `twinQuotient_ker_eq_bot` |
| `det B_χ ≠ 0` | `twinQuotient_det_ne_zero` |
| `dim ker A_χ = 3 · baseOrder Dₐ` | `sectorAdj_nullity` |
| `dim ker A_χ = 3 (2ⁿ − 2)` | `sectorAdj_nullity_closed` |
| for `μ ≠ 0`: `μ ∈ spec A_χ ⇔ μ/4 ∈ spec B_χ` | `sectorAdj_nonzero_eigen_iff` |
| `λ ∈ spec B_χ ⇔ λ ≠ 0 ∧ 4λ ∈ spec A_χ` | `twinQuotient_eigen_iff` |
| `charpoly A_χ = X^{3(2ⁿ−2)} · charpoly (4 B_χ)` | `sectorAdj_charpoly` (in `SectorTwinQuotient.lean`) |

## Proof structure

1. **Cell signs** (`SectorCellSigns.lean`). The adjacency of two sector vertices depends on
   only two things (`crossAnnihilates_eq_cell`):
   - a cell adjacency bit and a cell sign bit, both built from the level-`n` signs `epsNeg n`;
   - the parities `s ⊕ t` of the two vertices' sign decorations.

   Replacing a cell `i` by its partner `i ⊕ χ` keeps the adjacency bit and flips the sign bit.
   Both bits are symmetric in the two cells.
2. **Twin factorization** (`SectorTwinQuotient.lean`). `A_χ = P B_χ Pᵀ`, where `P` is the
   class incidence matrix and `Pᵀ P = 4 · 1`. Each class has exactly four vertices; this is
   shown by an explicit bijection `SectorVertex ≃ TwinClass × Bool × Bool`. The characteristic
   polynomial identity, the eigenvalue correspondence and the formula `nullity = 3 · #classes`
   (which assumes `B_χ` is non-singular) all follow from this factorization.
3. **Splitting by parity** (`twinQuotient_mulVec_add` / `_sub`). `B_χ` is non-singular as soon
   as two matrices on representative cells are:
   - the signed cell matrix `S`;
   - the unsigned cell matrix `|S|`.
4. **Twin-star shape, uniformly in `n`** (`SectorCellStructure.lean`, `SectorCellStar.lean`).
   Take the universal cell `τ`:
   - `τ = 2ⁿ⁻¹` when `χ < 2ⁿ⁻¹`;
   - `τ = 1` when `χ = 2ⁿ⁻¹`;
   - `τ = χ ⊕ 2ⁿ⁻¹` otherwise.

   Then the cell graph on representatives has this shape:
   - `τ` is adjacent to every other representative;
   - every other representative `r` is adjacent to `r ⊕ τ`;
   - `r` and `r ⊕ τ` have the same remaining neighbours.

   The proof applies the Cayley–Dickson doubling recursion of `epsNeg` once. Everything then
   reduces to the commutation law and the cyclic law one level down.
5. **2-adic descent** (`TwinStarParity.lean`). Let `M` be a symmetric integer matrix with zero
   diagonal. Suppose that modulo 2 it has this twin-star shape, and that its order is
   `≡ 3 (mod 4)`. Then `M` is non-singular:
   - modulo 2, the kernel of `M` is spanned by the all-ones vector;
   - an odd kernel vector `x` would give `xᵀMx ≡ ∑ Mᵢⱼ ≡ 2 (mod 4)`, which is impossible;
   - so every integer kernel vector is even, and descent shows it is zero.

   Both `S` and `|S|` reduce modulo 2 to the same cell graph. There are `2ⁿ⁻¹ − 1 ≡ 3 (mod 4)`
   representatives because `n ≥ 3`.

## Remarks

- The modules `Sovereign.Graph.SectorTwinQuotient` and `Sovereign.Graph.SectorTwinQuotientRank`
  did not exist in the project before; they were created for this result. The earlier module
  `SectorTwinInterlacing` only contains arithmetic about `baseOrder` and is left unchanged.
- The nullity statement is about the real matrix `A_χ` acting on `SectorVertex n χ → ℝ`. The
  eigenvalue statements are about real eigenvectors. `B_χ` is symmetric
  (`twinQuotient_symm`).
