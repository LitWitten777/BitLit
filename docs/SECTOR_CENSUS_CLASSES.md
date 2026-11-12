# The charge-sector census: closed form, classes, and where it leads

This note records the result of the current pass — *skeletonise, formalise, verify, optimise*
— on workstream **W2** of `RESEARCH_COMPUTE_ROADMAP.md` (the census of a single charge
sector), and the threads it opens.  Everything called a theorem below is a Lean 4 theorem
that `lake build` accepts with no `sorry` and with the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## 1. What was open

`Sovereign/Combinatorics/TowerSectorCensus.lean` had the three *descent laws* of the sector
census `sectorCount n χ v` — the number of ordered admissible index pairs of charge
`χ = i ^^^ j` and degree `v` in the annihilation graph of dimension `2ⁿ`:

* low charge (`0 < χ < 2ᵐ`): the degrees double, `v ↦ 2v + 4`, and two degenerate pairs are
  added at the top degree;
* high charge (`χ = 2ᵐ + χ'`, `χ' ≠ 0`): the degrees are complemented,
  `v ↦ 2ᵐ⁺¹ - (2v + 4)`, plus two pairs at the top degree;
* power-of-two charge: the whole sector collapses onto the top degree.

Each law only speaks about the degrees the descent *hits*.  The roadmap listed the closed
form, and the number of distinct sector censuses per dimension, as open.

## 2. What is now proved

**Determination.**  `sectorClosed n χ v`
(`Sovereign/Combinatorics/TowerSectorCensusClosedForm.lean`) is an explicit recursion on the
binary expansion of the charge, with the octonionic base `sectorClosed 3 χ v = 6` for `v = 4`
and `0` otherwise.  The theorem

```
sectorCount_eq_sectorClosed : 3 ≤ n → χ ≠ 0 → χ < 2 ^ n →
    sectorCount n χ v = sectorClosed n χ v
```

holds for **every** degree `v`, including all the degrees of multiplicity zero.  The missing
half of the descent is supplied by three vanishing laws, which express the arithmetic
separation of the two degree families of a doubling step: a low sector realises only degrees
`≡ 12 (mod 16)`, a high sector only degrees `≡ 4 (mod 16)` together with the top degree, and
a power-of-two charge only the top degree.

**Classes.**  Reading the descent as a word gives the `(n-3)`-bit key `sectorKey n χ`
(`Sovereign/Combinatorics/TowerSectorCensusClasses.lean`), and

* `sectorCount_congr_of_key` — charges with equal words have equal censuses;
* `sectorKey_eq_of_sectorClosed_eq` — equal censuses force equal words;
* `sectorRep n k` with `sectorKey_sectorRep` — every word is realised;
* `sector_census_card` — **in dimension `2ⁿ` the `2ⁿ - 1` charge sectors carry exactly
  `2^(n-3)` distinct degree censuses.**

**Top degree.**  `sectorCount_top_degenerate` and `sectorCount_top_generic`: the multiplicity
of the top degree `2ⁿ - 4` is the whole sector, `2ⁿ - 2`, when the charge is below `8` or a
power of two, and `2^(n - p + 1) - 2` when the highest set bit of the charge sits at level
`p` with `3 ≤ p < n`.

**Support size.**  `sectorCount_support_card`: the number of distinct degrees realised by a
sector is one more than the number of ones in its descent word — the degree-constant sectors
are the words `0`, and each high step of the descent contributes exactly one new degree.

**Regularity.**  `sector_degree_constant_iff`: a sector is degree-constant exactly when its
charge is below `8` or is a power of two.  This turns the "regular sector" criterion, which
the computations had only observed, into a theorem for every dimension.

## 3. The picture in dimension 64

Evaluating the proved closed form at the eight representatives `sectorRep 6 k`, `k < 8`
(degree ↦ multiplicity):

| word `k` | census |
| --- | --- |
| 0 | `60 ↦ 62` |
| 1 | `4 ↦ 60`, `60 ↦ 2` |
| 2 | `12 ↦ 56`, `60 ↦ 6` |
| 3 | `4 ↦ 4`, `52 ↦ 56`, `60 ↦ 2` |
| 4 | `28 ↦ 48`, `60 ↦ 14` |
| 5 | `4 ↦ 12`, `36 ↦ 48`, `60 ↦ 2` |
| 6 | `12 ↦ 8`, `44 ↦ 48`, `60 ↦ 6` |
| 7 | `4 ↦ 4`, `20 ↦ 48`, `52 ↦ 8`, `60 ↦ 2` |

Each row sums to `62 = 2⁶ - 2`, as `sectorPairs_card` requires, and the top-degree entries
`62, 2, 6, 2, 14, 2, 6, 2` are the values predicted by the top-degree law.

## 4. Where this leads

1. **A non-recursive multiplicity formula.**  The determination exhibits every sector census
   as one base contribution `2^(n-4) · c`, `c ∈ {12, 2}` (or `14` in the degenerate case),
   plus one contribution `2^(n-m)` for each level `m` of the descent, placed at a degree
   obtained from the level by a sequence of "append a bit / complement" steps.  Writing that
   placement as a bit formula would give the sector analogue of `censusClosedForm`, i.e.
   `sectorCount n χ (8t + 4)` read off directly from the binary expansions of `χ` and `t`.
2. **Sector spectra (W5).**  The exact class count says there are only `2^(n-3)` sectors to
   analyse spectrally in dimension `2ⁿ`, not `2ⁿ - 1`; and the regularity criterion
   identifies precisely which of them are regular, which is the hypothesis under which the
   twin-quotient spectral argument applies.
3. **Multiplicity profile.**  The support size is now exact (`sectorCount_support_card`);
   what remains on the same machinery is the list of multiplicities itself: the descent
   predicts that a sector's multiplicities are `2^(n-4) · c` with `c ∈ {12, 2, 14}` together
   with one `2^(n-m+1)` per high step at level `m`, and proving that as a closed formula
   would complete the profile.
