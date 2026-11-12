# Review of the latest theorems, and the next highest-value targets

**Date.** 2026-09-22.
**Scope.** A read of the theorems added in the most recent passes — the workstreams W1–W5 of
`RESEARCH_COMPUTE_ROADMAP.md` and the three "T2" rows of its status table — followed by a
prioritised list of the targets that are now worth the most.  This document supersedes
nothing: `docs/RESEARCH_ROADMAP_NEXT.md` keeps the R1–R10 numbering of the previous survey,
and the targets below are numbered **T1–T9** to avoid any collision.

**The standard used.**  A line counts as *proved* only when a Lean theorem states it for every
dimension (or for every `k`, or every charge) — not for a tabulated list — and `lake build`
accepts the file with no `sorry` and only the standard kernel axioms.  A theorem whose
statement, read without its name and docstring, is an identity between defined constants is
recorded here as *bookkeeping*: true, useful as a regression test, but not the claim its name
makes.

**Build state at the time of writing.** `lake build` completes (8258 jobs, 0 errors, 0
warnings); no `sorry` occurs in any Lean declaration in the tree (the string occurs only in
docstrings and in the metaprogramming modules under `Sovereign/Meta/`, which manipulate it as
text).

---

## 1. Verdicts on the latest theorems

| module | what it really proves | verdict |
| --- | --- | --- |
| `Graph/CrossHalfVertexDegree` | `crossAnnihilates` is equivalent to annihilation in the algebra; the degree of each of the four vertices of a pair is `2 · towerDegree n i j`; the edge count `Dₐ³/4 − 28Dₐ + 96` | **general, content-bearing** — the model the rest of the library should follow |
| `Combinatorics/TowerSectorCensusClosedForm` | `sectorCount n χ v = sectorClosed n χ v` for every level, charge and degree | **general** |
| `Combinatorics/TowerSectorCensusClasses` | the census depends on the charge exactly through `sectorKey`; the `2ⁿ − 1` sectors carry exactly `2^(n−3)` distinct censuses | **general** |
| `Combinatorics/TowerSectorProfile` | the non-recursive profile agrees with the closed form — verified exhaustively in dimensions 16, 32, 64, 128 by kernel evaluation | **instance layer** (the module says so); *now subsumed*, see §2 |
| `Combinatorics/TowerDegreeMomentsUniform` | the doubling recurrence `censusMoment_succ` for **all** `k, q`; the odd/even kernel identities | **general** for the recurrence; the accompanying `vanishing_leading_coeff_k1_to_k5` is a finite check for `k ≤ 5` |
| `Combinatorics/PrefixDepthBijection` | `|prefixDepthPairs n k| = 2^(q−k) · censusInteriorVal q k`, quantified in `q, k` | **general**, though the argument is still a counting one: no explicit bijection is exhibited |
| `Graph/BaseGraphQuotient` | arithmetic identities between `baseOrder D = (D−4)/2`, `baseDegree D = (D−8)/4`, `sectorOrder`, `sectorZeroModes` | **bookkeeping**: no matrix, graph or partition occurs in any statement |
| `Graph/SectorTwinInterlacing` | the same arithmetic, plus two statements whose proofs are `h_rayleigh` and `linarith` | **bookkeeping, with two statements weaker than their docstrings**: `adjacency_spectral_radius_bound` has the conclusion `|λ| ≤ D − 8` *as its own hypothesis*, and `spectral_gap_from_degree_bounds` is announced as `λ₂/d ≤ 7/12` but concludes `0 < d_max` |
| `Graph/RegularSectorSpectrum` | genuine polynomial algebra: `pC6 = (X²−4)(X²−1)²`, `pQuot16 = (X²−64)(X²−16)²`, and that `X² + 4X − 224` has no integer root and real roots `−2 ± 2√57` | **true and non-trivial, but unattached**: nothing in the module ties these polynomials to the characteristic polynomial of any sector |
| `Algebra/SedenionAnomalyCancellation` | `annihilator_dim D := D/2 − 2` evaluated at seven dimensions; `chiral_index D = 0`, which holds by unfolding the definition | **bookkeeping** |
| `Quantum/ToroidalLatticeSurgery` | `graphBettiOne v e` evaluated at tabulated `(v, e)` | **bookkeeping** |
| `Physics/CosetHarmonicsGlueball` | identities and ratios between values of the defined function `stiefel_eigenvalue` | **bookkeeping** relative to its name; the mass-gap statement is a statement about that function, not about a Laplacian |

Two structural conclusions.

1. **The census thread is finished as a combinatorial object.**  With the closed form, the
   class theorem, and now the profile (§2), a sector census is a computable function of an
   `(n−3)`-bit word with no recursion left in it.  Everything still open on that thread is
   either a *corollary* (T4) or an *analytic* statement about the limit (T6).
2. **The spectral thread has no object.**  Five modules are named after adjacency matrices,
   quotients, interlacing and expander gaps; none of them contains a matrix.  The constants
   `7/12`, `5/12`, `5/24`, the "zero modes" and the "quotient order" are definitions, and the
   theorems relate them to each other.  This is the single largest gap in the project, and
   since the graph itself is already formalised — `crossAnnihilates` is decidable and proved
   equivalent to annihilation — it is a *reachable* gap.  T1 and T2 are that gap.

---

## 2. Shipped with this review

Two new modules, both building with no `sorry` and the standard kernel axioms only.

* `Sovereign/Combinatorics/TowerSectorProfileClosed.lean` — **closes item R1 / workstream W2**:

  ```lean
  theorem sectorCount_eq_sectorProfile (n chi v : Nat) (hn : 3 ≤ n) (hchi0 : chi ≠ 0)
      (hchi : chi < 2 ^ n) : sectorCount n chi v = sectorProfile n (sectorKey n chi) v
  ```

  for every level, charge and degree, where `sectorProfile` is the fold of affine descent
  steps over the bits of the word — no recursion on the census.  The proof shows the fold
  satisfies exactly the two descent laws of `sectorClosed` (`sectorProfile_succ_low`,
  `sectorProfile_succ_high`) together with the degenerate law `sectorProfile_key_zero`; the
  supporting invariant is `sectorPush_window`: a pushed degree stays inside `4 ≤ v ≤ 2ˡ − 4`
  and stays `≡ 4 (mod 8)`.  The previous instance layer (dimensions 16–128) is retained as a
  kernel-level cross-check.  Two corollaries are shipped with it — `sectorProfile_total` and
  `sectorCount_total_eq`: summed over all degrees, any descent word carries exactly `2ⁿ - 2`
  pairs, which is the first item of T4 below and a cross-check of `sectorPairs_card`.

* `Sovereign/Graph/AdjacencyEigenvalueBound.lean` — a *derived* spectral radius bound:

  ```lean
  theorem crossDegree_bounds … : 8 ≤ crossDegree n s t i j ∧ crossDegree n s t i j ≤ 2 ^ (n+1) - 8
  theorem eigenvalue_abs_le_row_absSum …          -- row-sum (Gershgorin-type) bound, from scratch
  theorem crossGraph_eigenvalue_abs_le …          -- |λ| ≤ Dₐ − 8 for the annihilation graph
  ```

  The last one says: any non-negative matrix whose row sums are the *proved* annihilation-graph
  vertex degrees has all real eigenvalues in `[−(Dₐ−8), Dₐ−8]`.  The constant comes from
  `towerDegree_bounds` through `crossDegree_eq_two_mul_towerDegree`, not from a table.  It is
  the honest replacement for `adjacency_spectral_radius_bound`.

* `Sovereign/Graph/CrossAdjacencyMatrix.lean` — **the adjacency matrix itself** (the first
  stage of T1 below):

  ```lean
  abbrev admVertex (n : Nat) : Type                     -- cross-half vertices, admissible pairs
  def    crossAdj  (n : Nat) : Matrix (admVertex n) (admVertex n) ℝ
  theorem crossAdj_entry       …  -- every entry is 0 or 1
  theorem crossAdj_rowSum_le   …  -- every row sum is at most crossDegree n s t i j
  theorem crossAdj_eigenvalue_abs_le (n : Nat) (hn : 3 ≤ n) (lam : ℝ) (x : admVertex n → ℝ)
      (hx : x ≠ 0) (heig : (crossAdj n).mulVec x = lam • x) : |lam| ≤ 2 ^ (n + 1) - 8
  ```

  The last statement is unconditional: every real eigenvalue of the annihilation-graph
  adjacency matrix of dimension `Dₐ = 2ⁿ⁺¹` lies in `[−(Dₐ−8), Dₐ−8]`, with the constant
  derived from the vertex-degree law rather than tabulated.  This is the first spectral
  theorem in the project that is about a matrix.

---

## 3. The next targets, in priority order

### T1. The sector adjacency matrix (the prerequisite of everything spectral)

**Where it stands (after this review).**  `Sovereign/Graph/CrossAdjacencyMatrix.lean` builds
the matrix `crossAdj n` of the whole annihilation graph, proves its entries are `0/1` and its
row sums bounded by the proved vertex degrees, and derives `|λ| ≤ Dₐ − 8` unconditionally.
What remains is the *charge-sector* refinement and the two structural lemmas:

```lean
theorem crossAdj_symm     (n) : (crossAdj n).IsSymm
theorem crossAdj_rowSum   (n p) : ∑ q, crossAdj n p q = (crossDegree n … : ℝ)   -- equality
def     sectorAdj (n chi : Nat) : Matrix (sectorVertex n chi) (sectorVertex n chi) ℝ
theorem sectorAdj_rowSum  (n chi p) : ∑ q, sectorAdj n chi p q = (crossDegree n … : ℝ)
```

Symmetry needs a symmetry lemma for `crossAnnihilates` (the annihilation relation is symmetric
in the algebra, so it should follow from `crossAnnihilates_iff` plus the corresponding fact
about the product); the row-sum *equality* needs the observation that every annihilating
partner of an admissible vertex is itself admissible.

**Why first.**  It is the object five modules are named after, and it is the only hypothesis
standing between the library and a *proved* spectral bound: feeding `sectorAdj_rowSum` into
`crossGraph_eigenvalue_abs_le` gives `|λ| ≤ Dₐ − 8` for the actual graph, in every dimension,
with nothing tabulated.  It also makes `Graph/AnnihilationGraph`'s vertex and edge counts
statements about a matrix rather than about numerals.

**Risk.** Low; the index type is now fixed (`admVertex n`, a subtype of
`Bool × Bool × Fin (2ⁿ) × Fin (2ⁿ)`), and the row-sum lemma is the public interface, so
downstream modules never unfold it.

### T2. The equitable twin quotient, as a theorem about characteristic polynomials

**Target.**

```lean
theorem sectorAdj_charpoly_eq (n chi : Nat) (hn : 3 ≤ n) :
    (sectorAdj n chi).charpoly = X ^ (3 * baseOrder (2 ^ (n+1))) * (4 • baseAdj n chi).charpoly
```

i.e. the four sign decorations of a pair are twins (equal neighbourhoods), the partition is
equitable, the non-zero spectrum is that of the `(D−4)/2`-row quotient, and the quotient is
`4 ·` a `{0,1}`-matrix.

**Why.**  This is what `BaseGraphQuotient` and `SectorTwinInterlacing` assert numerically;
with T1 in hand it converts every one of their arithmetic identities into a spectral theorem,
and it reduces all later spectral work from `(D−2)(D−4)` rows to `(D−4)/2`.

**Risk.** Highest on this list.  Mathlib has characteristic polynomials but not equitable
partitions; the twin part (rank-one blocks of equal rows ⇒ kernel vectors) is elementary and
should be proved first as `twin_rows_mem_ker`, which is already enough to give the zero-mode
count `3(D−4)/2` as a theorem about `sectorAdj` rather than about `sectorZeroModes`.

### T3. All higher moments, uniformly in `k` (old R2, still open)

**Target.** With `censusMoment` and the *proved* recurrence `censusMoment_succ`:

```lean
theorem censusMoment_poly (k : Nat) :
    ∃ p : Polynomial ℚ, p.natDegree = k + 2 ∧ p.coeff (k + 1) = 0 ∧
      ∀ q, (censusMoment k q : ℚ) = p.eval ((2 : ℚ) ^ (q + 3))
```

**Why.**  `M₁ … M₅` are five separate proofs today and `M₆` would be a sixth.  The recurrence
that makes them uniform is already a theorem; what is missing is the strong induction on `k`
that reads the binomial expansion of the doubling kernel as a triangular linear system for the
coefficient vector.  Medium effort, no missing mathematics, and it is the finite-`D` half of T6.

### T4. The corollaries the profile theorem now makes cheap

With `sectorCount_eq_sectorProfile` proved, each of the following is a short argument about the
word `w = sectorKey n χ` rather than a new induction:

* *(done, shipped with this review)* the **pair count** `∑_v sectorCount n χ v = 2ⁿ - 2`, read
  off the profile rather than off the pair enumeration (`sectorCount_total_eq`);
* the **multiplicity multiset** of a sector: `{6 · 2^(n−3)} ∪ {2^(n−3−t) : t < n−3}`, with the
  merges dictated by the coincidences among the pushed degrees;
* `sectorCount_support_card` in closed form — the number of *distinct* degrees in a sector as a
  function of `w`, hence a classification of the degenerate sectors that does not go through
  `exists_nontop_of_key_ne_zero`;
* the **per-sector handshake**: `∑_v v · sectorCount n χ v` as an explicit bit formula in `χ`,
  and with T1 the edge count of each sector graph;
* the **top-degree multiplicity** `2^(n−p+1) − 2` re-derived from the profile, which is a
  regression test against the existing `sectorCount_top_generic`.

**Why.**  These are the statements a reader of the census thread will ask for next, and they
are the natural regression tests of T1's row sums against `logs/research/w4.json`.

### T5. Retire, or prove, the tabulated spectral constants

Concretely, in `Graph/IrregularGraphSpectralBounds` and `Graph/SectorTwinInterlacing`:

1. restate `adjacency_spectral_radius_bound` as an instance of `crossAdj_eigenvalue_abs_le`
   (it then has content and its proof is one line) — now possible with no prerequisites;
2. correct `spectral_gap_from_degree_bounds`, whose conclusion (`0 < d_max`) does not match its
   docstring: either prove `λ₂ ≤ 7/12 · d` for the actual matrix (needs T1 + T2) or downgrade
   the docstring to what the statement says;
3. decide the fate of `7/12`, `5/12`, `5/24`: either derive them from the degree bounds
   `8 ≤ d ≤ D − 8` by interlacing on the quotient, or record them as *computed for `D ≤ 64`*
   and remove the claim that they hold in every dimension.

**Why.**  Every downstream expander/Cheeger/Ramanujan module reads these constants.  Until one
of the two branches is taken, those modules are named after properties that nothing in the tree
establishes.  This is the cheapest *credibility* gain available.

### T6. The limit law of the normalised degree (old R3)

**Target.** Derive `limitingMoment k` from the recursion of T3 and prove

```lean
theorem censusMoment_tendsto (k : Nat) :
    Filter.Tendsto (fun q => (censusMoment k q : ℝ) / (2 ^ (q + 3)) ^ (k + 2))
      Filter.atTop (nhds (limitingMoment k))
```

so that the nine constants `mu0 … mu8` of `Combinatorics/LimitingDegreeDistribution` become
corollaries, and then identify the limit measure: the descent is the iterated function system
`x ↦ x/2`, `x ↦ 1 − x/2` on the normalised degree `x = v/D`, plus the atom each doubling step
deposits at the top degree.  With the profile theorem the IFS is now *explicit* — the weights
are `6 · 2^(n−3)` and `2^(n−3−t)` — which is the piece that was missing when this was R3.

### T7. The `ℚ(√57)` factor, attached to the graph

`RegularSectorSpectrum` proves that `X² + 4X − 224` has discriminant `912 = 16 · 57`, no integer
root, and roots `−2 ± 2√57`.  The target is to prove that this polynomial *divides the
characteristic polynomial of the `D = 64` regular sector quotient* — i.e. the statement the
module is named for.  It needs T1 and T2 in dimension 64 only, so it is a good first consumer
of them and a sharp test that the quotient construction is correct.

### T8. A structural proof of the prefix-depth classes (old R5)

`prefixDepthPairs_card` is proved by counting.  The target is the map
`admissible pair ↦ level at which the descent of degreeClosed stops`, a proof that it computes
`pairPrefixDepth`, and the class decomposition transported along it.  Value: it is the last
member of the census family whose proof does not follow the structure of the object, and the
map is what a combinatorial model of the graph would be built on.

### T9. Reproducibility of the logged computations (old R7)

`logs/research/` holds verdicts for workstreams that no script in the tree regenerates.  The
target is unchanged: either restore the generators or regenerate the logs from the scripts that
exist, and add a check that every numeric constant asserted in a Lean file and also present in
a log agrees with it.  Low mathematical content; it is what makes the logs evidence rather than
assertion.

---

## 4. Suggested sequencing

```
T1 ──► T2 ──► T5 (2,3) ──► T7
 │       └──► T4 (sector edge counts)
 └────► T5 (1)

T3 ──► T6
T4, T8, T9 independent
```

`T1 + T3` is a good next sprint: both are self-contained, both have their evidence in hand
(`w4.json`, `w1.json`), and together they unlock the entire spectral programme and the limit
law.  `T5 (1)` is an hour's work once T1 exists and removes the most misleading statement in
the tree.

## 5. Definition of done (restated)

1. The statement quantifies over the dimension, or over `k`, or over the charge — not over a
   list of instances.
2. It mentions the object it is about: a matrix, a graph, a census, a code.
3. `lake build` is clean, the file contains no `sorry`, and `#print axioms` shows only
   `propext`, `Classical.choice`, `Quot.sound`.
4. Any numeric constant in it is either proved or cited to a log entry that can be regenerated
   from this repository.
