# Research roadmap — the next steps

**Scope.** This is a *working* roadmap: a prioritised list of the concrete next results to
aim at, written against the code that is actually in the tree today.  It supersedes nothing;
`RESEARCH_ROADMAP.md` keeps the long-horizon programme narrative and
`RESEARCH_COMPUTE_ROADMAP.md` keeps the computation ↔ formalisation pairing of workstreams
W1–W5.  What is new here is (a) an honest audit of *what kind* of statement each part of the
library currently proves, (b) for every proposed next step a target Lean statement precise
enough to start on immediately, and (c) an explicit separation between what is machine-checked
and what is only numerical evidence.

**The standard used throughout.**  A line counts as *proved* only when a Lean theorem states
it for every dimension (not for a tabulated list of dimensions), and `lake build` accepts the
file with no `sorry` and only the standard kernel axioms.  Everything else is labelled
*evidence* and says exactly what range it was checked in.

---

## 0. Status snapshot (verified 2026-09-22)

* `lake build` completes: 8239 jobs, no errors, no `sorry` anywhere in `Sovereign/`,
  `RequestProject/` or the root modules.
* 212 Lean files, ≈2470 `theorem`/`lemma` declarations.
* The core Cayley–Dickson thread is proved *uniformly in the dimension*: the degree census
  and its closed form, its first four moments, the charge-sector census, its closed form and
  its `2^(n-3)` classes, and the vertex-degree/edge-count bridge from the census to the
  annihilation graph.
* A syntactic audit of the same tree: of the ≈2470 statements, ≈1200 carry no binder at all —
  they are closed numerical statements about defined constants — and 32 of the 174 files with
  theorems consist *entirely* of such statements.  This is not automatically a defect (an
  instance such as `census_dim64_closed_exact` is a checked corollary of a general theorem),
  but it does locate the part of the library where the mathematics is still carried by a table
  rather than by a quantifier.  Items **R3**, **R4** and **R8** below are about that part.

Two structural observations drive the priorities:

1. **The census thread has reached the point where the *general* statements are the cheap
   ones.**  Everything about a sector is now determined by an `(n-3)`-bit word; the remaining
   questions (a non-recursive multiplicity formula, all higher moments, the limit law) are
   statements about that word, not new combinatorics.
2. **The spectral and asymptotic layers are still tabulated.**  `LimitingDegreeDistribution`
   *defines* the numbers `μ_k` and proves identities between them; `IrregularGraphSpectralBounds`
   *defines* `λ₂ ≤ 7/12` as a constant.  Nothing in either file mentions the census or an
   adjacency matrix.  Connecting them to the objects they are named after is the single largest
   increase in real content available in the project, and — because the objects are now fully
   determined — it is reachable.

---

## 1. Tier A — do these next (high value, evidence already in hand)

### R1. The non-recursive sector census (closes W2)

**Where it stands.** `sectorCount n χ v = sectorClosed n χ v` for all `n ≥ 3`, `χ ≠ 0`, `v`
(`Sovereign/Combinatorics/TowerSectorCensusClosedForm.lean`), and the census depends on `χ`
only through the word `sectorKey n χ` (`…/TowerSectorCensusClasses.lean`).  `sectorClosed` is
still a recursion on the level.

**Target.** A profile function with *no* recursion on the census: with `L = n - 3`, read the
word `w = sectorKey n χ` as a list of steps, step `t` acting at level `m = 3 + t` by the affine
map

```
push m 0 v = 2 * v + 4                  (low step)
push m 1 v = 2 ^ (m + 1) - (2 * v + 4)  (high step)
```

Then the whole census is one *main* family plus one contribution per step:

```
sectorProfile n w v =
    (if v = push_{0..L-1} 4 then 6 * 2 ^ L else 0)
  + Σ_{t < L} (if v = push_{t+1..L-1} (2 ^ (t + 4) - 4) then 2 ^ (L - t) else 0)
```

and the theorem to prove is

```
theorem sectorCount_eq_sectorProfile (n χ v : Nat) (hn : 3 ≤ n) (hχ0 : χ ≠ 0) (hχ : χ < 2 ^ n) :
    sectorCount n χ v = sectorProfile n (sectorKey n χ) v
```

**Why.** It is the sector analogue of `censusClosedForm`, and it makes the *multiplicity
profile* a corollary rather than a separate project: the multiset of multiplicities of a sector
is `{6·2^(n-3)} ∪ {2^(n-3-t) : t a step}` with the merges dictated by the word, which is the
one piece `sectorCount_support_card` does not give.  It also gives the degree of a sector in
closed bit form, which is what R4 and R6 need as input.

**Evidence.** The identity above was checked against the *proved* closed form for every level
`3 ≤ n ≤ 11` and every non-zero charge (all `2^n - 1` of them per level): exact agreement.  A
machine-checked instance layer is in
`Sovereign/Combinatorics/TowerSectorProfile.lean` (see §4).

**Status (2026-09-22): proved.**  `Sovereign/Combinatorics/TowerSectorProfileClosed.lean`
establishes `sectorCount_eq_sectorProfile` for every level, charge and degree; the review in
`docs/RESEARCH_REVIEW_V7.md` records what it unlocks.

**Route.** Induct on `n` exactly as `sectorClosed` descends; the only real lemma is that the
affine maps commute with the `mod 16` separation already proved
(`sectorCount_low_eq_zero` / `sectorCount_high_eq_zero`).  Low risk.

### R2. All higher moments of the degree census, uniformly in `k` (closes W1)

**Where it stands.** `censusMoment3_formula` and `censusMoment4_formula` prove `M_3` and `M_4`
in every dimension, via `censusWeightedSplit`, which handles polynomial weights of degree ≤ 4.

**Target.** Two steps, the second being the real one.

```
-- (a) mechanical: raise the splitting lemma to arbitrary degree
theorem censusWeightedSplit_general (q d : Nat) (c : Nat → ℤ) : …

-- (b) the uniform statement
theorem censusMoment_poly (k : Nat) :
    ∃ p : Polynomial ℚ, p.natDegree = k + 2 ∧ p.coeff (k + 1) = 0 ∧
      ∀ q, (censusMoment k q : ℚ) = p.eval ((2 : ℚ) ^ (q + 3))
```

**Why.** It converts an open-ended sequence of one-off computations (`M_5`, `M_6`, … each a
separate proof today) into a single theorem, and it is the finite-`D` half of R3.

**Evidence.** For `0 ≤ k ≤ 10` the moment `M_k` is exactly a polynomial in `D = 2^(q+3)` of
degree `k + 2` whose `D^(k+1)` coefficient vanishes: interpolated through `k + 3` points and
then confirmed on all `q ≤ 15` (exact rational arithmetic).

**Route.** The doubling law already used for `M_3`, `M_4` is
`M_k(2D) = 2 Σ_v [(2D - (2v+4))^k + (2v+4)^k] c(v) + (2D-4)^k · 6(D-1)`.  Expanding the
binomial turns it into a triangular linear recursion for the coefficient vector of `M_k` in
terms of `M_0, …, M_k`; the degree and the vanishing coefficient fall out of that recursion by
strong induction on `k`.  Medium effort, no missing mathematics.

### R3. Make the limiting degree distribution a theorem about the census

**Where it stands.** `Sovereign/Combinatorics/LimitingDegreeDistribution.lean` defines
`mu0 … mu8` as rational constants and proves 26 closed identities between them (the reflection
symmetry, the variance `7/60`, the kurtosis ratio).  Nothing in the file refers to `censusT`,
so nothing there currently constrains the tower.

**Target.**

```
theorem censusMoment_tendsto (k : Nat) :
    Filter.Tendsto (fun q => (censusMoment k q : ℝ) / (2 ^ (q + 3)) ^ (k + 2))
      Filter.atTop (nhds (limitingMoment k))
```

with `limitingMoment` *derived* from the recursion of R2 (so that `limitingMoment 2 = 11/30`
becomes a corollary instead of a definition), followed by

```
theorem limitingMoment_reflect (k : Nat) :
    ∑ j ∈ Finset.range (k + 1), (-1) ^ j * (k.choose j) * limitingMoment j = limitingMoment k
```

proved from the reflection symmetry of `censusT` rather than checked term by term, and finally
the identification of the limit law itself: the descent is an iterated function system with the
two contractions `x ↦ x/2` and `x ↦ 1 - x/2` of the normalised degree `x = v/D`, plus the
`6(D-1)` atom that each doubling step deposits at the top degree.  Naming that measure — and
proving that its moments are the `μ_k` — is the substantive question behind the numbers.

**Why.** It turns the largest purely tabulated module in the library into mathematics, and it
explains the constants: `μ_2 = 11/30` exceeds the uniform value `1/3` by exactly `1/30`, which
is the mass the atoms contribute; today that excess is an observation about two rationals.

**Evidence.** The nine constants `mu0 … mu8` in the file agree exactly with the leading
coefficients computed from the Lean definition of `censusT` by exact interpolation
(`1, 1/2, 11/30, 3/10, 1679/6510, 99/434, 2888981/14055090, 75373/401574, 651294729/3762079090`).
So the table is *right*; it is only unconnected.

**Route.** R2 first — with the polynomial in hand, the limit is the leading coefficient and the
`Tendsto` proof is routine.  The measure-theoretic identification is a separate, harder piece
and should be scheduled after the moment statement, not before.

---

## 2. Tier B — the structural gaps

### R4. Spectra of the actual sector graphs (closes W5)

**Where it stands.** `Sovereign/Graph/CrossHalfVertexDegree.lean` is the model to follow: it
defines the decidable test `crossAnnihilates`, proves it equivalent to annihilation in the
algebra, and derives the vertex degree `2 · towerDegree n i j` and the edge count
`D³/4 - 28D + 96` in every dimension.  By contrast `IrregularGraphSpectralBounds.lean` proves
facts about the constants `lambda2MaxBound = 7/12`, `spectralGapMinBound = 5/12`,
`cheegerConductanceMinBound = 5/24`; no adjacency matrix appears in it.

**Target, in three stages.**

1. `sectorAdj n χ : Matrix V V ℚ` built from `crossAnnihilates`, with `sectorAdj_symm` and
   the row-sum lemma `∑ w, sectorAdj n χ v w = crossDegree …` (immediate from the proved
   degree law).
2. The twin quotient: vertices with equal neighbourhoods form an equitable partition, so the
   non-zero spectrum of `sectorAdj` is the spectrum of a `(D-2)/2`-row quotient.  Statement:
   `sectorAdj_charpoly_eq_quotient_charpoly_mul_pow_X`.
3. Regular sectors — those with `sectorKey n χ = 0`, which R1/`sector_degree_constant_iff`
   characterises as `χ < 8` or `χ` a power of two — have an explicitly computable spectrum;
   for the rest, prove a genuine bound `λ₂ ≤ …` by Cauchy interlacing on the quotient from
   the proved degree bounds `8 ≤ d ≤ D - 8`, and then either *prove* the `7/12` constant or
   retire it.

**Why.** Every downstream expander/Cheeger/Ramanujan claim in the project currently rests on
the tabulated `7/12`.  Replacing it with a proved bound is what makes those modules mean what
their names say.  The exact spectra are already computed for `D ≤ 64` (log `w5.json`), and the
`ℚ(√57)` irrationality at `D = 64` is the concrete target the formal statement must accommodate
(so: do not state the general theorem over `ℤ`).

**Risk.** The largest item on this roadmap.  Mathlib has characteristic polynomials and
interlacing-adjacent material but not equitable-partition quotients; stage 2 is the piece that
may have to be built from scratch.  Budget it as its own workstream, and keep stage 1 shippable
on its own.

### R5. A bijective proof of the prefix-depth class sizes (closes W3)

**Target.** A map from admissible index pairs to prefix depth, and the resulting structural
proof of `degreeCount_level_card` (currently proved by counting, in
`TowerDegreeCensusLevels.lean`).  Concretely: show the prefix depth of the degree index equals
the level at which the descent of `degreeClosed` stops, then transport the class decomposition
along that map.

**Why.** It is the last member of the census family still proved by arithmetic rather than by
structure, and the bijection is what would let the census be read off a pair directly — useful
for R6 and for any attempt at a combinatorial model of the graph.

### R6. Sector-level graph invariants, for free

Once R1 and the `crossDegree` law are both available, the following are short:

* the degree multiset of the sector graph and its handshake identity per sector;
* the sector edge count as a bit formula in `χ` (the global count is already proved);
* connectivity/diameter statements per class rather than per dimension — there are only
  `2^(n-3)` classes to examine, and the degenerate class is completely explicit.

These are the natural regression tests for R1: each is a corollary whose value can be checked
against `w4.json` and `w5.json` before it is proved.

---

## 3. Tier C — hygiene, reproducibility, and the strengthening programme

### R7. Restore the computation layer referenced by the roadmaps

`RESEARCH_COMPUTE_ROADMAP.md` documents `scripts/research/cd_kernel.py` and per-workstream
scripts `w1_…`–`w5_…`; the tree currently contains `scripts/research/run_all.py` plus
`src/sedenion/research/w1_census_moments.py` and `w2_sector_census.py` only, while
`logs/research/` holds results for W1–W26.  So most logged verdicts cannot be re-derived from
this repository.

**Target.** Either restore the generators or regenerate the logs from scripts that exist, and
add a check that every constant asserted in a Lean file which also appears in a log matches it
(a `#eval`-versus-JSON comparison, run in CI).  Low mathematical content, high value for
trust: it is the difference between a log and a reproducible computation.

### R8. The strengthening programme

The project already has the right pattern for this: `MillenniumStrong.lean` and
`ABCEpsilonZero.lean` each say, in their own docstrings, that the module they replace recorded
bookkeeping and that each heading has been re-proved with content.  Apply it systematically to
the 32 fully closed-statement modules, in this order (largest content gap first):

| module | what it asserts today | content-bearing replacement |
| --- | --- | --- |
| `Combinatorics/LimitingDegreeDistribution` | nine rational constants + identities | R3 |
| `Graph/IrregularGraphSpectralBounds` | `λ₂ ≤ 7/12` as a constant | R4 |
| `Graph/AnnihilationGraph`, `Graph/ZeroDivisorModularKernel` | vertex/edge counts for listed `D` | statements quantified over `n`, on top of `crossAnnihilates` |
| `Geometry/StiefelFrameCensus`, `Geometry/ToroidalEmbedding` | frame/torus counts for listed dimensions | a census theorem in the dimension parameter |
| `Fluid/BoundaryCoupling`, `Fluid/CoupledSingularity` | numeric identities named after PDE facts | statements about the fields they name, or an explicit downgrade of the claim in the docstring |
| `Quantum/QuantumThresholdObstruction`, `Quantum/RateDistanceProduct` | threshold/rate constants | bounds quantified over the code family |

**Rule of thumb for "content-bearing".** The statement must mention the object (a matrix, a
graph, a field, a code), and it must quantify over the parameter the module's name claims to
be about.  A file whose every theorem can be checked by `norm_num` is a table; tables are
useful, but they should be introduced as instances of a theorem, not as the theorem.

### R9. Finish the Chladni/D₄ thread

`Taxonomy/ChladniNodalD4.lean` proves D₄-equivariance of `cos(3x)cos(5y) − cos(5x)cos(3y)` for
all real mode numbers, the visible straight lines for odd integer modes, and the exact
half-open-grid defect of the exporter.  The natural generalisation: for arbitrary integer modes
`(p, q)` characterise which of the lines `x = kπ/(2r)` lie in the nodal set, and count nodal
domains.  The sampling-grid lemmas (`gridPt`, `inSample`, `sample_d4_invariant`) should be
lifted out of the Chladni file into a reusable "what the exporter actually plots" API, since
every future figure in the project has the same failure mode.

### R10. Long shots, stated so they can be attacked

* **Spectral field tower.** Prove, rather than tabulate, that the component spectra are
  integral for `D ≤ 32` and generate `ℚ(√57, √145)` at `D = 64`.  R4 stage 2 is the enabler.
* **Asymptotic expansion.** With R2 and R3, ask whether the normalised spectral measure of the
  annihilation graph converges, and whether the family is asymptotically Ramanujan — the
  Alon–Boppana comparison in `Graph/AlonBoppanaObstruction.lean` is currently a statement about
  constants.
* **Codes from sectors.** The sector classes give `2^(n-3)` candidate code families per
  dimension; the distance of each is a function of its word.  A distance bound proved from R1
  would be the first genuinely *derived* result in the coding modules.

---

## 4. Machine-checked evidence shipped with this roadmap

Conjectures in §1 are supported by computations; to keep the standard of the project, the
central one is also checked *inside Lean*, against the proved closed form, in
`Sovereign/Combinatorics/TowerSectorProfile.lean`:

* `sectorProfile` is defined exactly as in R1 (a fold of affine steps over the bits of the
  descent word, with no recursion on the census);
* `sectorCount_eq_sectorProfile_dim16/32/64/128` prove, by kernel evaluation together with the
  proved determination theorem, that the profile reproduces `sectorCount n χ v` for every
  charge and every degree in dimensions 16, 32, 64 and 128.

That is an instance layer, not the theorem: R1 is still open, and is stated in the module
docstring as the target.  The polynomial-moment evidence of R2/R3 (`k ≤ 10`, `q ≤ 15`) is
numerical only and is *not* machine-checked.

---

## 5. Suggested sequencing

```
R1 ──► R6 ──► R10 (codes)
 │
 └───► R4 stage 1 ──► R4 stage 2 ──► R4 stage 3 ──► R10 (field tower, Ramanujan)

R2 ──► R3 (moments) ──► R3 (measure)

R5, R7, R9  independent; R7 first if the logs are to be trusted by anything downstream.
R8 is the umbrella that R3 and R4 discharge two rows of.
```

A reasonable next sprint is **R1 + R2 + R7**: all three are self-contained, all three have
their evidence already in hand, and together they unlock R3, R4 and R6.

## 6. Definition of done (unchanged, restated)

1. The statement quantifies over the dimension (or over `k`, or over the charge) — not over a
   list of instances.
2. It mentions the object it is about.
3. `lake build` is clean, `#print axioms` shows only `propext`, `Classical.choice`,
   `Quot.sound`, and the file contains no `sorry`.
4. Any numerical constant appearing in it is either proved or cited to a log entry that can be
   regenerated from this repository.
