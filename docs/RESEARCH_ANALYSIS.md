# What this line of research is, where it leads, and what it is good for

*An analytical survey of the programme in this repository: its object of study, the
mechanism that makes it work, the results that are actually proved, the results that are
only computed, the claims that are neither, and the applications that are realistic.*

Everything called **proved** below names a Lean theorem that `lake build` accepts in this
repository with no `sorry` and only the standard kernel axioms. Everything called
**computed** names a logged exact computation in `logs/research/` — evidence, not proof.
Everything called **parameter-level** is a theorem about constants defined a few lines above
it, which therefore says nothing about the object it is named after. The distinction is the
single most important thing to keep in view when reading this project.

---

## 1. Executive summary

The mathematical core of this repository is a complete, uniform, machine-checked
combinatorial theory of **zero divisors in the Cayley–Dickson tower** — the sequence of
algebras ℝ, ℂ, ℍ, 𝕆, 𝕊 (sedenions), 𝕋 (trigintaduonions), … obtained by iterated doubling.
From dimension 16 onwards these algebras are no longer division algebras, and the structure
of their zero divisors has classically been studied one dimension at a time, largely by
computer search.

This programme replaces that with statements proved **simultaneously in every dimension
D = 2ⁿ**, by turning the algebra into bit arithmetic:

* the product of basis vectors is `e_a · e_b = ± e_{a⊕b}` — a twisted group algebra over
  (ℤ/2)ⁿ (`basis_mul`);
* failure of associativity is a ±1 function of three indices (`assocNeg`), and *all* the
  counting invariants of the programme are statistics of that one function;
* every such statistic obeys a **doubling law** relating level n to level n+1, and therefore
  has a closed form polynomial in D.

The results that follow from this — an exact degree formula, a degree quantisation `≡ 8 mod
16`, the exact degree spectrum, the closed-form degree census, the associating-triple law,
the handshake identity, the vertex and edge counts of the annihilation graph, the moments of
the degree distribution up to order 4 (order 6 computed), the classification of regular
charge sectors — form a coherent, genuinely new body of exact mathematics about a classical
object, and they are all formally verified.

Around that core sits a much larger, much weaker layer: modules that attach a famous name
(Navier–Stokes, Yang–Mills, BSD, fault tolerance) to arithmetic about locally defined
constants. Earlier curation passes removed the worst of it and labelled the rest; an audit
of what remains classifies 630 of ~2450 theorems as evaluations of locally defined
parameters. Those modules should not be read as results about the objects they name, and
this document does not treat them as such.

---

## 2. What is actually going on

### 2.1 The algebra reduces to a sign cochain on 𝔽₂ⁿ

`Tower n` is the n-fold Cayley–Dickson double of ℤ, of dimension 2ⁿ, with basis `basis n a`
indexed by `a < 2ⁿ`, i.e. by 𝔽₂ⁿ. The key structural theorem (`Sovereign/Algebra/TowerBasis.lean`) is

> `basis n a * basis n b = ± basis n (a ^^^ b)`,

with an explicit recursive sign `epsNeg n a b ∈ {±1}`. So each algebra in the tower is the
**twisted group algebra** ℤ_ε[(ℤ/2)ⁿ]: the multiplication table is entirely determined by a
2-cochain ε on 𝔽₂ⁿ with values in {±1}, defined by the doubling recursion.

Associativity of a twisted group algebra is exactly the 2-cocycle condition on ε; hence the
associator of three basis vectors is the **coboundary**

> `dε(a,b,c) = ε(b,c) ε(a, b⊕c) ε(a,b)⁻¹ ε(a⊕b, c)⁻¹ ∈ {±1}`,

which the library calls `assocNeg n a b c`. ℝ, ℂ, ℍ have `dε ≡ +1`; from 𝕆 onwards `dε`
takes the value −1 somewhere, and its −1-set is the whole subject of the programme.

This is the conceptual heart. *Every* quantity studied here is a weight, a slice, or a
moment of the single ±1 function `dε` on 𝔽₂ⁿ × 𝔽₂ⁿ × 𝔽₂ⁿ:

| object | in terms of `dε` |
| --- | --- |
| non-associating middles of `(i, j)` | `{k : dε(i,k,j) = −1}`, size = the *degree* |
| associating triples `A(D)` | number of `(a,b,c)` with `dε = +1` |
| annihilation of `±eᵢ ± e_{H+j}` | two sign conditions built from ε, plus `i⊕j = k⊕m` |
| charge sectors | fibres of the XOR charge `χ = i⊕j` |

### 2.2 Zero divisors, and the graph they form

For `H = 2ⁿ` and algebra dimension `Dₐ = 2H`, the *cross-half* vectors are
`v = s·eᵢ + t·e_{H+j}` with signs `s, t ∈ {±1}`. `TowerZeroDivisors.lean` proves, **in the
algebra and for every n**, that

> `v · w = 0` ⟺ the XOR charges agree (`i⊕j = k⊕m`) **and** two explicit ε-sign conditions hold
> (`crossVec_mul_eq_zero_iff`),

so annihilation conserves the charge χ. This is the general-dimension form of what the
sedenion (D=16) and trigintaduonion (D=32) modules had established only by exact evaluation.

The **annihilation graph** has these zero divisors as vertices and annihilating pairs as
edges. `CrossHalfUniversal.lean` proves in every dimension: there are `(Dₐ−2)(Dₐ−4)` vertices;
the remaining cross-half vectors number `6Dₐ−8`; the graph splits into `Dₐ/2 − 1` charge
sectors of `2(Dₐ−4)` vertices each; and `(Dₐ−2)(Dₐ−4) = 8·T_{(Dₐ−4)/2}` (an "eightfold
triangular" identity).

### 2.3 The mechanism: renormalisation under doubling

Why is any of this exactly computable? Because the inclusion `𝔽₂ⁿ ⊂ 𝔽₂ⁿ⁺¹` makes `dε`
**self-similar**: the level-(n+1) data is two copies of the level-n data, one with the degree
map `v ↦ 2v + 4` and one with the reflection `v ↦ D − (2v+4)`, plus a fixed number of new
extremal items. This single fact drives the entire programme:

* **Degrees are finite-state functions of bits.** The degree of a pair `(i, j)` is computed
  by a descent on the binary expansions (`towerDegree`), and then in closed form
  (`degreeClosed n i j = 2ⁿ⁻¹ − 4 + altSum (i⊕j) (stopLevel n i j) n`) as an alternating
  dyadic sum over the set bits of `i⊕j` above a stop level
  (`nonassocMiddles_card_eq_degreeClosed`). The degree is, in effect, a 2-automatic function
  of the index pair.
* **Multiplicities depend only on a prefix statistic.** The number of pairs of a given degree
  in dimension `2^(q+3)` depends on the degree index `t` only through its *prefix depth* —
  the larger of its leading-zero and leading-one counts (`degreeCount_eq_censusClosedForm`).
  Hence only `q+1` distinct multiplicities occur, the class of depth `k` containing `2^(q−k)`
  degrees (`tower_degree_census_multiset`), and the census is symmetric under complementation
  (`degreeCount_symm`).
* **Every weighted count satisfies a doubling law, hence is a polynomial in D.** The general
  law `censusT_succ_weighted` transports an arbitrary weight through one doubling step; each
  moment then follows by induction.

That is the answer to "what exactly is going on": *the nonassociativity of the
Cayley–Dickson tower is a renormalisable, self-similar structure on binary strings, and
every counting question about its zero divisors is therefore answerable in closed form,
uniformly in the dimension.*

---

## 3. The proved core, in one table

`D = 2ⁿ` is the tower parameter; the algebra carrying the graph has dimension `Dₐ = 2D`.

| statement | theorem | file |
| --- | --- | --- |
| basis product law `e_a e_b = ± e_{a⊕b}` | `basis_mul` | `Algebra/TowerBasis.lean` |
| annihilation criterion, every dimension | `crossVec_mul_eq_zero_iff` | `Algebra/TowerZeroDivisors.lean` |
| charge conservation | `crossVec_charge_conservation` | `Algebra/TowerZeroDivisors.lean` |
| vertex/sector counts, eightfold triangular law | `zdVerts_card_universal`, `sector_card`, `zd_triangular_universal` | `Algebra/CrossHalfUniversal.lean` |
| exact degree of a pair (closed form) | `nonassocMiddles_card_eq_degreeClosed` | `Combinatorics/TowerDegreeClosedForm.lean` |
| degree quantisation (`≡ 4 mod 8` middles) | `nonassocMiddles_card_mod_eight` | `Combinatorics/TowerDegreeQuantization.lean` |
| exact degree spectrum | `nonassocMiddles_card_spectrum` | `Combinatorics/TowerDegreeQuantization.lean` |
| associating triples `A(D) = D³/2 + 14D − 24` | `associatingTriples_formula` | `Combinatorics/AssociatingTriplesCount.lean` |
| handshake `T(D) + A(D) = D³` | `totalNonassocMiddles_formula` | `Combinatorics/TowerDegreeHandshake.lean` |
| closed-form census | `degreeCount_eq_censusClosedForm` | `Combinatorics/TowerDegreeCensusClosedForm.lean` |
| complete degree multiset | `tower_degree_census_multiset` | `Combinatorics/TowerDegreeCensusLevels.lean` |
| moments of order 1–4 | `degreeCount_second_moment`, `…_third_…`, `…_fourth_…` | `Combinatorics/TowerDegreeMoments*.lean` |
| **variance of the degree distribution** | `censusVariance_formula`, `degreeCount_variance` | `Combinatorics/TowerDegreeVariance.lean` |
| sector census: size and descent laws | `sectorPairs_card`, `sectorCount_succ_low/high/…` | `Combinatorics/TowerSectorCensus.lean` |
| vertex degree of the graph, edge count | `crossDegree_eq_two_mul_towerDegree`, `crossTotalDegree_formula` | `Graph/CrossHalfVertexDegree.lean` |
| regular sectors: `χ < 8` or `χ = 2ᵏ`; `n+4` of them | `chargeSector_regular_iff`, `regularSectorCharges_card` | `Combinatorics/…`, `Algebra/TowerSectorRegularity.lean` |
| confinement inside the subalgebra | `cross_half_confinement_iff_degenerate` | `Algebra/TowerAssociatingConfinement.lean` |

Reading the graph off this: in the algebra of dimension `Dₐ`, the annihilation graph has
`(Dₐ−2)(Dₐ−4)` vertices, every vertex degree is `≡ 8 mod 16` and lies between `8` and
`Dₐ − 8`, and there are exactly `Dₐ³/4 − 28Dₐ + 96` edges (672, 7392, 63840 in dimensions
16, 32, 64).

### 3.1 The new result of this pass: how spread out the degrees are

The moments give the size of the degree distribution; what they had not been combined into
is its *shape*. `Combinatorics/TowerDegreeVariance.lean` (added now, proved for every
dimension) gives the exact second central moment:

> `60 (M₀M₂ − M₁²) = 7D⁶ − 66D⁵ − 516D⁴ + 8520D³ − 38112D² + 70656D − 47104`,
> with `M₀ = (D−1)(D−2)`, `2M₁ = D³ − 28D + 48`, `30M₂ = 11D⁴ − 700D² + 2880D − 3136`.

Interpreted: the degree of a uniformly random admissible pair has mean `M₁/M₀ = D/2 + O(1)`
and variance `(7/60)D² + O(D)`. The standard deviation is therefore about `0.342 D` against a
mean of `0.5 D` — the degrees occupy a window as wide as the dimension itself. Two
consequences worth stating plainly:

1. **The graph is maximally irregular, in every dimension.** Not "not regular": the degree
   spread is of the same order as the degree. Any argument that treats the annihilation graph
   as an approximately regular graph is unsound.
2. **There is a limit law.** The normalised degree `x = v/D` has a limiting distribution on
   `[0,1]`, symmetric about `1/2` (that symmetry is `degreeCount_symm`, proved), with moments
   `1/2, 11/30, 3/10, 1679/6510, 99/434, 2888981/14055090, …` (the first four proved, the
   last two computed). It is U-shaped: more spread than uniform (variance `7/60` versus
   `1/12`), less than the arcsine law. Identifying this measure is a clean open question —
   see §5.1. The Mersenne-type factors `3, 7, 31, 127` in the denominators are the signature
   of the doubling recursion and suggest the moments satisfy an explicit linear recursion.

---

## 4. What is computed but not proved, and what is merely named

### 4.1 Computed, logged, and open

`scripts/research/` (a dependency-free exact-arithmetic harness; 158 boolean checks, 0
failures in the committed run) has pushed five fronts past the proof frontier:

| front | computed | still open |
| --- | --- | --- |
| moments | `M₅`, `M₆` exactly, `q ≤ 13` | a **uniform** theorem: `M_k` is a polynomial of degree `k+2` with vanishing `D^{k+1}` coefficient, for all `k` |
| sector census | all sectors, `n ≤ 10`; `2^(n−3)` distinct sector censuses | a closed form for `sectorCount n χ v` from the bits of `χ` |
| prefix-depth classes | class sizes re-derived, `q ≤ 12` | a *bijective* proof of `degreeCount_level_card` |
| graph counts | `D ≤ 128` | — (now proved in every dimension) |
| sector spectra | exact characteristic polynomials, `D = 16, 32, 64` | any general spectral theorem |

The spectral front is the substantive gap. What the computation shows: in `D = 16` every
sector has spectrum `{±8, ±4², 0¹⁸}`; in `D = 32` every eigenvalue is a rational integer; in
`D = 64` integrality fails for the first time, the regular sectors leaving the factor
`x² + 4x − 224` with roots `−2 ± 2√57`. Structurally, each sector has an equitable partition
into twin classes (vertices with identical neighbourhoods), so its non-zero spectrum is that
of a quotient with `(Dₐ−2)/2` rows instead of `(Dₐ−2)(Dₐ−4)` — that quotient is the right
object for a proof, and none exists yet.

### 4.2 The parameter-level layer

A large part of the repository consists of modules that define constants and then prove
arithmetic about them. `scripts/lean_theorem_audit.py` classifies 630 of the ~2450 theorems
across both libraries as such evaluations. In particular:

* `Sovereign/Fluid/*` does not contain the Navier–Stokes equations. It contains identities
  about named rational constants and a vanishing-vortex-stretching statement for a
  16-dimensional toy bilinear form. It is not evidence about regularity of any PDE.
* `Sovereign/Physics/Millennium*` is bookkeeping, and the module `MillenniumStrong.lean`
  says so explicitly before replacing five of its headings with genuine (and much more
  modest) theorems: hypercharge determination from anomaly cancellation, evenness of the odd
  Betti numbers of a Kähler manifold, `a_p = 0` for `y² = x³ − x` at `p ≡ 3 mod 4`,
  reflection symmetry of the zeros of ζ.
* Several `Quantum/*` modules state code parameters as `structure` fields and prove
  arithmetic relations between them. The underlying coding-theoretic claims (distance,
  triple-evenness, transversality) are *asserted at the parameter level*, not derived from a
  constructed code.
* `Graph/IrregularGraphSpectralBounds.lean` records numerical bounds as rational constants;
  it is a table, not a spectral theorem.

The honest reading: names like "settles OP-0xx" in this repository record the project's own
problem list, not a resolution of anything in the literature. The genuinely load-bearing
mathematics is the Algebra/Combinatorics/Graph core described in §2–§3, plus a handful of
independent results (the `ε = 0` abc family in `NumberTheory/ABCEpsilonZero.lean`, the
`MᵀM = 24·I₂₁` cubature identity in `Geometry/StiefelCubature.lean`, and the second library
described in §7).

---

## 5. Where it leads

### 5.1 A limit theory for the degree distribution

The natural next object is the **generating function** `Z_q(x) = Σ_t x^{8t+4} censusT q t`.
The doubling law is a functional equation for `Z_q` (two substitutions plus a boundary term),
and from it should follow, in order:

1. the uniform moment theorem (`M_k` polynomial of degree `k+2`, `D^{k+1}` coefficient zero)
   — this is the first genuinely *structural* statement of the programme rather than another
   instance;
2. an explicit transfer-operator representation: the census is a product of small matrices
   read along the bits of `t`, which would turn `censusClosedForm` from a proved formula into
   an explained one;
3. identification of the limiting normalised degree law, whose moments are listed in §3.1.

Difficulty: (1) is a substantial but standard induction over an abstract weight — the
existing `censusT_succ_weighted` already does one step for arbitrary weights, so the work is
in handling a symbolic degree `k`. (2) and (3) are research-level but small.

### 5.2 Spectral theory of the sectors

The intended chain is: twin classes → equitable partition → quotient matrix of size
`(Dₐ−2)/2` → exact characteristic polynomial for regular sectors → Cauchy interlacing for the
irregular ones, bounding `λ₂` from the proved degree bounds `8 ≤ d ≤ Dₐ − 8`. That would
replace the tabulated constants of `IrregularGraphSpectralBounds` with theorems, and would
give the first honest statement about expansion of these graphs.

There is already an obstruction result pointing the way: `d − 1 = Dₐ − 9 ≡ 7 mod 8` is never a
perfect square, so the Alon–Boppana bound `2√(d−1)` is irrational in every dimension and a
sector with integer eigenvalues can never saturate it (`Graph/AlonBoppanaObstruction.lean`;
its argument is a clean number-theoretic one, though the eigenvalue values it feeds on are
tabulated rather than derived). Coupled with §4.1's finding that integrality *fails* at
`D = 64`, the interesting question becomes: **which quadratic fields occur, and with what
regularity?** `ℚ(√57)` at `D = 64` is a concrete first data point.

### 5.3 Structure theory, not just counting

Three questions the counting has made askable:

* **A bijective theory.** The census is currently proved by descent. A bijection from
  admissible pairs to prefix-depth classes (workstream W3) would explain *why* multiplicities
  are `2^(q−k)`, and would likely generalise to the sector census.
* **Automaticity.** Is the sequence `(degree of the pair (i,j))` 2-automatic in a precise
  sense, and is `censusT` the coefficient sequence of an algebraic power series over 𝔽₂? The
  closed forms strongly suggest yes; a proof would connect this programme to the standard
  toolkit for automatic sequences.
* **Beyond cross-half.** Everything here concerns cross-half zero divisors, which are the
  canonical family but not all of them. The doubling mechanism does not obviously stop there;
  extending the criterion to general pairs of vectors is the largest available generalisation.

### 5.4 Codes with prescribed divisibility

The proved divisibility `degree ≡ 8 mod 16` in the graph, together with the (computed, not
yet proved) divisibility of common-neighbourhood sizes by 4, is exactly the input condition
for **triply-even binary codes** — the class underlying transversal T gates in quantum fault
tolerance. This is the one place where the pure results touch an application with no gap in
kind, only a gap in work: one must construct the code from the graph (rows = neighbourhoods),
prove the weight divisibility from the counting theorems, and then compute the actual
parameters. The existing `Quantum/*` modules assert those parameters; they do not construct
the code. This is the most promising concrete continuation.

---

## 6. Implications

**For the mathematics of Cayley–Dickson algebras.** The zero-divisor structure of the
sedenions and beyond has long been described dimension by dimension. This programme supplies
uniform closed forms — degree, spectrum of degrees, census, moments, edge count, sector
classification — valid in every dimension and verified. That is a qualitative change in what
is known about the objects, and it is the part of this repository that could stand on its own
outside it.

**For method.** The workflow here is worth naming: *exact computation first, formal proof
second*, with the computation transcribed from the Lean definitions so that a computed value
and a kernel evaluation are comparable term by term (`scripts/research/cd_kernel.py`), and a
logged verdict count that a proof must later subsume. The roadmap's working rule — a line
moves from *computed* to *proved* only when a Lean theorem states it for every dimension —
is the discipline that keeps the two apart. It works: every closed form in §3 was first
found numerically.

**For the epistemics of machine-generated mathematics.** This repository is also a case
study in how such a corpus goes wrong. Thousands of declarations accumulated, most of the
grand-sounding ones being arithmetic about their own definitions; three duplicate copies of
the source tree existed simultaneously; the build did not run at all. Recovery required
deleting ~104 modules and ~147 individual declarations, and instituting an audit script that
classifies every declaration. The lesson generalises: in an automated formalisation pipeline,
**the classifier matters as much as the prover**. A theorem that builds is not thereby a
theorem about anything.

---

## 7. The second library

`RequestProject/` is an unrelated and comparatively conventional development, in four
clusters, and it is mathematically sound:

* `DigitalRoot/` — digital roots in an arbitrary base `b` with divisor `d ∣ b−1`: casting out
  `(b−1)`s, divisibility detection, the "trinity" `{d, 2d, …}` with `(b−1)/d` elements,
  additivity/multiplicativity, and the periodicity of digital roots of powers. The decimal
  case is *defined* as `b = 10`, so the familiar 3/6/9 facts are corollaries.
* `Sieve/Legendre.lean` — the exact Legendre density of a finite sieve: survivors in one
  period are the residues coprime to `M = ∏ p`, giving density `∏(1 − 1/p)`.
* `Hecke/` — `HeckeSystem`: the purely algebraic axioms of a normalised Hecke eigenvalue
  system, with the resulting rigidity (agreement at the primes ≤ N forces agreement at all
  n ≤ N) — the honest algebraic shadow of multiplicity one, correctly flagged as *not* the
  analytic theorem.
* `Delta/` — Ramanujan's Δ as `η²⁴`: the q-expansion and τ, genuine modularity
  `Δ(−1/z) = z¹²Δ(z)` proved by the logarithmic-derivative/E₂ argument on top of Mathlib, and
  a "phase wall" theory explaining features of the domain-colouring portrait of Δ from only
  two inputs — real coefficients and period one.

The Δ modularity proof and the phase-wall theory are the strongest results in that library.

---

## 8. Practical applications, honestly tiered

**Tier 1 — usable today, directly from the proved results.**

1. *Constant-time zero-divisor arithmetic.* `crossVec_mul_eq_zero_iff` gives an O(1) test for
   annihilation of two cross-half vectors, and `degreeClosed` gives the size of a vector's
   annihilator in O(n) bit operations instead of O(D) enumeration. For symbolic-algebra
   support of sedenions/trigintaduonions — where the naive computation is quadratic in the
   dimension — this is an immediate speedup, and the Lean definitions are directly
   transcribable (as `scripts/research/cd_kernel.py` demonstrates).
2. *A family of structured test graphs with fully known statistics.* The annihilation graphs
   come with proved vertex count, edge count, degree multiset, and sector decomposition, and
   an O(1) adjacency oracle. Graphs whose degree distribution is *exactly* known but
   *maximally spread* (§3.1) are unusually good stress tests for spectral algorithms,
   degree-based heuristics, and graph-partitioning code, because they break the
   near-regularity assumptions such code often hides.
3. *A reusable formal library.* `Sovereign/Algebra/` is, as far as the build shows, a
   self-contained formalisation of the Cayley–Dickson tower with a twisted-XOR basis law,
   conjugation, coordinates, and a decidable annihilation test. Anyone formalising octonionic
   or sedenionic mathematics can build on it rather than redo it.

**Tier 2 — plausible with identified work.**

4. *Quantum codes with guaranteed weight divisibility* (§5.4). The route is concrete; the
   work is constructing the code and proving its weights from the counting theorems. Payoff
   if it lands: an infinite, explicitly indexed family of triply-even codes with closed-form
   parameters.
5. *Algebraic-degree lower bounds for nonassociative mixing functions.* The sponge modules
   propose hashing over these algebras; the useful, provable ingredient is that products in
   the tower have controlled algebraic degree growth and that the annihilator structure is
   exactly known — which is what one needs to *rule out* certain algebraic attacks. Current
   modules assume indifferentiability rather than proving it; a real result here would be a
   degree lower bound, not a security claim.
6. *Benchmark instances for spectral graph theory.* Once §5.2 is proved, the sectors become a
   family with known spectra and known non-saturation of Alon–Boppana — useful as certified
   ground truth for eigenvalue solvers and expander heuristics.

**Tier 3 — claimed in the repository, not supported by it.**

7. Global regularity for Navier–Stokes, the Yang–Mills mass gap, BSD, geometric Langlands,
   universal fault tolerance, three-generation particle physics. The modules bearing these
   names prove arithmetic about their own constants. They should be read as *notation for an
   aspiration*, and any external claim based on them would be unfounded.

---

## 9. Recommended order of work

1. **Uniform moment theorem** (§5.1.1). Highest ratio of structural value to risk; the
   doubling machinery is already in place.
2. **Triply-even code construction** (§5.4). The only application-facing item whose
   prerequisites are all proved.
3. **Regular-sector spectrum via the twin quotient** (§5.2). Closes the oldest open item in
   the programme's own list and is the gateway to every expansion statement.
4. **Closed form for the sector census** (§4.1). Mechanically similar to the global census,
   already computationally confirmed to level 10.
5. **Bijective proof of the prefix-depth class sizes** (§5.3). The explanatory, rather than
   verificatory, version of a result already proved.

And, orthogonally: continue the curation discipline. Every new module should be classified
when it is written — *general theorem*, *definitional evaluation*, or *table* — because the
credibility of the core depends on the layer around it being labelled accurately.

---

## 10. Where to look

| question | file |
| --- | --- |
| the mathematics, top-down | `next_steps.md`, then this document |
| the open/closed state of each workstream | `RESEARCH_COMPUTE_ROADMAP.md` |
| the computations and their output | `scripts/research/`, `logs/research/RESULTS.md` |
| what was removed and why | `docs/LIBRARY_CURATION.md`, `docs/REQUESTPROJECT_CURATION.md` |
| per-declaration classification | `scripts/lean_theorem_audit.py` |
| the algebra itself | `Sovereign/Algebra/TowerBasis.lean`, `…/TowerZeroDivisors.lean` |
| the counting theory | `Sovereign/Combinatorics/` |
| the graph | `Sovereign/Graph/CrossHalfVertexDegree.lean` |
