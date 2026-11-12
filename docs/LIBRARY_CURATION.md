# Curation of the formal library

This note records the September 2026 consolidation of the Lean sources: what was
kept, what was removed, and the conventions that new modules are expected to
follow.

## 1. Why

Before the consolidation the repository held three overlapping copies of the same
development:

| tree | `.lean` files | status |
| --- | ---: | --- |
| `formal/` | 246 | the build target (broken: 44 modules listed in `lakefile.toml` had no source file) |
| `lee/` | 374 | a flat snapshot; 186 files byte-identical to `formal/`, the rest superseded drafts (`CDTower2.lean`, `AnnihilationGraph2.lean`, …) |
| `experiments/legacy_sovereign/` | 2 | earlier versions of `CayleyDickson.lean` and `LeechSedenionFano.lean` |

Within `formal/` a syntactic audit of the 5 195 declarations found 1 175 whose
statement has no binder and whose proof is a single `rfl`/`decide`/`norm_num`
call, 255 closed numeral facts, and a large further group of `ring`-provable
identities over constants defined a few lines above them.  `lake build` did not
succeed at all.

## 2. Selection criteria

A module was kept when it carries at least one theorem that

1. quantifies over a free parameter (`n`, `D = 2^n`, a pair of indices, a field,
   an algebra) rather than a hard-coded numeral, **or** records a genuine finite
   classification (an exact diameter, an exact code distance, an exhaustive
   census); and
2. is proved by induction, descent, linear algebra, or a combinatorial argument —
   `decide` and `rfl` are acceptable as the last step of a reduction, not as the
   whole proof; and
3. is not a restatement of a result that already appears in another module.

A module that only supplies definitions used by a kept module was kept as a
definition module even when it proves nothing (for example
`Sovereign.Algebra.LeechSedenionFano`, which carries the concrete sedenion model,
and `Sovereign.Geometry.StiefelSpectrum`, which defines the Casimir eigenvalue).

## 3. What the library now looks like

```
Sovereign.lean                 -- root index
Sovereign/
  Algebra.lean        Algebra/        -- Cayley–Dickson doubling, zero divisors, property loss
  Combinatorics.lean  Combinatorics/  -- degree spectrum, associating triples, closed forms
  Graph.lean          Graph/          -- annihilation graph, spectral obstructions
  Geometry.lean       Geometry/       -- Stiefel frames, cubature, finite geometry
  Quantum.lean        Quantum/        -- CSS / subsystem codes, sponge permutation
  Fluid.lean          Fluid/          -- non-associative hydrodynamics
  NumberTheory.lean   NumberTheory/   -- ABC, Szpiro, effective bounds
  Physics.lean        Physics/        -- anomaly cancellation, finite consistency conditions
  Meta.lean           Meta/           -- self-audit, certificate soundness, proof-search engine
  Rewriting.lean      Rewriting/      -- non-associative rewriting tactic (tooling)
```

Module names follow `Sovereign.<Cluster>.<Module>`, so the Lake target is a single
glob:

```toml
[[lean_lib]]
name = "Sovereign"
globs = ["Sovereign", "Sovereign.+"]
```

Adding a module therefore never requires editing `lakefile.toml`; run
`python3 scripts/gen_indices.py` to refresh the cluster index modules.

| cluster | modules |
| --- | ---: |
| `Sovereign.Algebra` | 29 |
| `Sovereign.Meta` | 21 |
| `Sovereign.Geometry` | 17 |
| `Sovereign.Quantum` | 15 |
| `Sovereign.Combinatorics` | 14 |
| `Sovereign.Graph` | 14 |
| `Sovereign.Fluid` | 13 |
| `Sovereign.NumberTheory` | 8 |
| `Sovereign.Physics` | 5 |
| `Sovereign.Rewriting` | 3 |
| **total** | **139** |

After the consolidation the library holds 2 967 declarations (was 5 195 in `formal/`
alone, before counting `lee/`), of which 11 are closed numeral facts and all eleven
live in the two self-audit modules that study them.

`RequestProject/` is a second, independent library (Ramanujan's `τ`, Hecke
operators `T₂`/`T₃`, digital-root arithmetic, sieve and word graphs).  It was left
untouched by this pass and curated separately, under the same criteria: see
`docs/REQUESTPROJECT_CURATION.md`.

## 4. The surviving core

The headline results, by cluster.

**`Sovereign.Algebra`** — the twisted-XOR basis product law `e_a · e_b = ± e_{a⊕b}`
for every dimension `2^n` (`TowerBasis`); the cross-half annihilation criterion
`crossVec_mul_eq_zero_iff` and charge conservation in every dimension
(`TowerZeroDivisors`); the counts `(D−2)(D−4)` signed cross-half zero divisors,
`6D−8` non-zero-divisors, and the bijection between XOR charges and the points of
`PG(n−2, 𝔽₂)` (`CrossHalfUniversal`); the property-loss chain for *all* elements,
not just basis vectors (`CayleyDicksonTowerStrong`).

**`Sovereign.Combinatorics`** — the closed-form degree law
`|nonassocMiddles(m+r) i j| + 4 = 2^r · (|nonassocMiddles m i j| + 4)` and the
`assocNeg_xor_shiftDefect` identity behind it (`TowerDegreeClosedForm`); the
`O(n)` degree formula with its maximality and minimality criteria
(`TowerDegreeFormula`); `A(D) = D³/2 + 14D − 24` associating triples
(`AssociatingTriplesCount`); the coset-partition size spectrum `4 + 8k`
(`CosetPartitionSpectrum`).

**`Sovereign.Geometry`** — the exact cubature identity `Mᵀ M = 24 · I₂₁` and the
diagonalisation of the projected annihilation operator (`StiefelCubature`); the
census of the 168 frames (`StiefelFrameCensus`); integrality, monotonicity and the
Pell-family classification of spectral coincidences on `V₂(ℝ⁷)`
(`StiefelSpectrumStrong`).

**`Sovereign.Graph`** — non-pole sectors violate the Ramanujan bound while the
doubling pole satisfies it (`RamanujanDuality`); the Alon–Boppana bound is never
saturated, by a quadratic-residue obstruction mod 8 (`AlonBoppanaObstruction`);
the Hashimoto spectrum has a 146-dimensional neutral centre, so the discrete
geodesic flow is not Anosov (`GeodesicFlowObstruction`); every component has
diameter exactly 3 (`ComponentDiameter`).

**`Sovereign.Quantum`** — the CSS distance of the symmetric tower codes is exactly
2 (`QuantumCodeDistance`), the phenomenological threshold is identically zero
(`QuantumThresholdObstruction`), and the rate–distance product vanishes
(`RateDistanceProduct`); the one positive construction is the subsystem code whose
gauge generators are associator 2-cells (`AssociatorSubsystemCode`).

**`Sovereign.Fluid`** — vanishing of the 16-dimensional Lamb vector on the
zero-divisor manifold and positivity of the non-zero Dirichlet-to-Neumann
eigenvalues (`BoundaryCoupling`); a machine-checked contraction/ball-invariance
enclosure (`CoupledSingularity`, `IntervalEnclosure`); `Re_c(δ) = 4π/δ`
(`CriticalReynoldsNumber`); the Kraichnan–Kolmogorov interpolation
`α(δ) ∈ [5/3, 3]` (`EnstrophyCascade`).

**`Sovereign.NumberTheory`** — the `ε = 0` form of ABC is false, unconditionally
(`ABCEpsilonZero`); Mason–Stothers, the Fermat–Catalan and Brocard certifications,
and the Frey/Szpiro reduction chain (`ABCConjectureObstruction`, `SzpiroSharpness`).

**`Sovereign.Meta`** — `implication_from_theorem_iff`: once `p` is a theorem,
`(p → q) ↔ q`, so no finished theorem reduces an open problem; the annihilation
graph is bipartite and the `−8` "gap" is the extremal value forced by that sign
symmetry (`MillenniumImpactAudit`); certificate-by-predicate-name is unsound
(`ReasoningStoreAudit`).

## 5. What was removed

104 modules were deleted outright, and a further 147 individual declarations were
deleted from modules that survived.  The module removals fall into four groups.

* **Numeral certificates.**  Modules whose theorems are equalities between
  constants defined in the same file (`HigherTower`, `StiefelManifold`,
  `GaugeGeometry`, `ChingonSpectrum`, `KleinQuadric`-style tables,
  `TrigintaduonionSpectrum`, `TrigintaduonionCSS`, `TrigintaduonionLDPC`,
  `TowerPoleSpectrum`, `TowerPoleCSS`, `TowerCrownSpectrum`, `LatticeSurgery`,
  `SideChannelResistance`, `GNLCapacity`, `MonographTheorems`, `AuditGenerated`,
  `SectorSpectralStratification`, `HigherStiefelCurvature`, `HigherOrderQLDPC`,
  `LiePoissonIntegrator`, `UnifiedOrganismPipeline`, `TowerOrganismSystem`,
  `TowerSymplecticFlatness`, `TowerModularTensorCategories`, `GrandOpenProblems`,
  `HigherDimensionProverCampaign`, `AutonomousDiscovery`, `QuarticTowerSaturation`,
  `GossetPolytope`, `GossetMetricSyllogism`, `SignetOctadSemantics`,
  `SovereignSigma`, `RelationalTopologyChinese`, `GeometricCognitiveRuntime`,
  `PrimeOrganismDistribution`, `RamanujanBPComplexity`, `ExpanderMixingSharpness`,
  `SedenionFanoMHD`, `RamanujanTurbulence`, `SingleShotResilience`,
  `FlavorMixingObstruction`, `GaugeUnification`, `MillenniumFoundations`-style
  dimension counts).
* **`HYP-NNN` topic modules.**  About sixty modules named
  `Tower<Topic>` — `TowerTropicalBraids`, `TowerRotaBaxterHopf`,
  `TowerVeeringTriangulationsConvergence`, `TowerFarguesScholzeG2`,
  `TowerXiaoGenusTwoFibration`, and so on.  Each attaches a literature topic to a
  handful of `ring`-provable telescoping identities and `rfl` facts about locally
  defined numerals, closing with a `hypNNN_master_invariant` that conjoins them.
  None proves anything about the topic it is named after.
* **Grand-name modules.**  `YangMillsMassGap`, `GeometricLanglandsCompiler`,
  `NavierStokes3DRegularity`, `UniversalFaultTolerance`.  Earlier audits had
  already reclassified their "master theorems" as parameter arithmetic; the
  arithmetic is not used anywhere.
* **Duplicates.**  The whole `lee/` tree, `experiments/legacy_sovereign/`, the
  stale nested `formal/lakefile.lean`, the one-line `formal/check_ax.lean`, and
  `NonassocRing.Tactic`, a compatibility shim that re-declared the
  `nonassoc_ring` syntax already declared in `NonassocRewriter` (and therefore
  made that module fail to elaborate).

Two further edits resolved genuine duplication inside the surviving core.

* `chargeSector_regular_iff` was proved twice, in `TowerDegreeClosedForm` (for the
  predicate `IsRegularSector`, with no lower bound on `n`) and in
  `TowerSectorRegularity` (for `chargeSectorRegular`, assuming `3 ≤ n`).  The two
  modules had never been imported together, so the clash only surfaced once the
  library acquired a root.  The inductive version keeps its proof but is now called
  `chargeSectorRegular_iff_regularCharge`, since `regularSectorCharges_card` depends
  on it; its doc comment points at the general form.
* `SedenionStratification` compared the sedenion zero-divisor counts with the
  numerals `(D−2)(D−4)` and `6D − 8` at `D = 16`.  `CrossHalfUniversal` already
  proves those counts for every `D = 2^n` and bridges them to the concrete sedenion
  lists, so the two numeral comparisons were dropped.

The 147 declaration-level removals are the closed numeral identities inside kept
modules — `7 * 6 = 42`, `(4 : Nat) = 4`, `True`, `(2 : Nat) ^ 24 = 16777216`, and so
on — with two deliberate exceptions.  `Meta/ReasoningStoreAudit` and
`Meta/KernelSelfAudit` *study* such statements: their point is that a numeral
certificate cannot support the claim it is filed against, so their numeral theorems
are the subject matter and stay.

Nothing is lost: the deleted sources remain in the Git history at the commit
preceding the consolidation.

## 6. Conventions for new work

* Put a new module in the cluster directory it belongs to; the module name is
  `Sovereign.<Cluster>.<Module>` and must match the file path.
* State results over a parameter `n` or `D = 2^n` whenever the numeric case
  generalises.  The doubling-induction pattern of `TowerBasis` and
  `TowerDegreeClosedForm` is the house style.
* Do not add a theorem whose statement is an equality between two constants
  defined in the same file; `scripts/lean_theorem_audit.py` reports these.
* Eliminative results are first-class: name them for what they exclude
  (`AlonBoppanaObstruction`, `QuantumThresholdObstruction`) rather than for the
  claim they refute.
* Run `python3 scripts/gen_indices.py` after adding or deleting a module, then
  `lake build`.

## 7. Tooling

* `scripts/lean_theorem_audit.py <path>` — inventory the declarations of a tree
  and classify each as `numeral`, `defeval`, `trivial`, `definition` or `general`.
* `scripts/curation_manifest.py` — the keep-list used by the consolidation,
  together with a check that it is closed under the import relation.
* `scripts/gen_indices.py` — regenerate the cluster index modules and the root.
* `scripts/prune_numeral_theorems.py` — delete the closed numeral identities the audit
  flags, provided nothing else in the library refers to them; `--apply` writes.

## 8. Consequences outside the Lean sources

The Python tooling and the `tests/` suite referred to the old `formal/` paths.  Those
references were retargeted mechanically: file paths now point into `Sovereign/<Cluster>/`,
`lake --dir formal build <Mod>` became `lake build Sovereign.<Cluster>.<Mod>` run from the
repository root, and the fourteen test modules that existed only to check removed Lean
modules were deleted.  `scripts/lint_tautology_traps.py` now scans `Sovereign/` and
`RequestProject/` and reports no violations.  The Python suite itself could not be executed
in the environment used for the consolidation (no `pytest` installed), so these edits are
mechanical rather than test-verified.

Historical reports that described the old layout (sprint logs, refactor summaries, earlier
audits) were moved to `docs/history/` unchanged rather than rewritten.
