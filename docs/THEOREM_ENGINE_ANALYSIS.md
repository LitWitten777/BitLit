# Critical analysis of the automated theorem engine

This note reviews the pipeline that turns research questions into certified results in this
repository — its **input** (what the engine is fed and what it computes), its **reasoning**
(what it actually checks, in Python and in Lean) and its **output** (what it reports) — and
records the repairs made in this pass.  Every claim below was produced by running the code
in this repository; the commands are given so that each one can be re-checked.

## 1. What the engine is

```
   roadmap / hypotheses                 src/sedenion/research/roadmap.py, docs/RESEARCH_ROADMAP*.md
            │
            ▼
   computational workstreams  W1 … W26  src/sedenion/research/, scripts/research/
            │  (census + degree kernels re-stated in Python)
            ▼
   conjecture + experiment logs         logs/conjectures.jsonl, logs/experiment_log.jsonl
            │
            ▼
   Lean 4 / Mathlib certification       Sovereign/**, RequestProject/**
            │
            ▼
   audit + digests                      scripts/research/zero_token_theorem_auditor.py,
                                        logs/research/RESULTS.md, artifacts/*.json
```

The design is sound: conjecture computationally, log falsification criteria, certify in
Lean, then audit what was certified.  The defects found are all in the *joints* between
those stages — the places where one stage takes another's word for something.

## 2. Findings on the input stage

### F1 — Two Python transcriptions of one Lean definition, one of them wrong

`Sovereign/Combinatorics/TowerDegreeCensus.lean` defines

```
censusT 0 t     = if t = 0 then 42 else 0
censusT (q+1) e = 2 * censusT q (e/2) + (if e = 2^(q+1) - 1 then 6*(2^(q+3) - 1) else 0)   -- e odd
                = if e/2 < 2^q then 2 * censusT q (2^q - 1 - e/2) else 0                   -- e even
```

`src/sedenion/research/w1_census_moments.py` transcribes this correctly.
`scripts/research/cd_kernel.py` — described in `FILES_TOUCHED.md` as "dependency-free
transcription of the Lean definitions" — implemented a *different* recursion with base value
`1` instead of `42`, no parity split, no doubling factor and no degenerate top term.  Every
value it produced disagreed with Lean, starting at `censusT 0 0` (`1` versus `42`).

*Repaired.*  `cd_kernel.censusT` now matches the Lean definition; the superseded recursion is
kept as `_legacy_censusT` for provenance and the module's self-test now checks `M₀` and `M₁`
against the certified closed forms.

### F2 — Nothing ever compared Python against Lean

The two stages shared no data.  A transcription error in either direction could survive
indefinitely, and one did.

*Repaired.*  `scripts/audit/CensusVectors.lean` evaluates the Lean definitions themselves —
`censusT`, `censusMoment k` and `degreeCount` — and writes `artifacts/CENSUS_VECTORS.json`;
`tests/research/test_lean_python_agreement.py` fails if either Python kernel disagrees with
those vectors.  Run:

```
lake env lean scripts/audit/CensusVectors.lean
python3 tests/research/test_lean_python_agreement.py
```

Before the repair this test reported `FAIL test_cd_kernel_matches_lean`; it now passes.

### F3 — Conjecture records are not machine-linked to the formal artefacts

`logs/conjectures.jsonl` carries `conjecture_id`, a prose statement and a support count;
the roadmap carries a `formal_target` string naming a *file*.  Nothing names the Lean
declaration that settles a conjecture, so "verified" is a human judgement and cannot be
re-checked.  Recommended: record the fully qualified declaration name and have the audit
confirm that it exists in the compiled environment and is not a tautology (§4, §6).

## 3. Findings on the reasoning stage — the computational half

### F4 — Floating-point interpolation silently falsified every published closed form

`interpolate_polynomial` used `float`.  The moments reach `10³⁰` while a double carries 53
bits, and the true leading coefficients are `1/2, 11/30, 3/10, 1679/6510, 99/434` and
`2888981/14055090`.  The digest generator then formatted each coefficient with `f"{c:.0f}"`,
so `logs/research/RESULTS.md` published, for example,

```
* `M_1` → 24 + -14 * D + 0 * D^3
```

under the heading "Proposed closed forms (all checked at every computed point)".  The true
identity is `M₁ = D³/2 − 14 D + 24`; the published polynomial is not merely imprecise, it is
wrong at every point, and all six reported forms had this defect.

*Repaired.*  The interpolation is exact (`fractions.Fraction`), the digest prints exact
rational coefficients, and the reported polynomial is checked for equality — not within a
tolerance — at every computed level.

### F5 — The falsification criterion was dead code

W1 lists "the `D^(k+1)` coefficient does not vanish" as a falsification criterion.  The check
read

```python
vanishing = True
if len(coeffs) > expected_degree + 1:      # len(coeffs) == k+3 == expected_degree+1
    vanishing = abs(coeffs[expected_degree + 1]) < 1e-10
```

The guard is never true, so `vanishing` was hard-wired to `True` and the criterion was never
evaluated.  The degree bound was not tested either: fitting `k+3` points to a degree-`k+2`
polynomial assumes the conclusion.

*Repaired.*  The fit now uses `k+4` points, so the degree bound is falsifiable, and both the
degree bound and the vanishing of the `D^(k+1)` coefficient are tested exactly.  Both hold
for `k ≤ 6`.

### F6 — Replayed logs were reported as fresh passes

`run_all.py` recomputes W1, W3, W4 and W5; the remaining 22 workstreams are read from
`logs/research/*.json` written on an earlier day.  They were printed as `PASSED` in the
summary table and counted in "158 checks, 0 failures", and the exit status could not
distinguish "checked now" from "checked once".  The "Total runtime: 0.0s" line compounded
the impression.

*Repaired.*  Replayed workstreams are reported as `CACHED` (`CACHED_FAILED` when the stored
log has failures), the digest lists which workstreams ran and which were replayed together
with the timestamp of each stored log, and the runtime line says what it measures.

## 4. Findings on the reasoning stage — the formal half

The Lean development is genuinely `sorry`-free: the environment-level audit added in this
pass confirms that no theorem in either library depends on `sorryAx` or on any axiom outside
`propext`, `Classical.choice` and `Quot.sound`.  The weakness is elsewhere — in *what the
statements say*.

### F7 — Vacuous statements carrying load-bearing names

* `TowerDegreeMomentsGeneral.censusMoment_poly_exists` asserts
  `∃ p : Polynomial ℚ, p.natDegree ≤ k+3 ∧ p.coeff (k+2) = 0`.  Nothing connects `p` to the
  census, so `p = 0` is a witness for every `k`: the theorem is true of any project
  whatsoever.  `censusMoment_poly_law` has the same gap — it records the degree and the
  vanishing coefficient of hand-written polynomials, never that they compute the moments.
* `TowerDegreeMomentsUniform.vanishing_leading_coeff_k1_to_k5` quantifies over hard-coded
  rational functions ("if this explicit cubic equals `aD³+bD²+cD+d` then `b = 0`").  It is a
  true statement about literals, not about `censusMoment`, although the surrounding
  docstrings describe it as the abstract vanishing law.
* The new audit finds 12 further theorems whose statement is a syntactic tautology, among
  them `ZeroViscosityBoundary.op036_falsification_refuted : (0 : Nat) = 0 ∧ ¬((0:Nat) ≠ 0)`,
  `Helicity.op038_falsification_refuted`, `ZeroDivisorSignature.op053_falsification_refuted`,
  `Combinatorics.symmetry_k0 : mu0 = mu0`, and
  `TowerDegreeMomentsGeneratingFunction.intermediate_moments_subleading_zero`, whose
  conclusion is `∀ j, 1 ≤ j → j < k → (0 : ℚ) = 0`.  Three of these are conjuncts of
  "master resolution" theorems, so the vacuity propagates upward.

*Repaired for the moments.*  `Sovereign/Combinatorics/TowerDegreeMomentsPolynomial.lean` adds
the missing link: `polyCensusMoment0_eval … polyCensusMoment6_eval` prove
`pₖ.eval (2^(q+3)) = censusMoment k q` for every level, `censusMoment_poly_represented`
restates the existence claim with that clause included — so the zero polynomial is no longer
a witness — and `censusMoment_poly_unique` shows the representing polynomial is unique.  The
original statements are left in place, with a docstring caveat pointing at the strengthened
versions.  The remaining tautologies are listed in `artifacts/THEOREM_AUDIT.json` under
`flagged`.

### F8 — The auditor could not see what it claimed to audit

`scripts/research/zero_token_theorem_auditor.py` is a regular-expression scan of source text.
Concretely:

* it pointed at an absolute path from another machine (`/data/mind/cognition/sov/...`), so in
  this repository it audited nothing and divided by zero;
* it parses by text, so it misses 193 theorems that exist in the environment and lists 45
  names that are not theorems at all;
* it documents an `[EXTERNAL_AXIOM]` category that is never produced — no axiom analysis is
  performed, so a `sorry` reached *through* another declaration, or an added axiom, is
  invisible;
* it equates tactic with content: 73 theorems it labels `TAUTOLOGY_RFL`/`TAUTOLOGY_DECIDE`
  are general quantified statements about the project's own definitions, while it labels as
  `SUBSTANTIVE_TACTIC` every one of the 12 real tautologies above, because they are closed
  with `decide` inside a longer proof or with `intros; rfl`;
* it returns 0 regardless of what it finds, so it cannot gate anything.

*Replaced.*  `scripts/audit/TheoremAudit.lean` audits the compiled environment:

```
lake env lean scripts/audit/TheoremAudit.lean      # ≈2 min, writes artifacts/THEOREM_AUDIT.json
```

For every theorem the project adds to the environment it records the axioms the proof really
depends on, how many variables the statement quantifies over, and whether the statement
mentions any definition of the project at all, and it classifies accordingly:

| category | 3292 hand-written theorems |
| --- | --- |
| `SORRY` | 0 |
| `NONSTANDARD_AXIOM` | 0 |
| `TAUTOLOGY` | 12 (0.3%) |
| `GROUND_NO_PROJECT_CONTENT` — closed statement mentioning no project definition | 53 (1.6%) |
| `GROUND_PROJECT` — closed statement about project definitions (one fixed dimension) | 1276 (38.7%) |
| `GENERAL_NO_PROJECT_CONTENT` — quantified, but about nothing of the project | 304 (9.2%) |
| `GENERAL` — quantified statement about the development | 1647 (50.0%) |

A further 493 declarations are generated by Lean itself (equation, injectivity and `sizeOf`
lemmas) and are counted separately rather than inflating the total, as they did in the old
report.  The run exits non-zero on `SORRY` or `NONSTANDARD_AXIOM`, so it is usable as a gate,
and the axiom closure is memoised, which is what keeps a whole-library audit at two minutes
rather than seven.

The report also lists the 51 modules that contain no `GENERAL` theorem at all — every claim
in them is either a closed instance or a generic fact.  That list is the most useful output
of the audit: it is where names promise more than statements deliver.

## 5. Findings on the output stage

* **A conjecture was published as a closed form and never certified.**  `M₆` appeared in
  `logs/research/RESULTS.md` as a "proposed closed form", in rounded — hence incorrect —
  coefficients.  It is now a theorem: `Sovereign.censusMoment6_formula` and
  `Sovereign.degreeCount_sixth_moment` prove

  ```
  14055090 · Σ v⁶ · (multiplicity of v)
      = 2888981 D⁸ − 992751380 D⁶ + 13010997600 D⁵ − 76669578944 D⁴
        + 256178304000 D³ − 541086161920 D² + 727509565440 D − 466943066112
  ```

  for every dimension `D = 2ⁿ ≥ 8`, with the `D⁷` coefficient vanishing as the pattern
  predicts.  The sixth moment is the first even moment past the splitting lemma's reach, so
  the module also extends that lemma to weights of degree six.
* **The per-order duplication is now stated once.**  Each moment used to require its own
  copy of the splitting lemma and its own hand-expanded doubling step; the coefficients were
  transcribed by hand, which is precisely where a slip becomes a wrong theorem rather than a
  failed proof.  `Sovereign.censusWeighted_split` and `Sovereign.censusMoment_succ_coeff`
  state both steps for every order, and `Sovereign.censusMoment_succ_two` shows the
  hand-derived recurrence following from the general one.
* **Digests should separate "computed" from "certified".**  `RESULTS.md` mixes both.  The
  new `polynomial_formula`, `degree_bound_check` and `reproduces_every_computed_point` fields
  in `logs/research/w1.json` make the computational status explicit; the certified status is
  exactly the set of Lean theorems, and the audit report now enumerates those.

## 6. What to do next, in priority order

1. **Gate the pipeline on the audit.**  `scripts/audit/run_all_checks.sh` runs the build, the
   audit, the vector export, the differential test and the workstreams, and fails on the
   first problem.  Adding it to the acceptance criteria makes "0 sorry, 0 non-standard
   axioms" a checked property rather than a claim.
2. **Name the formal target of every conjecture.**  Put the fully qualified Lean declaration
   in `logs/conjectures.jsonl`, and extend the audit to verify that it exists, is not
   flagged, and is `GENERAL`.  This closes the last unchecked joint in the pipeline.
3. **Work through the 51 modules with no general theorem.**  For each, either strengthen the
   statements to quantify over the tower, or rename them to what they are (a computation in
   one dimension).  The three `*_falsification_refuted` tautologies should be removed from
   the "master" conjunctions that cite them, since they contribute nothing.
4. **Finish the uniform moment law.**  Half of this is now done:
   `TowerDegreeMomentsWeights` states the two per-order steps once for every order —
   `censusWeighted_split` for weights of arbitrary degree and `censusMoment_succ_coeff` for
   the doubling law, whose coefficients are read off the kernel polynomial instead of being
   expanded by hand (`censusMoment_succ_two` recovers the order-two recurrence as an
   instance).  What remains is the polynomiality statement itself:
   `censusMoment_poly_represented` is still proved case by case for `k ≤ 6`.  Solving the
   recurrence `p(2D) = 2^(k+1) p(D) + P_k(D)` coefficientwise shows that the vanishing of the
   `D^(k+1)` coefficient is exactly the solvability condition, which is the shape an
   induction on `k` should take.
5. **Randomise the differential test.**  The exported vectors cover `q ≤ 8`; property-based
   sampling of larger `q` against the Lean-certified closed forms would catch drift in the
   regime where only the Python kernels are used.

## 7. Files added or changed in this pass

| File | Change |
| --- | --- |
| `Sovereign/Combinatorics/TowerDegreeMomentsSixth.lean` | added — sixth moment: splitting lemma of degree six, doubling law, closed form, census form |
| `Sovereign/Combinatorics/TowerDegreeMomentsPolynomial.lean` | added — representation theorems `pₖ.eval (2^(q+3)) = censusMoment k q`, the non-vacuous polynomial law, uniqueness |
| `Sovereign/Combinatorics/TowerDegreeMomentsWeights.lean` | added — arbitrary-degree splitting lemma, the doubling kernel as a polynomial, the doubling law for every order |
| `Sovereign/Combinatorics/TowerDegreeMomentsGeneral.lean` | docstring caveat on the vacuous existence statement |
| `Sovereign/Combinatorics.lean` | cluster index regenerated |
| `scripts/audit/TheoremAudit.lean` | added — environment-level audit, CI gate |
| `scripts/audit/CensusVectors.lean` | added — ground-truth vectors from the Lean definitions |
| `scripts/audit/run_all_checks.sh` | added — end-to-end gate |
| `tests/research/test_lean_python_agreement.py` | added — Lean/Python differential test |
| `scripts/research/cd_kernel.py` | corrected transcription, self-test against certified formulas |
| `src/sedenion/research/w1_census_moments.py` | exact rational interpolation, real degree and vanishing checks, exact verification at every point |
| `scripts/research/run_all.py` | exact closed forms in the digest, `CACHED` status, honest runtime and exit status |
| `scripts/research/zero_token_theorem_auditor.py` | paths made relative, division-by-zero guard, superseded-by note |
| `artifacts/THEOREM_AUDIT.json`, `artifacts/CENSUS_VECTORS.json` | generated reports |
