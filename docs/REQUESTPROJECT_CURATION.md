# Curation of the `RequestProject` library

`docs/LIBRARY_CURATION.md` records the consolidation of the Cayley–Dickson development into
`Sovereign/`.  The second library, `RequestProject/` (modular forms, Hecke operators, digital
roots), was left untouched by that pass; this note records its curation, done with the same
criteria.

## 1. Selection criteria

Unchanged from `docs/LIBRARY_CURATION.md`:

1. a kept theorem quantifies over a free parameter (a base `b`, a divisor `d`, a set of primes,
   a ring, a weight, an arbitrary coefficient sequence) **or** records a genuine finite
   classification or computation (the orbits of doubling on `ZMod 9`, the first thirty values
   of `τ`, the Hecke image of `Δ` on a certified range);
2. it is proved by induction, descent, analysis or a combinatorial argument — `decide` is
   acceptable as the evaluation step of a computation, not as the whole content of a statement;
3. it is not a restatement of a result proved elsewhere in the library.

## 2. Starting state

| module | declarations |
| --- | ---: |
| `Tesla369`, `BaseGeneral`, `FibVortex` | 71 |
| `Sieve23`, `SieveGeneral` | 26 |
| `Hecke23`, `HeckeGeneral`, `HeckeWords` | 52 |
| `DeltaGraph`, `DeltaModular`, `DeltaWordGraphs`, `VerticalWalls` | 141 |
| `T2vsT3`, `T2vsT3Delta` | 65 |
| `Main` | 0 (a file of `set_option`s, imported by nothing) |

355 declarations in 15 flat modules, with base-ten results proved independently of their
base-`b` generalisations, three distinct `tau_one`/`Delta` naming schemes, and one module
(`Main`) with no content.

## 3. What the library looks like now

```
RequestProject.lean                    -- root index
RequestProject/
  DigitalRoot.lean    DigitalRoot/     -- Basic, Decimal, Fibonacci
  Sieve.lean          Sieve/           -- Legendre, TwoThree
  Hecke.lean          Hecke/           -- System, Words
  Delta.lean          Delta/           -- Coefficients, QExpansion, Modularity,
                                       --   HeckeImages, PhaseWalls, WordComparison
```

Module names follow `RequestProject.<Cluster>.<Module>` and each cluster has an index module,
exactly as in `Sovereign/`; the Lake target is the single glob
`globs = ["RequestProject", "RequestProject.+"]`, so adding a module never means editing
`lakefile.toml`.  One namespace per cluster: `DigitalRoot`, `Sieve`, `Hecke`, `Delta` (with
`Delta.Walls` for the phase-wall theory).  272 declarations remain, and `lake build
RequestProject` completes with no `sorry` and only the standard kernel axioms.

## 4. Consolidation

* **Base ten is now a corollary.**  `DigitalRoot.digitalRoot` is *defined* as
  `digitalRootBase 10`, so `digitalRoot_of_pos`, `digitalRoot_pos`, `digitalRoot_le_nine`,
  `digitalRoot_modEq`, `digitalRoot_congr`, `digitalRoot_digitsSum`, `digitalRoot_add`,
  `digitalRoot_mul` and `digitalRoot_two_pow_notMem_trinity` are one-line specialisations of the
  base-`b` theorems instead of separate proofs, and `trinity = trinityBase 10 3` is recorded
  once (`trinity_eq_trinityBase`).
* **One Hecke module.**  `Hecke23` and `HeckeGeneral` are merged into `Hecke.System`; the
  `{2,3}`-specific `Smooth3`, `Smooth3_eq` and `eq_on_Smooth3` are dropped in favour of the
  general `Smooth S` and `eq_on_Smooth`, with the single corollary `eq_on_smooth_two_three`.
  The eigenvalue formulas `a_4`, `a_6`, `a_9`, `a_12`, `a_27` now all live there.
* **One `Δ`.**  `DeltaModular.Delta` (the eta product as an analytic function) is now
  `Delta.form`, in the same namespace as `Delta.tau`; the duplicated `VerticalWalls.tau_one`
  is gone, the `q`-expansion machinery (`qParam`, `approx`) lives in `Delta.QExpansion`, and the
  trinity bridge `digitalRoot_natAbs_mem_trinity_iff` moved to `DigitalRoot.Decimal`, where its
  companion `mem_trinity_of_three_dvd` replaces the local copy `coeff_mem_trinity`.
* **Naming.**  `deltaCoeffs → coeffs`, `deltaApprox → approx`, `tauTable_eq_deltaCoeffs →
  tauTable_eq_coeffs`, `Delta_* → form_*`, `DeltaH → formH`.

## 5. What was removed, and why

Net change: 355 → 272 declarations (83 fewer; the remaining differences are renames).

* **`T2vsT3` and `T2vsT3Delta` (65 declarations → 11).**  Both files compare
  `t₂ = τ(2)·τ = -24 τ` with `t₃ = τ(3)·τ = 252 τ` on `1 ≤ m ≤ 20`.  Since the two sequences are
  the *same* sequence rescaled, every one of the six "panels" (product, difference, quotient,
  power, remainder, and the six delta diagrams built from them) is arithmetic with the two
  constants: `diffT_eq`, `modT_eq`, `quotT_eq`, `powT_pos`, `powLogCoeff_*`, `panelA_*`…
  `panelF_*`, `comparison_table`, and the trinity corollaries `prodT_mem_trinity`,
  `diffT_mem_trinity`, `modT_mem_trinity` are all immediate once `t₂` and `t₃` are known.  The
  surviving module `Delta.WordComparison` keeps the three statements that are actually about the
  pair — `prodT_neg` (the two are anti-parallel), `ratioT_eq` (the ratio is the constant
  `τ(2)/τ(3) = -2/21`) and `antiparallel` (`21 f₂ = -2 f₃` as functions) — plus the
  supporting `t2_eq`, `t3_eq`, `tauT_ne_zero`, `abs_ratio_21_2`.
* **Closed numeral restatements.**  `Sieve23.sieved_eq`, `survivors_eq`, `sieved_card`,
  `survivors_card`, `survivors_symmetric`, `totient_six`, `dvd_two_or_three_iff` — the residues
  mod six, listed by `decide`; and `Sieve23.card_sieved_range`, which is
  `Sieve.card_sieved_range` at `S = {2,3}` (kept as `Sieve.two_three`).
* **Trivial restatements of the trinity.**  `trinity_generates_nat` (an `omega` goal),
  `three_generates` and `six_nine_generates` (immediate from `trinity_generates`),
  `trinity_residues`, `trinity_zmod`, `trinity_doubling` (three numerals), `vortex_orbit_cards`
  (the cardinalities of orbits already listed elementwise), `digitalRoot_mem_range`,
  `Hecke23.trinity_smooth`, `digitalRoot_fib_cycle_sum`.
* **Duplicated Hecke words.**  `eigen_word_two`, `eigen_word_three`, `eigen_polynomial_two`,
  `eigen_polynomial_three` — four `by simp` proofs of two statements.
* **Decorative computations.**  `DeltaGraph.tau_word_values` (the five multipliers, also given
  by `Delta.word_multipliers`), `DeltaGraph.digitalRoot_tau_table` and
  `DeltaWordGraphs.word_abs_multipliers_strictMono` (the colouring and the ordering of five
  literals).
* **`Main.lean`**, a file of `set_option`s that no module imported and that therefore affected
  nothing.

Nothing that was removed is used by what remains; `lake build RequestProject` is green.

## 6. Retargeting

Module names in the Python tooling and in `data/theorem_provenance.json` were updated to the new
paths (`RequestProject.DeltaGraph.tau_congr_mod_27 →
RequestProject.Delta.Coefficients.tau_congr_mod_27`, and so on), including the two claims that
cite the `T₂`/`T₃` comparison, which now point at `RequestProject.Delta.WordComparison`.
