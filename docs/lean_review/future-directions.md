# Embedded future directions and unresolved interfaces

The lexical scan matched **236 comment blocks in 181 distinct files**. Full matched comments are retained below, with line numbers and byte-identity IDs. This is a retrieval ledger, not an endorsement of a proposed theorem or a claim that every note is still current.

Search terms: TODO, FIXME, future, roadmap, next step, not yet, open problem/question, remaining, further work, would require, could be, to be proved/implemented, research direction, unresolved, unproved. Nested block and line comments are scanned. Notes using other wording can be missed; **every extracted comment**, matched or not, is preserved in `source-index.json`. Consecutive line comments may appear as separate entries.

## Corrections that must travel with the notes

- **IFS** — TowerDegreeIFSCorrection already rejects the proposed half-scale IFS; use the actual recurrence and density, not the old plan.
- **Reasoning cycles** — Organism/Cycles corrects the associator blind spot and the confusion between undirected H¹ and directed circular premises.
- **HRT** — CanonicalOperatorFormulas discharges the Zak-side operator formulas. ConditionalDossierCertification supersedes old orbit-partition/discrepancy proposals and exposes a strong witness-producing reduction; the unconditional headline remains admitted.
- **Torus control** — GateReachability and ToricTranslation already prove important expressiveness obstructions.
- **Scope annotations** — existing truth-in-labelling comments are evidence about intended limits, not proof that all surrounding prose is correct. Quantification/no-real-number counts are not semantic novelty criteria.

## Matched source comments

### `Forensics/Inert/JohnDeeTextAudit.lean`

Content ID `1c56cb33f7737d83`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L42**

````text
/-!
# Inert forensics: audit of the private text `john-dee.md` ("UFT4 Ω" posts)

**Status: inert forensics** (Lake library `QBXForensics`, module
`QBX.Forensics.Inert.JohnDeeTextAudit`).  This is a *refutation* of claims in a private document
about physics and numerology, not a result about mathematics: nothing imports it, it is not
part of the headline index `QBX.Forensics`, and its registry row (H-179) is filed in the
forensics tier, not counted among the proved results.  Under the forensics policy
(`QBX/Forensics/POLICY.md`) it is not extended unless the source document gains a buyer or a
collaborator.

`john-dee.md` contains two posts: a "structural decryption" of the John Dee manuscripts and a
"topological derivation" of the fine-structure constant.  Almost everything in them is
narrative without a checkable statement.  This file checks the statements that *are* exact.

**Refuted.**
* `knotIndex_one`, `knotIndex_ne_137`: the "discrete knotting index"
  `N = 2·(6n − 1) + 2⁷ + 1` is `139` at `n = 1`, not `137` (the text sets `2·(6·1 − 1) = 8`;
  it is `10`), and **no** integer `n` gives `137`.
* `deltaSlip_bounds`: the "Delta-slip" `Δ = (1 / (2π φ²)) · (1 − 1/√5)` lies between `0.0336`
  and `0.0337`; the text's value `0.018451` is wrong by a factor of about `1.8`.
* `alpha_formula_with_true_delta`: with the true `Δ` the master formula
  `α⁻¹ = 137 + 2Δ − Δ²/π` gives more than `137.066`, against the measured `137.035999…`.
* `alpha_formula_misses_codata`: even with the text's own `Δ = 0.018451` the formula gives
  `137.0368…`, which the text itself admits is not the CODATA value; the remaining gap is
  attributed to an unspecified "tensor trace", i.e. the formula is fitted, not derived.
* `heptagon_repeats`: rotation by `360°/7` is periodic — after 7 steps it is the identity
  (a primitive 7th root of unity) — so it cannot "force an infinite, non-terminating loop".
* `xor_band_passes_noise`: XOR with a fixed band does not remove noise: two inputs that differ
  by non-zero noise still differ after the band, by exactly the same noise.

**What survives as an engineering idea.**  The "sequential-to-spatial collapse" (a linear
character stream laid out on a grid) is a chart decomposition of the text; its exact form is
the atlas theorem `QBX.Formal.TextManifold.windows_flatten_atlas`.  Nothing else in the two
posts gives a checkable statement.
-/
````

### `Formal/AddressTorusLedger.lean`

Content ID `5f3db25b7f1b4ebc`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L29**

````text
/-!
# F-5 on the address graph (WS9 roadmap step 8, part (b))

`TorusLedgerSectors.lean` (W5, finding F-5) is stated on the toric-code lattice `Edge m`.
Through the edge correspondence of `ToricAddressEdges.lean` (W7) it transfers to the address
graph `T²_m = addrGraph 0 2 (m, m)` itself.

A `ℤ/2` ledger on the address graph assigns a transport `ℓ e ∈ ℤ/2` to every unordered pair of
addresses (only adjacent pairs matter). It is pure gauge (`AddrPureGauge`) if there are address
potentials `p` with `ℓ s(a, b) = p a + p b` for every edge `a — b`.

* `addrPureGauge_iff_toric`: for `m ≠ 1`, `ℓ` is pure gauge on the address graph iff its pull-back
  `ℓ ∘ toricEdge` to the toric-code lattice is pure gauge;
* `addrPureGauge_iff`: **F-5 on addresses** — `ℓ` is pure gauge iff it is flat on every face and
  trivial around both non-contractible cycles;
* `exists_addr_faceFlat_not_pureGauge`: the two cycle bits are independent of the face checks —
  for `m ≥ 3` there is a face-flat ledger on the address graph that is not pure gauge;
* `toricEdge_transEdge`: **F-4 on addresses** — the lattice translation `transEdge s t` of
  `ToricTranslation.lean` (W4: it acts trivially on the logical sectors) is exactly the torus
  shift gate `shiftGate (s, t)` acting on address-graph edges.
-/
````

### `Formal/Agents/Delegation.lean`

Content ID `cafc6f2cb55c7f24`; 1 byte-identical path(s); statements/comments triaged; proof-body review pending.

**L7–L33**

````text
/-!
# The task-delegation scheduler of the QBX agent layer

`QBX/agents/scripts/delegate.py` turns a task into role-owned subtasks and runs them in
**waves**: every wave is a set of subtasks that may run at the same time.  This file is the Lean
model of its scheduler (`schedule` in the script, which follows the definitions below line by
line) and proves the properties the orchestration rules
(`agents/docs/orchestration_overview.md`, `multi_agent_topology.md`) ask for.

The model is generic: a subtask is any `α` with an identifier `key`, a list of prerequisite
identifiers `deps`, and a Boolean `conflict` relation (in the script: same role, or overlapping
write sets).  `cap` is `parallelism.max_concurrent_agents` from `agent_manifest.yaml`.

One round (`pick`) scans the remaining subtasks in order and adds a subtask to the wave when all
its prerequisites are done, the wave has fewer than `cap` members and the subtask conflicts with
no member already in the wave.  `rounds` repeats this until a round adds nothing.

* `schedule_waves_bounded` — every wave has at most `cap` subtasks;
* `schedule_waves_compatible` — no two subtasks of a wave conflict (so with the script's
  relation: no two share a role, and their write sets are disjoint);
* `schedule_deps_earlier` — every prerequisite of a scheduled subtask finished in an earlier wave;
* `schedule_perm` — every subtask is either scheduled exactly once or left over;
* `schedule_leftover_blocked` — with `0 < cap`, a left-over subtask is waiting on a prerequisite
  that never finished: the scheduler gives up on no subtask that could still run;
* `schedule_complete` — if the prerequisites are well founded (every prerequisite is a subtask of
  strictly smaller rank), nothing is left over.
-/
````

### `Formal/Agents/Organism.lean`

Content ID `e3618ab511509321`; 1 byte-identical path(s); full file source review; see R14; not build-verified.

**L9–L49**

````text
/-!
# The merkaba–tower organism: the orchestration loop of the QBX agent layer

`QBX/agents/scripts/organism.py` is the control loop that sits above the Orchestrator's
scheduler (`delegate.py`, modelled in `Delegation.lean`).  It keeps a list of open
**obligations** (an unproved `sorry`, a registry warning, an ownership error, a to-do from
`project_state.json`, …) and turns them into verified results by alternating two phases:

* **generate** (even clock): take the obligations whose *tower level* is at most the current
  capability level and that are ready, and dispatch one wave of them to role agents with the
  scheduler's round `Delegation.pick` (at most `cap` agents, no two in conflict);
* **verify** (odd clock): an independent check (`verify t o`: the Lean build, the registry
  check, the ownership audit, …) runs on every obligation of the wave; the accepted ones are
  moved to `done`, the others stay open.

If the generate phase finds nothing to dispatch, the capability level is raised by one (the
*tower*: level `k` admits work of level `≤ k`, up to `maxLevel`; levels above `maxLevel` need a
human).  The loop stops when nothing is open or when `window` verify phases in a row accepted
nothing; the plateau counter is the State-of-Thought one-counter automaton
`Sovereign.Organism.feed` of `StoppingCore.lean`.

The two phases are the two tetrahedra of the merkaba: the organism's clock walks the Gray code
of the cube `Q₃`, and the generate phase is exactly the time spent on the even tetrahedron
(`merkaba_phase`).  So every tick crosses from one tetrahedron to the other, and nothing is
accepted in the phase that produced it.

Main results (for any obligations, any verifier and any parameters):

* `run_conserves` — open and done obligations together are always a permutation of the input:
  nothing is lost or invented;
* `run_sound` — every done obligation was accepted by the verifier at an odd (verify) clock,
  and its level is at most `maxLevel`;
* `run_topo` — `done` is in dependency order: every prerequisite of a done obligation is the
  key of an obligation done before it;
* `run_batch` — every dispatched wave has at most `cap` members, no two in conflict, all ready,
  open and within the capability level;
* `run_halts` — the loop halts within `2 (n (window + 1) + window) + 1` ticks, `n` the number
  of obligations;
* `run_complete` — with an honest verifier, levels `≤ maxLevel`, well-founded prerequisites,
  `0 < cap` and `maxLevel - cap₀ < window`, the loop halts with nothing open.
-/
````

### `Formal/BraidTrace.lean`

Content ID `b28289e7c96360e8`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L65–L65**

````text
/-- `_reduce_once`: the rule and position of the next step, or `none` at a fixed point. -/
````

### `Formal/JLN/ConnesSkeleton.lean`

Content ID `76320c92c5db0b5a`; 1 byte-identical path(s); statements/comments triaged; proof-body review pending.

**L7–L36**

````text
/-!
# The axiom package of the claimed proof of Connes' rigidity is equivalent to the conjecture

Source: *Connes’ Rigidity Conjecture: Disproof of the Counterexamples and Proof of the Theorem*
(J. L. Nielsen, `QBX/docs/design/`), Appendix §B, `ConnesAppendix.lean`.

That appendix declares opaque objects (`VNAlg`, `L`, `Crossed`, `Tensor`, `VNIso`, `VNHom`,
`IsICC`, `HasPropertyT`), two opaque operations (`twistedComult`, `classify`) and four
propositional axioms (`not_degenerateI`, `not_degenerateII`, `rigid_d2_injective`,
`rigid_d2_surjective`), and derives `connes_rigidity` from them.  The appendix itself says the
part is "a proof skeleton" in which "no operator algebra is verified".

This file makes the status of the skeleton exact.  The objects the conjecture is *about* —
`L`, `VNIso`, `IsICC`, `HasPropertyT` (together with `Crossed`, `Tensor`) — form a
`SkeletonBase`.  The remaining declarations form `SkeletonAxioms B`.  Then:

* `connes_of_skeletonAxioms` — the axioms imply the conjecture for `B` (this is the appendix's
  `connes_rigidity`, with Mathlib's `Group` and `MonoidHom` in place of the hand-rolled ones);
* `skeletonAxioms_of_connes` — conversely, **whenever the conjecture holds for `B`, all the
  remaining axioms can be satisfied** (with `VNHom` a one-point type and `classify` returning a
  bijection supplied by the conjecture);
* `skeletonAxioms_iff_connes` — so the axiom package is satisfiable over `B` exactly when the
  conjecture holds over `B`.

In other words the ten axioms carry precisely the content of the conjecture, no more and no
less: the formal file certifies the case analysis, and the mathematical burden sits entirely in
`rigid_d2_surjective` together with `not_degenerateI/II`.  This does not say the paper's argument
is wrong; it says the Lean appendix is not evidence for it beyond the cited theorems.  (The
universes of the groups and of the algebra objects are kept arbitrary.)
-/
````

**L73–L74**

````text
/-- The remaining declarations of the appendix (`VNHom`, `twistedComult`, `classify` and the four
propositional axioms), over a fixed base `B`. -/
````

**L139–L140**

````text
/-- **Converse.**  If the conjecture holds for `B`, every remaining axiom of the appendix can be
satisfied over `B`. -/
````

**L153–L155**

````text
/-- **The axiom package is equivalent to the conjecture.**  Over any interpretation of the
objects the conjecture is about, the appendix's remaining axioms are satisfiable iff Connes'
rigidity conjecture holds for that interpretation. -/
````

### `Formal/JLN/LambdaIrreducibilityAudit.lean`

Content ID `a69fd4698668e09c`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L52**

````text
/-!
# Audit of the Lambda Irreducibility Theorem (Riemann Hypothesis paper, Thm. 1.6.1)

Source: J. L. Nielsen's Riemann Hypothesis paper, Definitions 1.4.3, 1.5.3, 1.5.4 and Theorem
1.6.1 (see `todo.md`).  Two paradigms `L` (linear) and `C` (curved) each come with a class of
models; a *translation pair* `(T_{L→C}, T_{C→L})` gives round-trip operators
`R_L = T_{C→L} ∘ T_{L→C}` and `R_C = T_{L→C} ∘ T_{C→L}`.  The paper defines

* the **Λ-obstruction** `Λ_P(S) := S_P △ R_P(S)_P`, the models of paradigm `P` on which `S` and
  its round trip disagree (Def. 1.5.3);
* `S` is **Λ-irreducible** if `Λ_L(S) ≠ ∅` and `Λ_C(T_{L→C}(S)) ≠ ∅` (Def. 1.5.4);

and claims (Thm. 1.6.1): *if `S` is Λ-irreducible then `ZFC ⊬ S` and `ZFC ⊬ ¬S`.*

Everything is stated for an arbitrary *satisfaction system* — a type of sentences, a type of
models and a satisfaction relation `sat` — and then instantiated with Mathlib's first-order logic
(`FO.*`).  Provability over a theory is modelled semantically, as truth in all its models; for
first-order theories this is equivalent to derivability by Gödel's completeness theorem (cited,
not formalised here).

## Results

* `obstruction_eq_symmDiff`: `obstruction` is Def. 1.5.3 verbatim (`S_P △ R_P(S)_P`).
* **What the argument actually proves** (`obstruction_eq_empty_of_provable`,
  `independent_of_irreducible`): *if the round trip `R_L` sends sentences valid on the
  `L`-paradigm to valid ones, and refuted ones to refuted ones*, then Λ-irreducibility gives
  independence.  This is a hypothesis about the **translation pair**, not about ZFC.
* **Vacuity for sound pairs** (`not_irreducible_of_sound`): if the pair is semantically
  round-trip sound on the `L`-paradigm (the condition the paper derives for any translation that a
  ZFC proof would "induce"), then *no* sentence is Λ-irreducible.  So on the paper's own reading
  the hypothesis of Thm. 1.6.1 can be satisfied only by pairs the proof does not talk about.
* **The theorem is false as stated** (`irreducible_idNeg`, `lambdaIrreducibility_false`): for the
  pair `(id, ¬)` *every* sentence is Λ-irreducible as soon as both paradigms have a model, provable
  sentences included.  `FO.lambdaIrreducibility_false` instantiates this for every first-order
  theory with a model (in particular for ZFC, if ZFC is consistent).
* **Irreducibility is a property of the pair, not of the sentence**
  (`irreducibility_depends_on_pair`): the same provable sentence is Λ-irreducible for one pair
  and not for another (the identity pair), while provability does not mention any pair.
* **ZFC needs no translation** (`provable_of_equiv`, `FO.provable_and_irreducible`): if the
  theory proves `S_C` and proves `S_L ↔ S_C`, it proves `S_L` directly — and this is compatible
  with `S_L` being Λ-irreducible for some pair.  This is the critique's main point: RH_L and RH_C
  are both sentences of the one theory, and their equivalence is a theorem of that theory.
* **Condition (3) of Def. 1.4.3 is empty for syntactic translations**
  (`FO.roundTrip_elementary_invariant`): truth of *any* sentence, in particular of `R(S)` for any
  map `R` on sentences, is preserved by elementary embeddings.
-/
````

### `Formal/JLN/LambdaPlusPlusAudit.lean`

Content ID `52be3ea185966938`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L52**

````text
/-!
# Audit of the `Λ⁺⁺` invariant (Yang–Mills paper, Def. 4.19)

Source: J. L. Nielsen's Yang–Mills paper, Definition 4.19, Theorem 6.11 and the "Path 1" chain
(see `todo.md`).  For a family of admissible encodings `E`, a generating set of loops `Γ`, loop
holonomies `H_{γ,E} ∈ G`, a conjugation-invariant defect functional `Δ` and a local defect scale
`τ(a) > 0` (with `τ(a) ∼ a⁴`), the paper defines

  `Λ⁺⁺(a) := inf_E sup_γ Δ(H_{γ,E}) / τ(a)`

and claims `Λ⁺⁺(a) ≥ ε(G) > 0` uniformly for small `a`.

## What is checked here

* `lambdaPP` is Definition 4.19, verbatim, for an arbitrary group `G`.
* **The correct part** (`worstDefect_conj`, `lambdaPP_gauge_orbit`): since `Δ` is
  conjugation-invariant, a re-encoding that acts on the loop holonomies by conjugation (a gauge
  transformation) cannot change the worst-case normalised defect.  On a single gauge orbit the
  infimum over encodings is attained by every encoding.  So "no admissible encoding can flatten the
  holonomy" holds for gauge re-encodings, and it holds trivially.
* **The gap** — uniformity in `a` is the whole content, and it is a statement about the coupling.
  In the one-plaquette `SU(2)` model (`modelLambda`), the plaquette holonomy at lattice scale `a`
  and effective coupling `κ` is the torus element `diag(e^{i a²κ}, e^{-i a²κ})`, the defect is the
  paper's `Δ(U) = 1 - ½ Re tr U` (`su2Defect`, conjugation-invariant by `su2Defect_conj`), the
  encodings are all `SU(2)` gauge transformations, and `τ(a) = a⁴`.  Then
  (`modelLambda_eq`) `Λ⁺⁺(a) = (1 - cos(a²κ)) / a⁴`, and
  - `modelLambda_le`: `Λ⁺⁺(a) ≤ κ² / 2`;
  - `modelLambda_ge`: `Λ⁺⁺(a) ≥ (2/π²) κ²` as long as `a²|κ| ≤ π`.

  So `Λ⁺⁺(a)` is pinned between two constant multiples of `κ(a)²`:
  - `uniform_bound_iff`: **a uniform bound `Λ⁺⁺(a) ≥ ε > 0` for `a ∈ (0, a₀)` holds iff the
    effective coupling is bounded away from zero on `(0, a₀)`**;
  - `modelLambda_tendsto_zero`, `no_uniform_bound_of_tendsto_zero`: if the coupling runs to zero
    as `a → 0⁺` (asymptotic freedom), then `Λ⁺⁺(a) → 0` and **no `ε(G) > 0` exists**;
  - `runningCoupling`, `no_uniform_bound_running`: the one-loop running form
    `κ(a)² = 1 / log(1/a)` is such a coupling.

  Every ingredient of Definition 4.19 is present in this model (non-Abelian `G = SU(2)`, a
  conjugation-invariant defect built from a faithful representation, `τ(a) = a⁴`, an infimum over a
  nontrivial class of encodings).  Positivity of `Λ⁺⁺` uniformly in `a` is therefore **not** a
  structural consequence of the definition: it is equivalent to the coupling not running to zero,
  which is exactly the input the paper assumes ("fixed `μ_a`") rather than derives.

  `modelLambda_const_pos` records the other side: at *fixed* coupling `κ ≠ 0` the bound does hold,
  `Λ⁺⁺(a) ≥ 2κ²/π²` for all small `a`, which is the regime the paper's argument actually treats.
-/
````

### `Formal/LanguageMatrix.lean`

Content ID `8a5b35d2acaafca1`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L45**

````text
/-!
# The 70-language register

The design documents speak of a "70-language tapestry" with one braid strand per language.  This
file fixes a concrete register of 70 languages, chosen to cover every way of laying text on a
surface that QBX has to handle, and connects each entry to the formal results:

* strand `i : Fin 70` carries `language i`; the labelled `70 × 70` linking matrix of a pure braid
  on these strands can be any symmetric integer matrix with zero diagonal
  (`seventy_language_matrix`, `PureLinkingMatrix.lean`);
* every language gets the line layout of its script (`LangInfo.layout`), interpreted relative to
  the direction of the first line, and the layout results of `TextLayout.lean` apply to it.

Directions covered: left-to-right (42), right-to-left (21), top-to-bottom columns (5: Literary
Chinese and Japanese with columns right-to-left; Mongolian, Manchu and SignWriting with columns
left-to-right), bottom-to-top (2: Hanunó'o, Ogham).  Layouts: uniform (64), boustrophedon (archaic
Greek, Sabaean, Hieroglyphic Luwian), reverse boustrophedon (rongorongo, conventionally associated
with Rapa Nui), Ogham edge writing, and Egyptian hieroglyphs whose direction is set by the facing
of the signs (`variable`).  The register also records whether the language is tonal, whether it
is living, and its modality (one signed language, written in SignWriting).

The same table is in `QBX/data/languages/languages70.json` for the Python side.  The data
(directions, tonality, ISO 639-3 codes) are standard reference facts entered by hand; they are not
derived in Lean.  What Lean checks is everything stated about the table: its size, that the codes
are distinct, the counts per class, and the consequences for braids below.

Main results:

* `languages_length`, `languages_iso_nodup` and the class counts;
* `layout_rigid_iff` — a language's layout is rigid exactly when it is not boustrophedon (the
  mirrored lines of boustrophedon are reflections);
* `read_eq_flatten_of_uniform` — for the 65 languages with uniform or sign-resolved layout, the
  surface reading of any text is its logical reading;
* `nonuniform_layout_not_faithful` — for each of the 5 remaining languages there is a two-line
  text whose surface reading closes up to a different number of components, so those texts must
  be normalised to logical order before braiding.
-/
````

### `Formal/MultiProver/TemperleyLiebOscillator.lean`

Content ID `286ccf20584883f3`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L21**

````text
/-!
# Jones–Wenzl projectors at roots of unity: wiring into the oscillator channel

The oscillator channel (`OscillatorChannel.lean`) evaluates at `q = e^{iπ/r}`, where the
loop value is `δ = [2] = 2 cos(π/r)` and the quantum integers are
`quantumDim r k = sin(kπ/r)/sin(π/r)`.

* `qInt_quantumDim`: the abstract quantum integers `qInt δ k` of `TemperleyLieb.lean` at
  `δ = 2 cos(π/r)` are exactly `quantumDim r k`.
* `jw_spec_root_of_unity`: in any Temperley–Lieb family with loop value `2 cos(π/r)`, the
  Jones–Wenzl projectors `p₁, …, p_{r-1}` exist and satisfy Wenzl's theorem.
* `qInt_root_of_unity_self`: the recursion breaks down at the next step, because `[r] = 0`.
  This is the truncation behind "exactly `r - 1` simple objects" of the oscillator channel.
-/
````

### `Formal/MultiProver/ThreeFoldWay.lean`

Content ID `ffff6774b0cff941`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L66**

````text
/-!
# The three-fold way for the five channels

Dyson's three-fold way sorts complex representations by their antiunitary symmetries.  An
*antilinear structure* on `ℂ^m` is a map `J v = A · v̄` (with `A` a complex matrix); it commutes
with a matrix `M` iff `A · M̄ = M · A`, and `J² = A · Ā`.  A family of matrices `S` is

* of **real** type if some such `J` commutes with all of `S` and `J² = +1`
  (indicator `+1`, division algebra `ℝ`);
* of **quaternionic** type if some such `J` commutes with all of `S` and `J² = −1`
  (indicator `−1`, division algebra `ℍ`);
* of **complex** type if neither exists (indicator `0`, division algebra `ℂ`).

(`HasJ`, `IsType`.)  For irreducible families real and quaternionic exclude each other (Schur);
that general fact is not proved here, but it is proved for the one family where it matters
(`su2_not_real`).

This file replaces a draft that classified the channels by a lookup table.  Every entry of the
table below is now a theorem about the actual matrices the channel computes, and two entries of
the draft turned out to be wrong:

| channel      | family of matrices                                    | type            | theorem                    |
|--------------|-------------------------------------------------------|-----------------|----------------------------|
| `fold`       | permutation matrices of `Word.perm`                   | real            | `fold_isReal`              |
| `link`       | abelian character `t ^ writhe`, `t ∉ ℝ`               | complex         | `writheChar_isComplex`     |
| `anchor`     | reduced Burau matrices at `t ∉ ℝ`, `n ≥ 2`            | complex         | `anchor_isComplex`         |
| `harmonic`   | `burauAt θ`, `sin θ ≠ 0`                              | complex         | `harmonic_isComplex`       |
| `harmonic`   | `burauAt π` (`t = −1`)                                 | real            | `harmonic_pi_isReal`       |
| `oscillator` | its classical limit `SU(2)` on the fundamental strand | quaternionic, not real | `su2_isQuaternionic`, `su2_not_real` |

Corrections to the draft:
* the draft called `harmonic` *real on the universal arc*.  It is unitary there (Squier's form),
  but unitary is not real: away from `t = ±1` the trace of `σ₁` is `n − 2 − t ∉ ℝ`, and any
  invertible commuting antilinear `J` forces every trace to be real (`trace_conj_eq_of_hasJ`).
* the draft typed the oscillator by `r mod 4` (Fibonacci `r = 5` complex, Ising `r = 4`
  quaternionic).  All simple objects of `SU(2)_k` are self-dual, so none is of complex type; the
  standard Frobenius–Schur indicator of the spin-`j` object is `(−1)^{2j}` (cited, not proved).
  What is proved is the classical statement for the fundamental strand: `SU(2)` acting on `ℂ²`
  has a commuting `J` with `J² = −1` and none with `J² = +1`.  The level-indexed replacement of
  the old table is `spinType`.

Further results:
* `SymmetryType.indicator` is a bijection onto `{1, 0, −1}` (`indicator_injective`,
  `range_indicator`).
* `dotProduct_perm`: the permutation representation preserves the symmetric form `Σ vᵢwᵢ`.
* `burauAt_neg`, `neg_mem_resonanceSet`, `two_pi_sub_mem_resonanceSet`: conjugation exchanges
  the harmonic readings at `θ` and `−θ`, so the resonance set is symmetric and half of the sweep
  is redundant (used by the runtime router, `qbx_live/routing.py`).
* `clifford_one_equiv`, `clifford_two_equiv`: the first entries of the Clifford period-8 table
  (`cliffordType`) are derived from Mathlib — `Cl₀,₁ ≅ ℂ`, `Cl₀,₂ ≅ ℍ`; `cliffordType_period`.
* `card_azClasses`, `card_azComplex`, `card_azReal`, `card_azDyson`: the Altland–Zirnbauer
  classes `(T², C², S)` number `10 = 2 + 8`, and the three with no charge conjugation and no
  chiral symmetry are Dyson's three.

Not formalized: Schur exclusivity in general; the Frobenius–Schur indicators of `SU(2)_k`; the
remaining Clifford algebras `Cl₀,ₙ`, `n ≥ 3`; any link between Bott periodicity and the
Cayley–Dickson property-loss ladder.
-/
````

### `Formal/Sovereign/GapFilling/HarmonicFano.lean`

Content ID `8672be1ab59b5ad1`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L127–L128**

````text
/-- **Fano erasure recovery**: if a word carries zero checksum, an erased letter's generator is
the checksum of the remaining letters. -/
````

### `Formal/Streams/WeylLongestAn.lean`

Content ID `21a567c8cae673b3`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L32**

````text
/-!
# The unique longest element of `W(Aₙ)` (the symmetric group), for every `n`

Type `A` was the one irreducible finite type not yet covered by the files `WeylLongest*.lean`.
Here `n = L + 1` (Mathlib's `CoxeterMatrix.Aₙ (L + 1)`, the braid group on `L + 2` strands) is
arbitrary.  The method is the one of `WeylLongestBn.lean` (whose `psum`, `prefixT`, `swapIdx` and
`cRefl_prefixT` are reused):

* `anCartan n`, `an_isCartanFor`: the Cartan matrix of `Aₙ` realises `CoxeterMatrix.Aₙ n`
  (rank-two reduction `isCartanFor_of_local`);
* `anSigma i`: the transposition of `ε`-coordinates `i ↔ i + 1`; **`cRefl_an_prefixT`**:
  `sᵢ (prefixT x) = prefixT (anSigma i x)` for every `x` with `x₀ + ⋯ + x_{L+1} = 0`
  (rows `i < L` coincide with those of `Bₙ`; the last row uses the sum-zero condition);
* `anPos n`: the positive roots `εₐ - ε_b` (`a < b ≤ n`); `anPos_isPositiveRootSet`;
  `anPos_card`: there are `n(n+1)/2` of them;
* `anWord`, `anDelta`: the Garside element `Δ = s₀ (s₁ s₀) (s₂ s₁ s₀) ⋯ (s_L ⋯ s₀)` (the positive
  half twist); `foldr_anWord`: it reverses the `ε`-coordinates `0, …, L + 1`;
* `anCrep_w0_prefixT`, `anCrep_w0_not_mem`: `w₀ = toCoxeter Δ` sends `εₐ - ε_b` to
  `ε_{N-a} - ε_{N-b}` (`N = L + 1`), a negative root;
* **`an_length_eq_iff`**: `ℓ(w) = n(n+1)/2` iff `w = w₀`; `an_length_le`: `ℓ(w) ≤ n(n+1)/2`;
  `an_length_eq_escapes`: `ℓ(w)` is the number of inversions; `anCrep_injective`: the
  reflection representation is faithful.

No `sorry`, no `native_decide`; nothing is checked by finite computation.
-/
````

### `NCG/MajoranaLeptogenesis.lean`

Content ID `36e737a67c104ee9`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L48**

````text
/-!
# Majorana CP phases and leptogenesis in the Noncommutative Standard Model

The finite Dirac operator `D_F` of the Noncommutative Standard Model contains a Majorana mass
term `M_R` for the right-handed neutrinos (`NCG.LeptonData`, `NCG.DSM_nuR_nuRbar`), and the
light neutrinos get the symmetric seesaw Majorana mass matrix `m_ν = −m_D M_R⁻¹ m_Dᵀ`
(`NCG.seesawMass`).

## 1. Majorana CP phases

* The leptonic mixing matrix of Majorana neutrinos is `U = U_PDG(θ₁₂, θ₂₃, θ₁₃, δ) · P`,
  `P = diag(1, e^{iα/2}, e^{iβ/2})` (`majoranaPMNS`); it is unitary, and the Majorana phases do
  not enter the Jarlskog invariant (`jarlskog_majoranaPMNS`).
* Majorana phases cannot be removed: a rephasing `ν ↦ e ν` of a Majorana field keeps its mass
  real and positive iff `e = ±1` (`majorana_rephase_real_iff`). The Majorana-type invariant
  `Im((U_{e1} Ū_{e2})²)` is invariant under all remaining rephasings (`majoranaInv_rephase`)
  and equals `−c₁₂² s₁₂² c₁₃⁴ sin α` (`majoranaInv_pmns`); it is non-zero iff `sin α ≠ 0` for
  non-degenerate mixing angles (`majoranaInv_pmns_ne_zero_iff`).
* **Invariant of the mass matrix itself.** `I(m) = Im(m_{ee} m_{μμ} m̄_{eμ}²)` is invariant under
  charged-lepton rephasing (`massInv_rephase`) and vanishes for real (CP-conserving) mass
  matrices (`massInv_of_real`); so `I(m) ≠ 0` means that the Majorana phases cannot be rotated
  away (`massInv_ne_zero_not_real`). For a two-flavour Majorana mass matrix
  `m = R(θ) diag(m₁, m₂ e^{iα}) R(θ)ᵀ`:
  `I(m) = c² s² m₁ m₂ (m₁² − m₂²) sin α` (`massInv_twoFlavour_phase`).
* **The spectral seesaw generates a non-zero Majorana CP phase**: for explicit lepton data of the
  spectral triple, the seesaw mass matrix has `I(m_ν) = 24 ≠ 0` (`spectral_seesaw_majorana_cp`).

## 2. Leptogenesis

* **Origin of the asymmetry.** For a decay amplitude `c₀ + c₁ L` (tree coupling `c₀`, one-loop
  coupling `c₁`, loop function `L`) the CP-conjugate amplitude is `c̄₀ + c̄₁ L`, and
  `|A|² − |Ā|² = 4 Im(c₀ c̄₁) Im(L)` (`cp_asymmetry_interference`): an asymmetry needs both a
  CP-violating phase of the couplings and an absorptive part of the loop.
* The exact one-loop CP asymmetry in the decay of the lightest heavy neutrino `N₁` is
  `ε_L = (1/8π) Σ_{j=2,3} Im[((Y†Y)_{1j})²]/(Y†Y)_{11} · f(M_j²/M₁²)` with
  `f(x) = √x (1 + 1/(1 − x) − (1 + x) ln((1 + x)/x))` (`epsilonL`, `loopF`).
* `f(x) < 0` for `x > 1` (`loopF_neg`); `ε_L = 0` if the Yukawa couplings are real
  (`epsilonL_of_real`); `ε_L > 0` whenever the CP phases have the right sign
  (`epsilonL_pos`); `ε_L(tY) = t² ε_L(Y)` (`epsilonL_smul`).
* **The three Sakharov conditions** hold simultaneously for explicit lepton data of the spectral
  triple (`spectral_leptogenesis_sakharov`): the Majorana term of `D_F` violates lepton number
  (and `B − L`) by two units (`majorana_violates_lepton_number`); the exact asymmetry is
  `ε_L = −t² f(M₂²/M₁²)/(4π) > 0`; and `N₁` decays out of equilibrium, `Γ_{N₁} < H(T = M₁)`.
-/
````

### `NCG/PatiSalamSpectralAction.lean`

Content ID `1930d369ea2978a6`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L401–L411**

````text
/-- **Spectral data of the fluctuated Pati–Salam Dirac operator `D_A` on `M × F`.**
* `D` is the spectrum of `D_A` (eigenvalues with multiplicity, with trace-class heat kernel).
* `c` is the cutoff `f`.
* `heat` is the Seeley–DeWitt heat-trace expansion `Tr e^{-tD_A²} ∼ (4πt)⁻² Σ aₖ tᵏ`.
* `a4_split` decomposes `a₄ = a 2`. Its Yang–Mills part is
  `(2/3) Σᵢ gᵢ² Tr_{H_F}(G(Tᵢ)²) YMᵢ` for the three factors
  `i = SU(2)_L, SU(2)_R, SU(4)`, with `YMᵢ = ∫ F^a_{iμν} F^{aμν}_i` and `Tᵢ` the standard
  generators `genL, genR, gen4`. This is `(1/360) · 30 · 8 ∫ Tr_{H_F}(F²)`, the `F²` term of
  the Seeley–DeWitt `a₄` (`SeeleyDeWittInvariants.a4`), normalised as in
  `NCG.SpectralAction.CanonicalGauge`. All remaining contributions (gravity, Higgs, `Σ`) are
  in `aRest`. -/
````

### `NCGHiggsThresholdEncA.lean`

Content ID `e31832d1c09d6efd`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L16–L16**

````text
/-- Remaining pieces of part A of the enclosure. -/
````

### `NCGHiggsThresholdEncB.lean`

Content ID `b9ec5875765a351a`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L16–L16**

````text
/-- Remaining pieces of part B of the enclosure. -/
````

### `NCGHiggsThresholdEncC.lean`

Content ID `98f615f9de0b05fd`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L16–L16**

````text
/-- Remaining pieces of part C of the enclosure. -/
````

### `NCGHiggsThresholdEncD.lean`

Content ID `e544c837777aac6a`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L16–L16**

````text
/-- Remaining pieces of part D of the enclosure. -/
````

### `NCGKO6.lean`

Content ID `e26cfb72752e0b71`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L188–L188**

````text
/-! ## Steps 4 and 6: the remaining KO-dimension 6 signs -/
````

### `Sovereign/Algebra/CrossHalfUniversal.lean`

Content ID `9d86af164becf54f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L92–L93**

````text
/-- **Universal non-zero-divisor count.** The remaining cross-half vectors — those with
`i = 0`, `j = 0` or `i = j` — number exactly `6D - 8`. -/
````

### `Sovereign/Algebra/DualUnityBoundaryDefs.lean`

Content ID `4f67cc5c0b4e30fa`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L37–L38**

````text
/-- Twelve vectors complementary to `kerVecs p`: on a paired index producing a kernel
vector, the opposite sign combination; on the remaining indices, both basis vectors. -/
````

### `Sovereign/Algebra/HopfLift.lean`

Content ID `5d03c0af4af00453`; 1 byte-identical path(s); source definitions and proofs reviewed; header triaged; see R41; not build-verified.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
6 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 9 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "singularit"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/Algebra/LANABicategoryAssociator.lean`

Content ID `c90818e834efb2f5`; 1 byte-identical path(s); full file source review; see R39; not build-verified.

**L1–L29**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Higher-Categorical Bicategory Associator 2-Cell Closure (OP-046, HYP-130)

This module formalizes:
1. The weak higher-categorical bicategory `ℬ_IUTT` of Hodge Theaters:
   - 0-cells: Hodge Theaters `T` carrying base volume.
   - 1-cells: Θ-morphisms `f : T₁ ⟶ T₂` carrying dilation factor `λ(f) > 0`.
   - 2-cells: 2-morphisms / modifications `α : f ⟹ g` carrying norm `‖α‖ ≥ 0`
     and bounding the boundary discrepancy `|λ(f) - λ(g)| ≤ ‖α‖ / 2`.
2. The non-commutative LANA Interim Report Figure 7 diagram:
   - Path 1: Multiradial evaluation across Θ-link (`λ = Δ > 1`).
   - Path 2: Tautological base evaluation (`λ = 1.0`).
   - Theorem: Path 1 ≠ Path 2 in the underlying 1-category.
3. The Sedenion Associator 2-Cell Closure:
   - Norm `‖α_assoc‖ = 2.0`, corresponding to `[e₁, e₂, e₄] = 2 e₇`.
   - Theorem: The associator 2-cell strictly fills the Figure 7 diagram
     for all `Δ ≤ 1 + ‖α_assoc‖ / 2 = 2.0`.
4. The Φ-Surgery Contraction Operator:
   - Contraction factor `κ = 0.64 = 16 / 25 < 1`.
   - Theorem: Φ-surgery strictly resolves Compatibility condition (9-1):
     `λ(S_Φ(Path 2)) < λ(Path 1)` for all `Δ ≥ 1.0`.
5. Mac Lane Pentagon Coherence:
   - Strict pentagon commutativity for composable 1-morphisms.
   - Vanishing of the Cayley–Dickson 3-cocycle coboundary `δω = 0` (product of phases = 1).
6. Complete resolution of Open Problem OP-046.
-/
````

### `Sovereign/Algebra/SedenionStratification.lean`

Content ID `ce0d80799d6b24e9`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L2–L32**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Machine-checked cross-octet stratification of the integer sedenions

The theorems in `Sovereign.Algebra.LeechSedenionFano` and `MonographTheorems` (removed by the 2026 curation)
record the *numerical* content of the monograph (`42 * 4 = 168`, …).  They are true,
but they say nothing about the sedenion algebra itself.

This module states and proves the corresponding *structural* facts about the actual
Cayley–Dickson algebra `CDSedenion = CD (CD (CD (CD ℤ)))`:

* the 256 cross-octet vectors `± e i ± e (8 + j)` are pairwise distinct and non-zero;
* such a vector annihilates another cross-octet vector **iff** `i ≠ 0`, `j ≠ 0`, `i ≠ j`
  (`crossOctet_annihilator_iff_index`);
* exactly 168 of them are zero divisors and exactly 88 are not
  (`crossOctetZD_length`, `crossOctetNonZD_length`);
* the annihilation relation is symmetric, is 8-regular on the 168 zero divisors, and
  therefore has 672 undirected edges;
* annihilation conserves the XOR charge `i ^^^ j`, and the 168 zero divisors split into
  the 7 charge sectors `χ ∈ {1, …, 7}` of 24 vectors each.

That the 88 remaining vectors are not zero divisors *in the whole algebra* (a statement
about infinitely many potential partners, hence not a finite check) is proved separately
in `Sovereign.Algebra.SedenionNonZeroDivisors`.

The finite verifications below are discharged by kernel-external evaluation
(`native_decide`) because they involve tens of thousands of exact integer sedenion
products.
-/
````

### `Sovereign/Algebra/StratificationMain.lean`

Content ID `cd0cb8205098ca2c`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L16**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Capstone: the exact zero-divisor criterion for cross-octet sedenions

Combining

* `crossOctetVec_annihilator_iff` (the 168 vectors with `i ≠ 0`, `j ≠ 0`, `i ≠ j` do
  annihilate a cross-octet partner), and
* `crossOctetVec_not_left_zero_divisor` / `crossOctetVec_not_right_zero_divisor` (the 88
  remaining vectors annihilate nothing at all in the 16-dimensional algebra),

gives the exact statement: a cross-octet vector `s • eᵢ + t • e₈₊ⱼ` is a zero divisor of
the sedenions **iff** `i ≠ 0`, `j ≠ 0` and `i ≠ j`.
-/
````

### `Sovereign/Algebra/TowerFlexibility.lean`

Content ID `0cbf2804ec89a997`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L28**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Resolution of Flexibility Beyond Basis Vectors (OP-007, HYP-114)

This module formalizes the affirmative resolution of Open Problem OP-007:
"Is every Cayley–Dickson algebra of the tower flexible on *all* elements, not just basis vectors?"

## Mathematical Framework:
1. An algebra A is flexible if for all x, y ∈ A:
   (x · y) · x = x · (y · x), or equivalently [x, y, x] = 0.
2. In `TowerAssociator.lean`, `basis_flexible` proves that every algebra of the tower
   is flexible on basis vectors: (e_a · e_b) · e_a = e_a · (e_b · e_a).
3. In `TowerCocycle.lean`, `assoc3_conj` and `assocNeg_reverse` establish the reversal
   invariance of the associator:
   conj [x, y, z] = - [conj z, conj y, conj x]
   assocNeg n a b c = assocNeg n c b a.
4. By trilinearity of the associator and polarization:
   [x, y, x] = ∑_a x_a² y_b [e_a, e_b, e_a] + ∑_{a < c} x_a x_c y_b ([e_a, e_b, e_c] + [e_c, e_b, e_a]).
   Since [e_a, e_b, e_a] = 0 and [e_a, e_b, e_c] + [e_c, e_b, e_a] = 0 identically,
   the associator [x, y, x] vanishes for all elements x, y.
5. In particular, linear combinations that strictly fail alternativity (such as the OP-008
   witness x = e₁ + e₁₀, y = e₄ where [x, x, y] = 2 e₁₅ ≠ 0) nevertheless strictly
   satisfy the flexibility identity:
   (x · y) · x = x · (y · x).
-/
````

### `Sovereign/Analysis/DoubleHomologyChladniDuality.lean`

Content ID `3417b4c3ee3af1f1`; 1 byte-identical path(s); source definitions and proofs reviewed; header triaged; see R40; not build-verified.

**L1–L21**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 3 of the 5
theorems in this module have no quantified variable: they check facts about fixed numbers. The
file never mentions the real numbers, so it contains no continuum model of any kind. The header
below uses the word "singularit"; read it as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem
or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Double Homology–Chladni Nodal Set Duality (Tier 3 Horizon)
  **Epistemic Classification:** [A] Persistent Double Homology & Equivariant Nodal Geometry

This module formally certifies the duality functor between the persistent double
homology cycle space (H_*ⁱⁿᶠ, H_*ˢᵘᵖ) of a Cayley-Dickson hyperdigraph and the D₄-equivariant
nodal manifold of the 2D harmonic wave equation. Every flat 1-cycle in double homology
maps bijectively to a closed, singularity-free nodal curve in the Chladni partition,
while non-zero Čech coboundary defects map to nodal saddle intersections.
-/
````

### `Sovereign/Autonomous/HardwareLoop.lean`

Content ID `4d091ac591323fd1`; 1 byte-identical path(s); full file source review; see R24; not build-verified.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
13 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 51 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "unconditional"; read them as motivation, not as
a description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/Autonomous/PoincareBall.lean`

Content ID `d5bb8e191d110115`; 1 byte-identical path(s); statements/comments triaged; proof-body review pending.

**L208–L209**

````text
/-- On the Lorentz-orthogonal complement of a future unit timelike vector `(q₀, q)`, the
Lorentz form `-v₀² + ‖v‖²` is non-negative. -/
````

### `Sovereign/Coding/QLDPC.lean`

Content ID `f37326710815478d`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L34**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 8 of the 11
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the words "settled", "unconditional"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Quantum LDPC Codes and Hypergraph Product Geometries (HYP-148, Related to OP-029 (not settled here))
  **Epistemic Classification:** [A] Coding Theory & Quantum Stabilizer Identities

This module formally certifies the Tillich–Zémor hypergraph product construction
applied to the sedenion [24, 4, 8] triply-even binary codes, yielding CSS Quantum
LDPC codes [[976, 16, ≥8]].

Key Results Formally Certified:
1. Exact Block Length and Logical Dimension:
   - Input classical codes: C₁ = C₂ = [24, 4, 8] with check dimensions m₁ = m₂ = 20.
   - Total physical qubits: N = n₁ n₂ + m₁ m₂ = 24 · 24 + 20 · 20 = 576 + 400 = 976.
   - Logical encoded qubits: K = k₁ k₂ = 4 · 4 = 16.
   - Code rate: R = 16 / 976 = 1 / 61.
2. Parity Check Commutation Over 𝔽₂:
   - For hypergraph parity checks H_X = [H₁ ⊗ I_{n₂}, I_{m₁} ⊗ H₂ᵀ] and
     H_Z = [I_{n₁} ⊗ H₂, H₁ᵀ ⊗ I_{m₂}], the product evaluates over 𝔽₂ to
     H_X · H_Zᵀ = H₁ ⊗ H₂ᵀ + H₁ ⊗ H₂ᵀ ≡ 0 (mod 2).
   - This identity holds unconditionally for arbitrary binary matrices H₁, H₂.
3. Quantum Minimum Distance Bound:
   - d_CSS ≥ min(d₁, d₂) = 8.
4. Parity Check Sparsity:
   - Maximum check weight row_wt(H_X) = wt(H₁) + 1 ≤ 9, ensuring the LDPC property.
-/
````

### `Sovereign/Combinatorics/TowerSectorProfile.lean`

Content ID `db912f3486661a84`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L21–L24**

````text
/-- The conjectured non-recursive census of the sector class `w` in dimension `2ⁿ`: the main
family of `6 · 2^(n-3)` pairs carried by the image of the octonionic degree `4`, plus, for
each step `t` of the descent, `2^(n-3-t)` pairs carried by the image of the level-`(t+4)` top
degree under the remaining steps. -/
````

### `Sovereign/Compression/BitCode.lean`

Content ID `c6421d4310f2acb5`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L3–L10**

````text
/-!
# Self-delimiting bit codes

A `BitCode α` is a self-delimiting (prefix) binary code: a decoder reading a codeword followed by
arbitrary further bits returns the encoded value and the remaining bits. We build such codes for
natural numbers (doubled binary digits, `2·size(n) + 1` bits), pairs, lists, DAG nodes and
proof DAGs.
-/
````

### `Sovereign/Conjecturer/Pipeline.lean`

Content ID `c0648021e9d25679`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L45–L45**

````text
/-- Remaining resource budget. -/
````

### `Sovereign/Consensus/Protocol.lean`

Content ID `9eb7573e8e440397`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L69–L69**

````text
/-- proposed, not yet certified artifacts -/
````

### `Sovereign/Fluid/CoupledSingularity.lean`

Content ID `cc09dad3b04d0b1d`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L30**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 9 of the 9
theorems in this module have no quantified variable: they check facts about fixed numbers. The
file never mentions the real numbers, so it contains no continuum model of any kind. The header
below uses the word "singularit"; read it as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem
or establishes a physical result.

Coupled Axisymmetric Hou-Chen Singularity, G_2 Calibration Helicity & Multi-Fractal Cascades.

Formal certification of:
1. Coupled 2-component boundary contraction bound:
   kappa = 85 / 100 < 1.
2. G_2-invariant associative 3-form calibration ratio bound:
   phi(u, v, w) / (||u|| ||v|| ||w||) <= 1.
3. Fano line associator vanishing:
   I_assoc = 0 on calibrated associative 3-planes.
4. 32D trigintaduonion PG(3, 2) edge decomposition:
   8 * 672 + 7 * 288 = 5376 + 2016 = 7392.
5. Multi-scale spectral decay rates:
   d_high = 24, lambda_2 = 4 => d_high / lambda_2 = 6 (rho_reg = 1/6).
   d_low = 8, lambda_2 = 4 => d_low / lambda_2 = 2 (rho_bireg = 1/2).
6. Multi-fractal She-Leveque intermittency bound at p = 6:
   zeta(6) = 16/9 < 18/9 = 2 = zeta_K41(6).
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

Checked by Lean with no `sorry` and standard axioms only; see the scope note above for what the theorems actually state.
-/
````

### `Sovereign/Fluid/EnstrophyCascade.lean`

Content ID `923ff5efad31a10e`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L12**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 8 of the 16
theorems in this module have no quantified variable: they check facts about fixed numbers. The
file never mentions the real numbers, so it contains no continuum model of any kind. The header
below uses the word "navier"; read it as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem
or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine
-/
````

### `Sovereign/Fluid/EnstrophyDecayReal.lean`

Content ID `c38cc9cdba3593eb`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
3 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 18 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "navier"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

**L11–L31**

````text
/-
# Viscous enstrophy decay over the reals

`Sovereign.Speculative.GlobalRegularity` states its "Viscous Enstrophy Decay Theorem" with
integer stand-ins, and its integrating-factor step (`integrating_factor_decay_bound`)
simply returns its hypothesis.  This module proves the actual statement for a
real-valued, differentiable enstrophy `E : ℝ → ℝ`.

* `exp_decay_of_deriv_le` — Grönwall in differential form: if `E' ≤ -k E` then
  `E t ≤ E 0 · exp (-k t)` for `t ≥ 0`.
* `enstrophy_exponential_decay` — the physical form: with enstrophy balance
  `E' = P - 2 ν D`, vanishing vortex stretching `P = 0`, viscosity `ν ≥ 0` and the
  Poincaré inequality `D ≥ λ₁ E`, one gets `E t ≤ E 0 · exp (-2 ν λ₁ t)`.
* `exp_decay_sharp` — the bound is attained by `E₀ · exp (-k t)`, so it cannot be
  improved in general.

What is *not* modelled here: the enstrophy balance, the vanishing of vortex stretching and
the Poincaré inequality are hypotheses about the flow, not consequences of the
Navier–Stokes equations; deriving them requires a PDE model that the library does not yet
contain.
-/
````

### `Sovereign/Fluid/FreeBoundaryRegularity.lean`

Content ID `199006bf3062ab70`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L10**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 6 of the 14
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 27 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. 1 theorem(s) here
are flagged as weak in `sovereign/artifacts/CLAIM_GAP.txt`. The header below uses the word(s)
"blowup", "singularit"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Fluid/UniversalRegularity.lean`

Content ID `64b8f46799e42941`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L25**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Universal Regularity vs. Biregularity Classification across the Cayley–Dickson Tower (OP-003, HYP-112)

This module formalizes the resolution of Open Problem OP-003:
"Prove HYP-070's criterion (χ < 8 or χ = 2^k) for all D = 2^n ≥ 16, not just D ∈ {16, 32}."

## Mathematical Foundation:
1. **Universal Regularity Criterion**:
   For every Cayley-Dickson dimension D = 2^n ≥ 16, a charge sector χ ∈ {1, ..., D/2 - 1}
   is (D - 8)-regular if and only if:
       χ < 8  ∨  ∃ k ≥ 3, χ = 2^k.
   The number of regular sectors in dimension D = 2^n is identically n + 3.

2. **Biregularity Refinement & Multiregularity Emergence**:
   The naive assumption that non-regular sectors are "biregular otherwise" holds only in D = 32.
   In D ≥ 64 (n ≥ 6), multiregular sectors with 3 or more degree levels emerge strictly.
   - Biregular sectors: exactly 7(n - 4) + (n - 4)(n - 5) / 2 sectors.
   - Multiregular sectors: (2^(n - 1) - 1) - (n + 3) - [7(n - 4) + (n - 4)(n - 5)/2] sectors.
   At D = 64 (n = 6), multiregularSectorCount 6 = 7 > 0, formally settling the biregular-otherwise
   conjecture and establishing the exact universal tripartite partition.
-/
````

### `Sovereign/Fluid/ZeroViscosityBoundary.lean`

Content ID `963b66159e276390`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 5 of the 12
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
never mentions the real numbers, so it contains no continuum model of any kind. 1 theorem(s) here
are flagged as weak in `sovereign/artifacts/CLAIM_GAP.txt`. The header below uses the word(s)
"navier"; read them as motivation, not as a description of what is proved. What is proved is exactly
the Lean statements. No theorem in this module settles an open problem or establishes a physical
result.
-/
````

### `Sovereign/Geometry/ArnoldCurvatureReduction.lean`

Content ID `566cb5a084b5c5d4`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L44**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Formalization of Infinite-Dimensional Arnold Curvature Reduction (OP-033, HYP-129)

This module formally settles Open Problem OP-033 (Level L3, Domain 4: Non-Associative Hydrodynamics & PDE):
"Kernel-formalize in Lean 4 the momentum map reduction μ: sdiff(M)* → g_2* and the sectional curvature formula
yielding 0 ≤ K ≤ 5/4 on V_2(ℝ^7)."

## Key Theorems Formally Certified:
1. Infinite-Dimensional Fluid Algebra sdiff(M) and Momentum Map:
   - SDiff(M) is the infinite-dimensional Lie group of volume-preserving diffeomorphisms.
   - Dual space sdiff(M)* comprises fluid vorticity fields ω.
   - The momentum map μ: sdiff(M)* → g_2* projects vorticity onto the 14D Lie algebra g_2.
   - The coadjoint quotient by SU(2) is the 11-dimensional Stiefel manifold V_2(ℝ^7) ≅ G_2 / SU(2).

2. Dimension and Tangent Bundle Decomposition of V_2(ℝ^7):
   - dim V_2(ℝ^7) = 2 * 7 - 3 = 11.
   - Vertical tangent space V_P ≅ so(2) has dimension 1.
   - Horizontal tangent space H_P has dimension 2 * (7 - 2) = 10.
   - Exact sum: dim V_P + dim H_P = 1 + 10 = 11.

3. Canonical Riemannian Sectional Curvature Formula on V_2(ℝ^7):
   - For an orthonormal 2-plane in T_P V_2(ℝ^7) spanned by tangent vectors X, Y:
     - Vertical components: A_X, A_Y ∈ so(2).
     - Horizontal components: K_X, K_Y.
     - Vertical bracket term: T_1 = (1/4) ‖[A_X, A_Y]‖² ≥ 0.
     - Horizontal-vertical cross term: T_2 = ‖(1/2)(K_X A_Y - K_Y A_X) + P · skew‖² ≥ 0.
     - Grassmannian term: T_3 = -K_Gr ≥ 0.
   - Total sectional curvature: K(X, Y) = T_1 + T_2 + T_3 ≥ 0.
   - Universal canonical bounds: 0 ≤ K ≤ 5/4 (in scaled integer units: 0 ≤ 4 * K ≤ 5).

4. Curvature Transition Jump and Geodesic Conjugate Point Bound:
   - Bulk Arnold curvature: K_bulk < 0 (divergence / Lagrangian turbulence).
   - Boundary Stiefel curvature: 0 ≤ K_boundary ≤ 5/4 (elliptic focusing).
   - Strict jump: 4 * K_bulk < 4 * K_boundary across the transition threshold.
   - Universal first conjugate point focusing time: t_conj ≥ 2π / √5.

5. Refutation of OP-033 Falsification Criterion:
   - Since K(X, Y) = T_1 + T_2 + T_3 is a sum of non-negative squares, K(X, Y) ≥ 0 for every 2-plane.
   - It is impossible for any 2-plane in V_2(ℝ^7) to have negative sectional curvature (K < 0).
-/
````

**L184–L192**

````text
/-- *Scope (truth-in-labelling):* this theorem checks fixed numerical facts about the finite model
defined in this file. It has no universally quantified variable and does not settle an open
problem. Formerly named `op033_arnold_curvature_reduction_settled`.

Full Formal Resolution of Open Problem OP-033:
    The momentum map reduction quotient matches dim V_2(ℝ^7) = 11,
    the tangent bundle splits as 1 + 10 = 11,
    sectional curvature is unconditionally non-negative and bounded by 5/4,
    and negative sectional curvature is impossible. -/
````

### `Sovereign/Geometry/FanoQuantumWalkSpectrum.lean`

Content ID `76e271ac6fe495f8`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L8**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 3 of the 8
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
never mentions the real numbers, so it contains no continuum model of any kind. The header below
uses the word(s) "settled"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Geometry/HigherCohomologyVanishing.lean`

Content ID `0be6ac288a7353f8`; 2 byte-identical path(s); source definitions and proofs reviewed; header triaged; see R27; not build-verified.

**L1–L24**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Higher Cohomology Vanishing Theorem for the Cayley-Dickson Tower (OP-006 Resolution)
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

Settles Open Problem OP-006 in the negative:
Proves that the Mac Lane associator 3-cocycle `ω = assocNeg n` does NOT extend to a
non-trivial class in `H⁴((ℤ/2)ⁿ; ℤ/2)` at any level `n` of the Cayley–Dickson tower.

Key Results:
1. `cup31_assoc_eq_delta`: For every 1-cocycle `χ : Nat → Bool` (additive character),
   the right cup product `ω ⌣ χ` is the exact coboundary `δ(ε ⌣ χ)`.
2. `cup13_assoc_eq_delta`: For every 1-cocycle `χ`, the left cup product `χ ⌣ ω`
   is the exact coboundary `δ(χ ⌣ ε)`.
3. `cohomology_class_cup_vanishes`: The cohomology class `[ω ⌣ χ] = 0` and `[χ ⌣ ω] = 0`
   in `H⁴((ℤ/2)ⁿ; ℤ/2)` for all levels `n`.
4. `stasheff_associahedron_k5_faces`: The higher Stasheff 4-cell coherence obstruction
   across the 9 faces (6 pentagons and 3 commutativity squares) of the 3D associahedron
   vanishes identically, guaranteeing that higher associators induce zero 4-cochain defect.
-/
````

**L142–L142**

````text
/-! ## 6. Settlement of Open Problem OP-006 -/
````

### `Sovereign/Graph/AlonBoppanaObstruction.lean`

Content ID `01e84a35a9678a78`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L39**

````text
/-!
# Alon–Boppana Saturation Obstruction Theorem (HYP-098, Settles OP-017)
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

This module formally resolves Open Problem OP-017 in the negative:
Does the D=16 annihilation graph saturate the Alon–Boppana bound? Does any sector at any D?

Answer: NO. Neither D=16 nor any other sector in any dimension D = 2^n ≥ 16 ever saturates
the Alon–Boppana bound 2√(d - 1).

Core Mathematical Proofs:
1. Universal Number-Theoretic Obstruction:
   The quantity d - 1 = D - 9 = 2^(m+4) - 9 satisfies (2^(m+4) - 9) % 8 = 7 for all m ≥ 0.
   Since quadratic residues modulo 8 are {0, 1, 4}, 7 is a quadratic non-residue mod 8.
   Therefore, k^2 ≠ 2^(m+4) - 9 for all integers k: the Alon-Boppana term √(d - 1) is strictly
   irrational for every dimension D = 2^n ≥ 16 in the doubling tower.
   Consequently, no sector with an integer second eigenvalue λ₂ ∈ ℤ can ever saturate 2√(d - 1).

2. Doubling Pole Sector Bound:
   Across all D ≥ 16, the doubling pole sector has λ₂ ≡ 4.
   Since 16 < 4(D - 9) for all D ≥ 16, the pole sector strictly satisfies λ₂² < 4(d - 1),
   maintaining a strictly positive Ramanujan slack 4(D - 9) - 16 ≥ 12.

3. Octonionic Regular Non-Pole Sectors:
   The regular non-pole sectors have λ₂ = (D - 8)/2.
   Saturation requires (D - 8)^2 = 16(D - 9), which reduces to (D - 16)^2 = 48.
   Since 48 is not a square in ℤ (6^2 = 36 < 48 < 49 = 7^2), this has zero integer solutions.
   At D = 16, the sector is strictly sub-Ramanujan: (16 - 8)^2 = 64 < 112 = 16(16 - 9).
   At D ≥ 32, the sector strictly jumps to super-Ramanujan: (32 - 8)^2 = 576 > 368 = 16(32 - 9).
-/
````

### `Sovereign/Graph/BaseGraphQuotient.lean`

Content ID `2c16f38926019054`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L43**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 26 of the 32
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the words "settled", "unconditional"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Equitable Base Graph Quotient & 4-Fold Quadruplet Tower (HYP-146, Related to OP-027 (not settled here))
  **Epistemic Classification:** [A] Graph-Theoretic & Spectral Identities

This module formally resolves the structure of the equitable twin-class
quotient for regular non-trivial charge sectors across the Cayley-Dickson tower.

Key Theorems Formally Certified:
1. 4-Fold Quadruplet Twin Class Structure:
   Every cross-half vertex v = (s, t, i, j) belongs to a cell of size exactly 4
   indexed by the basis index pair (i, j) with varying signs s, t ∈ {0, 1}.
   The quotient matrix Q factors unconditionally as Q = 4 * A_base, where A_base
   is the {0, 1}-adjacency matrix of a simple regular base graph.

2. Base Graph Parameters in Dimension D = 2^n ≥ 16:
   - Order (number of base vertices): N_base(D) = (D - 4) / 2.
   - Regular degree: d_base(D) = (D - 8) / 4.
   - Size (number of base edges): E_base(D) = N_base(D) * d_base(D) / 2.
   - Zero mode multiplicity: N_zeros(D) = 3 * (D - 4) / 2.

3. Concrete Realizations across Doubling Tower:
   - D = 16 (Sedenion): N_base = 6, d_base = 2, E_base = 6 (the 6-cycle C_6).
     Zero modes: 18. Non-zero eigenvalues: 4 * Spec(C_6) = {±8, ±4^2}.
   - D = 32 (Trigintaduonion): N_base = 14, d_base = 6, E_base = 42. Zero modes: 42.
   - D = 64 (Chingon): N_base = 30, d_base = 14, E_base = 210. Zero modes: 90.
   - D = 128 (Universal CD): N_base = 62, d_base = 30, E_base = 930. Zero modes: 186.
   - D = 256: N_base = 126, d_base = 62, E_base = 3906. Zero modes: 378.

4. Degree & Dimension Compatibility:
   For all D ≥ 16 with D % 4 = 0:
   - 4 * d_base(D) = D - 8 (exact sector degree).
   - N_base(D) + N_zeros(D) = 2 * (D - 4) (exact sector vertex count).
-/
````

### `Sovereign/Graph/MutualAnnihilationSpectrum.lean`

Content ID `3e010653aa0d2e5b`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 4 of the 20
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 57 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "blowup"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Graph/RamanujanSpectrum.lean`

Content ID `d4620174ba813531`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 1 of the 19
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 45 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "blow-up"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Graph/RegularSubfamilies.lean`

Content ID `248c5ebc0eb34160`; 1 byte-identical path(s); statements/comments triaged; proof-body review pending.

**L1–L8**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 1 of the 7
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
never mentions the real numbers, so it contains no continuum model of any kind. The header below
uses the word(s) "unconditional"; read them as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

**L10–L42**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Persistent Regular Sub-Families Across the Cayley–Dickson Tower (OP-012, HYP-115)

This module formalizes the affirmative resolution of Open Problem OP-012:
"HYP-074 proves the annihilation graph is regular iff D = 16. Does any *sub*-family
(e.g., pole sectors, quaternionic pairs) remain regular for all D?"

## Mathematical Framework:
1. Global Irregularity: HYP-074 establishes that the total annihilation graph
   is regular if and only if D = 16. At D ≥ 32, vertex degrees vary.
2. Persistent Regular Sub-Families:
   Despite global irregularity, two infinite sub-families remain strictly regular
   with degree identically equal to D - 8 across all D = 2^n ≥ 16:
   (a) The Octonionic Sub-Family:
       S_oct = {χ ∈ ℕ | 1 ≤ χ ≤ 7}.
       For all χ ∈ S_oct and all D = 2^n ≥ 16, χ < 8 satisfies the universal regularity
       criterion (HYP-112).
   (b) The Doubling Pole Sub-Family:
       S_pole(n) = {2^k | 3 ≤ k ≤ n - 2}.
       Every doubling pole (including the principal pole χ = D/4 = 2^(n-2)) satisfies
       the 2^k power-of-two criterion and remains strictly (D-8)-regular.
3. Sector Cardinality Scaling:
   The total number of persistent regular sectors is:
       |S_oct| + |S_pole(n)| = 7 + (n - 4) = n + 3 = log₂(D) + 3.
4. Falsification Protocol:
   A sub-family claimed regular that becomes irregular at some D.
   We prove that for all n ≥ 4 and all χ ∈ S_oct ∪ S_pole(n), χ satisfies the regularity
   criterion unconditionally, with 0 falsifying dimensions.
-/
````

### `Sovereign/Graph/SedenionAnnihilationMain.lean`

Content ID `0f4d31bd7e8c94da`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 1 of the 2
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 13 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "blowup"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Graph/ZeroDivisorFanoTopology.lean`

Content ID `e6aea7b951506102`; 2 byte-identical path(s); full file source review; see R45; not build-verified.

**L124–L124**

````text
/-- Theorem: The 3 lines through any point partition the remaining 6 points into 3 pairs -/
````

### `Sovereign/HigherConsensus/ModelStructure.lean`

Content ID `4187979fcf86b76f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L48**

````text
/-!
# Projective and injective structures on simplicial presheaves

For a small category `C` we study the category `Cᵒᵖ ⥤ SSet` of simplicial presheaves
(`Fun(Cᵒᵖ, sSet)`) and its two standard (Quillen) structures.

**Simplicial sets.** Kan fibrations (`sSetFibrations`) are the maps with the right lifting
property (RLP) against the horn inclusions `Λ[n+1, i] ⟶ Δ[n+1]`; trivial Kan fibrations
(`sSetTrivialFibrations`) are the maps with the RLP against the boundary inclusions
`∂Δ[n] ⟶ Δ[n]` (both as in Mathlib's `SSet.modelCategoryQuillen`).

**Projective structure.** Fibrations and trivial fibrations are defined objectwise
(`projFibrations`, `projTrivialFibrations`); cofibrations (`projCofibrations`) and trivial
cofibrations (`projTrivialCofibrations`) are defined by the left lifting property.

**Injective structure.** Cofibrations are the monomorphisms (= objectwise monomorphisms,
`injCofibrations_iff`); trivial fibrations are defined by the right lifting property
(`injTrivialFibrations`).

## Main results

* `projective_factorization` — every morphism factors as a projective cofibration followed by a
  projective trivial fibration (small object argument, applied to the generating family
  `C(-, c) ⊗ ∂Δ[n] ⟶ C(-, c) ⊗ Δ[n]`, whose sources are finitely presentable);
* `projective_factorization_fibration` — factorisation as a projective trivial cofibration
  followed by a projective fibration (generating family `C(-, c) ⊗ Λ[n+1, i] ⟶ C(-, c) ⊗ Δ[n+1]`);
* `projective_wfs`, `projective_wfs_fibration` — these are weak factorisation systems;
* `injective_factorization` — every morphism factors as a monomorphism followed by an injective
  trivial fibration: we show `Cᵒᵖ ⥤ SSet` has enough injectives (`enoughInjectives_functor`) and
  factor `f : X ⟶ Y` as `X ⟶ Y × I ⟶ Y` with `X ↪ I` injective (`hasFactorization_mono_rlp`);
* `injective_wfs` — (monomorphisms, injective trivial fibrations) is a weak factorisation system;
* `projCofibrations_le_injCofibrations`, `injTrivialFibrations_le_projTrivialFibrations` — the
  comparison between the two structures.

## Scope

Weak equivalences are not treated: Mathlib does not yet provide the Kan–Quillen model structure
on `SSet` (weak equivalences, and the fact that trivial Kan fibrations are exactly the Kan
fibrations which are weak equivalences), so we do not build a full `ModelCategory` instance. The
results above are the lifting/factorisation parts (CM4, CM5) of both structures, with trivial
fibrations described by their standard lifting characterisation.
-/
````

### `Sovereign/HyperBeam/Instance.lean`

Content ID `c2333b59218af2fd`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L4–L19**

````text
/-!
# The neuro-symbolic hyperbolic beam engine over the existing stack

* `TacticTable` — `b` goal-directed tactics: tactic `i` names a kernel rule and, given the
  current goal, proposes the premises that remain to be proved (backward chaining).
* `goalDirected T K G` — the proof space whose states are goal stacks (`none` for a failed
  tactic); a tactic script is replayed into a proof tree by `TacticTable.build`
  (untrusted: the kernel `K` has the last word).
* `neuroSpace T lib G` — the instance with the strict, `sorry`-rejecting kernel
  `Sovereign.Repair.strict lib`. Every path returned by hyperbolic beam search is a
  `NeuroBridge.CertifiedPath`, contains no `sorry`, and its goal is valid when the library is
  (`neuro_search_sound`).
* A worked example: for the goal `2 = 2` with two tactics, a genuine reflexivity step and a
  `sorry` hole, the gate rejects the hole (`exSpace_rejects_hole`) and hyperbolic beam search
  returns the genuine proof (`exSpace_found`).
-/
````

### `Sovereign/HyperBeam/ProofTree.lean`

Content ID `bbb6a7255b2522dd`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L134–L134**

````text
/-- Applying tactic `i` at `v` reaches a proof state not yet visited on the path. -/
````

### `Sovereign/InvariantRepair/Engine.lean`

Content ID `44254b63730c4c45`; 1 byte-identical path(s); full file source review; see R15; not build-verified.

**L4–L37**

````text
/-!
# The autonomous invariant synthesizer and proof-repair engine

**Repaired proof trees.** A repaired proof is a proof tree `PTree (IRule C)` in the sense of
`Sovereign.Compression`/`Sovereign.HyperBeam`, checked by the rule system `kernel L sem`:

* `nil` proves `inv []` (the empty invariant);
* `push c` turns a proof of `inv A` into a proof of `inv (c :: A)`, provided `c` is inductive
  relative to `A` (`relIndB`);
* `close` turns a proof of `inv A` into a proof of `safe`, provided `A` implies safety.

`kernel_sound` proves the rule system sound for the intended semantics `IValid`
(`inv A` = "every reachable state satisfies `A`", `safe` = "every reachable state is safe").

**Admission gate.** `admitB t` accepts a tree iff the kernel certifies it as a proof of `safe`
and it is acyclic in the sense of `Sovereign.HyperBeam.acyclicB` (no formula is derived twice
on a branch). `admitted_sound`: **every admitted tree — whoever produced it — proves that all
reachable states of the loop are safe.**

**Synthesis.** `synth` runs the abduction loop: while the current certificate does not close
the goal, `abduce` (`Sovereign.InvariantRepair.Abduction`) picks, among the pool lemmas that are
inductive relative to the current strata, the one at minimal hyperbolic distance from the
broken goal state, pushes it as a new stratum, and removes it from the pool. `repair` runs
`synth` on the whole library and returns the certificate tree only if the gate admits it.

Main guarantees:
* `repair_admitted`, `repair_sound`: the output is admitted, hence verified.
* `repair_eq_some_iff`: the gate only fails when the synthesized strata do not imply safety.
* `synth_stagesOK`, `synth_suffix`, `synth_inductive` — non-circular stratification,
  monotone growth, inductiveness of the synthesized invariant.
* `synth_stuck`: if synthesis stops without closing the goal, no remaining library lemma is
  inductive relative to the synthesized strata.
* Size bounds: `synth_length_le`, `certTree_size`, `csize_synth_le`, `synthCalls_le`.
-/
````

**L222–L222**

````text
/-- One abduction step from strata `A` with remaining pool `pool`. -/
````

**L225–L225**

````text
/-- The synthesis loop with fuel; returns the final strata and the remaining pool. -/
````

**L303–L304**

````text
/-- **Stuck means genuinely stuck**: with enough fuel, synthesis either closes the goal or no
remaining lemma is inductive relative to the synthesized strata. -/
````

### `Sovereign/InvariantRepair/Geodesic.lean`

Content ID `b1acffade957e9b8`; 1 byte-identical path(s); statements/comments triaged; proof-body review pending.

**L3–L25**

````text
/-!
# Proof-failure trajectories as discrete deviations from geodesics in `Dⁿ`

A symbolic proof attempt visits a sequence of proof states. Embedding every state in the
Poincaré ball `Dⁿ` (`Sovereign.Autonomous.PoincareBall`) turns the attempt into a discrete
trajectory `x₀, x₁, …, x_k` of points of `Dⁿ`, and the goal of the proof into a target point `g`.

A successful, non-wasteful attempt moves along the hyperbolic geodesic towards `g`: every step
`xᵢ → xᵢ₊₁` satisfies `d_H(xᵢ, xᵢ₊₁) + d_H(xᵢ₊₁, g) = d_H(xᵢ, g)`. The **step defect**

  `defect g x y = d_H(x, y) + d_H(y, g) - d_H(x, g) ≥ 0`

measures how far one step leaves the geodesic (it is `≥ 0` by the triangle inequality).

* `totalDefect_eq`: the defects telescope — the total defect of a trajectory equals its
  hyperbolic length plus the remaining distance to the goal, minus the initial distance.
* `onGeodesic_iff`: a trajectory follows the geodesic to `g` (length + remaining distance =
  initial distance) iff every step has defect `0`.
* `firstDev`: the index of the first step with positive defect — the point where the proof
  attempt *broke*. `firstDev_eq_none_iff` and `firstDev_spec` characterise it, and
  `brokenState` is the proof state at which the deviation starts; it is the goal state handed
  to the lemma-abduction operator.
-/
````

**L71–L71**

````text
/-- **Telescoping**: total defect = length + remaining distance − initial distance. -/
````

**L81–L82**

````text
/-- The trajectory follows the hyperbolic geodesic towards `g`: its length plus the remaining
distance equals the initial distance to `g`. -/
````

**L169–L170**

````text
/-- At the broken state, the next step of the attempt strictly moves away from the geodesic:
the detour through the next state is strictly longer than going straight to `g`. -/
````

**L183–L184**

````text
/-- The remaining distance to the goal after a trajectory equals the initial distance minus the
distance travelled plus the accumulated defect: every unit of deviation is lost progress. -/
````

### `Sovereign/Meta/GBNF/Lean4AstSyntax.lean`

Content ID `78534f39c1642d4d`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L45–L45**

````text
/-- The remaining characters. -/
````

### `Sovereign/Meta/KernelSelfAudit.lean`

Content ID `8ffe788593e121b9`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 8 of the 11
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 7 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. 1 theorem(s) here
are flagged as weak in `sovereign/artifacts/CLAIM_GAP.txt`. The header below uses the word(s) "mass
gap"; read them as motivation, not as a description of what is proved. What is proved is exactly the
Lean statements. No theorem in this module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/Meta/MillenniumImpactAudit.lean`

Content ID `6e09b5c1d83b7c95`; 1 byte-identical path(s); full file source review; see R31; not build-verified.

**L22–L78**

````text
/-!
# What the Stiefel/cubature theorems do — and do not — change for the Clay problems

The latest batch of results in this development
(`StiefelSpectrumStrong`, `StiefelFrameCensus`, `StiefelCubature`) consists of

* arithmetic laws for the `G₂` Weyl dimension, the `SU(2)`-singlet multiplicity and the
  Casimir eigenvalue on `V₂(ℝ⁷) ≅ G₂/SU(2)`,
* the census of the 168 sedenion cross-octet zero-divisor 2-frames, and
* the exact cubature identity `Mᵀ M = 24 · I₂₁` together with the diagonalisation of the
  projected annihilation operator, whose spectrum is `{-8 (×7), 0 (×14)}`.

This module answers, formally, the question of what those theorems do to the Clay
Millennium problems.  It has three parts.

## 1. The logical audit

`implication_from_theorem_iff`: if `p` is already a theorem, then `(p → q) ↔ q`.  So a
"reduction" of any open problem `C` to one of the finished theorems above is *logically
identical to `C` itself*: it transports no difficulty.  The instances
`cubature_reduction_iff`, `frame_census_reduction_iff`, `spectral_coincidence_reduction_iff`
and `stiefel_to_riemann_iff` record this for the concrete theorems and, in the last case,
for the Riemann hypothesis as stated here (`RiemannHypothesisStatement`).  Each of the
three theorems is moreover a statement about a *finite* object (a fixed 168 × 21 integer
matrix, a fixed 168-element list) or about an explicit quadratic form in two natural
numbers, so nothing in them is even expressible in the analytic vocabulary of the Clay
problems.

## 2. Why the "mass gap" of the discrete model is not a mass gap

The one number in the new batch that has the shape of a Clay-type statement is the
spectral gap `-8` of the projected annihilation operator.  Here it is explained away:

* `annihilation_bipartite`: the annihilation graph on the 168 zero divisors is **bipartite**,
  the two sides being the two values of the cross-product harmonic sign
  `crossSign (i, j, s, t) = s · t · sign(eᵢ × eⱼ)`.
* `sector_sign_eigenvector`: consequently each of the seven charge sectors contributes a
  `±1` eigenvector of the adjacency operator with eigenvalue exactly `-8`, and these are
  the seven cross-product directions that `StiefelCubature.projected_adjacency` sees.
* `abs_eigenvalue_le_row_bound` and `annihilation_eigenvalue_abs_le_eight`: `8` is the
  *a priori* bound for the modulus of any eigenvalue of an `8`-regular graph.

So `-8` is the extremal value permitted by regularity, attained for the trivial reason
that a `ℤ/2` sign symmetry makes the graph bipartite (`annihilation_gap_is_extremal`).  A
gap forced by bipartiteness carries no dynamical information, which is exactly the
difference between it and the Yang–Mills mass gap.

## 3. The one genuine bridge: the lowest continuum eigenspace

`stiefel_spectral_gap` and `stiefel_gap_attained_iff`: the smallest non-zero Casimir
eigenvalue on `V₂(ℝ⁷)` is `6`, attained only at the highest weight `(1,0)`, and
`lowest_eigenspace_dim_eq_21` its eigenspace has dimension
`g2_dim 1 0 · su2_singlet_mult 1 0 = 7 · 3 = 21` — precisely the number of harmonics that
the 168 discrete frames integrate exactly (`harmonic_dimension`).  This is a statement
about a compact 11-manifold and a finite graph; it is not a statement about the
Navier–Stokes equations on `ℝ³`, and no claim to the contrary is made here.
-/
````

### `Sovereign/Meta/ReasoningStoreAudit.lean`

Content ID `804ebf366ed2b493`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L56–L59**

````text
/-! The one remaining emitted certificate — the sedenion annihilation
`(e₁ + e₁₀)(e₄ − e₁₅) = 0` — is the only one that mentions the algebra at all; it lives in
`ReasoningStoreAuditSedenion` (its `MonographTheorems` dependency cannot be imported
alongside `AutonomousDiscovery`, see the note there). -/
````

### `Sovereign/Meta/SkeletonEngineCore.lean`

Content ID `73b717b56cc09bbb`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L121–L125**

````text
/--
`decompose done todo goal` is the list of leaf obligations obtained by exhaustively
applying invertible structural rules.  `done` holds hypotheses already inspected (atoms
and implications), `todo` holds hypotheses still to inspect.
-/
````

### `Sovereign/Meta/SkeletonEngineTactics.lean`

Content ID `96ecaf1b3e09c268`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L28**

````text
/-
# Skeleton Engine — tactic layer

The stages proved correct in `SkeletonEngineCore`, `SkeletonEngineVerifier`,
`SkeletonEngineOptimizer` and `SkeletonEngine` are exposed here as tactics and commands
that act on *real* Lean goals:

| stage        | tactic / command                            |
|--------------|---------------------------------------------|
| skeletonizer | `skeletonize`                               |
| formalizer   | `skeletonize?`, `skeleton_report`           |
| verifier     | `prop_engine`, `#engine_audit`              |
| optimizer    | `engine`                                    |

* `skeletonize` applies only invertible steps (`intro`, `And.intro`, destructing `∧`/`∨`
  hypotheses, closing trivial goals), mirroring `SkeletonEngine.decompose`.
* `skeleton_report` prints the remaining obligations as self-contained `example … := by
  sorry` statements, i.e. it formalizes the skeleton as text one can paste into a file.
* `prop_engine` closes a propositional goal *by reflection through the verified decision
  procedure* `SkeletonEngine.tautB`: the goal is reified into `Form`, `tautB` is evaluated
  by the kernel, and `SkeletonEngine.tautB_iff_valid` turns the Boolean result into the
  proof.  Nothing about the tactic has to be trusted — the proof term it produces is
  checked by the kernel like any other.
* `engine` is the full pipeline on a Lean goal: skeletonize, discharge every obligation
  that can be verified, report the residual ones.
* `#engine_audit foo` reports the axioms `foo` depends on and flags any dependence on
  `sorryAx`.
-/
````

### `Sovereign/Meta/StateOfThoughtStopping.lean`

Content ID `80cc44ab78a1b462`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L19**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The windowed stopping rule as a counter automaton

Roadmap item 2.2 of `docs/STATE_OF_THOUGHT_ROADMAP.md`. The training-free stopping rule
`tfStop` of the appendix fires at step `t` when over the last `r` steps the entropy and the
velocity stay below their thresholds and the consistency is positive.

* `tfStop_mono_threshold` : the rule is monotone in both thresholds;
* `runLen` : a one-counter automaton reading the feature stream (length of the current run of
  "good" steps);
* `tfStop_iff_runLen` : the rule fires at `t` iff `min r (t + 1) ≤ runLen t`, so it can be
  evaluated online with a single counter instead of a window buffer;
* `tfStop_of_good_from` : if the conditions hold at every step from `t₀` on, the rule fires
  at step `t₀ + r − 1`, i.e. within `r − 1` steps (bounded latency);
* `tfStop_not_of_bad` : conversely it never fires while the current step is bad.
-/
````

### `Sovereign/Meta/TopologicalEntropyBarrier.lean`

Content ID `587f9767945ea09f`; 1 byte-identical path(s); full file source review; see R37; not build-verified.

**L178–L188**

````text
/-- *Scope (truth-in-labelling):* this theorem checks fixed numerical facts about the finite model
defined in this file. It has no universally quantified variable and does not settle an open
problem. Formerly named `op063_topological_entropy_barrier_settled`.

Master Theorem: Persistent topological Shannon entropy S_top ≥ 0.80 bits is an exact
    necessary and sufficient condition to prevent collapse into degenerate trivial tautologies
    during autonomous theorem generation.
    - Necessary: S_top < 0.50 bits collapses with probability > 1 - 2^{-3000}.
    - Sufficient: S_top*(1/4) > 0.80 bits ensures exploration of non-contractible 1-cycles (H₁ ≥ 1)
      in the MANIFOLD_STABLE regime.
    - Settles Open Problem OP-063. -/
````

### `Sovereign/Meta/UpgradeEngine/SelfImprovement.lean`

Content ID `3492906f5c32e32f`; 1 byte-identical path(s); full file source review; see R18; not build-verified.

**L1–L8**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 1 of the 15
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
never mentions the real numbers, so it contains no continuum model of any kind. The header below
uses the word(s) "settled"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/NeuroBridge/Proposer.lean`

Content ID `ccc368db77c8d075`; 1 byte-identical path(s); full file source review; see R19; not build-verified.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 1 of the 27
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 6 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "unconditional"; read them as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/NumberTheory/ABCDensityObstruction.lean`

Content ID `838a64dcff97cb22`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L29**

````text
/-!
# ABC Triple Asymptotic Density Power Law Obstruction (HYP-105, OP-048)
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

Formal verification settling Open Problem OP-048 in the negative (Falsification):
1. The conjectured power law: N(X, ε) ~ c_ε * X^{1/(1+ε)} predicts that for any ε > 0,
   N(X, ε) -> ∞ as X -> ∞ with power exponent α = 1 / (1 + ε) > 0.
2. Under the standard ABC conjecture, for every ε > 0 there exist only finitely many
   coprime triples with quality q > 1 + ε, meaning N(X, ε) = O(1) is eventually constant.
3. Empirical counts from the ABC@home distributed search up to X = 10^18 for ε = 0.4:
   - N(10^6, 0.4) = 48
   - N(10^9, 0.4) = 84
   - N(10^12, 0.4) = 112
   - N(10^15, 0.4) = 132
   - N(10^18, 0.4) = 148
4. Power law refutation:
   - Predicted count at X = 10^18 under α = 1/1.4 ≈ 0.714 exceeds 10^10 triples.
   - Discrepancy ratio: N_predicted / N_actual > 10^8.
   - Empirical exponent between 10^6 and 10^18 is < 0.05, strictly less than 1/(1+ε) ≈ 0.714.
   - Falsifies the conjectured power law in accordance with OP-048 falsification criteria.
-/
````

**L82–L85**

````text
/-- Master theorem settling Open Problem OP-048 in the negative (Falsification):
    Empirical counting up to X = 10^18 definitively contradicts the power law
    N(X, ε) ~ c_ε * X^{1/(1+ε)}, proving that high-quality ABC triples do not
    follow an unconstrained power law density. -/
````

### `Sovereign/NumberTheory/BakerLatticeBound.lean`

Content ID `69b97da2b64b16db`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L24**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 4 of the 6
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the word "settled"; read it as motivation, not as a description of what is
proved. What is proved is exactly the Lean statements. No theorem in this module settles an open
problem or establishes a physical result.

  Sovereign Formal Verification Library
  Module: Sovereign.BakerLatticeBound
  Open Problem: OP-047 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-146 (Effective Baker-Type Lower Bounds from Leech Lattice and Cayley–Dickson Twisted-XOR Embeddings)

  This module formalizes:
  1. The Leech lattice Lambda_24 geometric invariants:
       - Dimension = 24.
       - Minimal squared Euclidean norm = 4.
       - Minimal vector length = 2.
       - Kissing number = 196,560.
  2. The discrete Phi-surgery logarithmic quantum:
       - Delta_log = ln(25/16) = 2 * ln(5/4) > 0.
  3. The geometric Baker-type lower bound on linear forms in logarithms:
       - |Lambda| >= (2 * Delta_log) / (||b||^n + 1).
  4. The master resolution theorem for OP-047.
-/
````

### `Sovereign/NumberTheory/EffectiveABCConstant.lean`

Content ID `ba24d9ee8927584e`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 4 of the 14
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 17 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "settled"; read them as motivation, not as a description of what is proved. What is
proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

**L11–L25**

````text
/-
  Sovereign Formal Verification Library
  Module: Sovereign.EffectiveABCConstant
  Open Problem: OP-042 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-153 (Effective Uniform Constant C_ε for Masser–Oesterlé ABC Conjecture)

  This module formalizes:
  1. The explicit, computable uniform ABC constant:
       C_ε = exp(K_leech / ε)
     where K_leech = (25 / 16) / ln(25 / 16) ≈ 3.5011 is determined by the
     minimax Φ-surgery contraction factor κ = 16/25 and the Leech minimal norm.
  2. Strict positivity and monotonicity of C_ε for all ε > 0.
  3. Boundedness on extremal ABC hits, including the Reyssat triple (q ≈ 1.6299).
  4. The master resolution theorem settling OP-042.
-/
````

### `Sovereign/NumberTheory/HallsConjectureReduction.lean`

Content ID `876406296e1630e9`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L18**

````text
/-
  Sovereign Formal Verification Library
  Module: Sovereign.HallsConjectureReduction
  Open Problem: OP-049 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-145 (Hall's Conjecture Exponent Reduction from ABC and Davenport Polynomial Sharpness)

  This module formalizes:
  1. The formulation of Marshall Hall's Conjecture (1970) and Weak Hall's Conjecture:
       |x^3 - y^2| >= C_eps * x^(1/2 - eps) for all non-trivial integer solutions.
  2. The exact mathematical reduction showing that the Masser–Oesterlé ABC conjecture
     implies the Weak Hall bound with explicit exponent delta = 3 * eps_0 / (1 + eps_0).
  3. Davenport's Theorem (1965) and Mason–Stothers polynomial ABC theorem:
       deg(g^2 - f^3) >= (1/2) * deg(f) + 1
     with certified sharpness on the Davenport witness (f = t^2 + 2, g = t^3 + 3t).
  4. Kernel-checked arithmetic verification of Noam Elkies' 1998 world-record near-miss:
       x = 5853886516781223, y = 447884928428402042307918
       |y^2 - x^3| = 1641843.
-/
````

### `Sovereign/Organism/RecurrentNovae.lean`

Content ID `bc835dc7521dfc55`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L252–L254**

````text
/-- Bounds on the number of eruptions already emitted but not yet seen by 2026: the light from
the last `distLy` years is still in flight, and a cycle lasts between `intervalMin` and
`intervalMax` years. -/
````

**L263–L264**

````text
/-- Status of the next-eruption window `[last + intervalMin, last + intervalMax]` in 2026:
`0` = window already closed (overdue), `1` = window open, `2` = window not yet open. -/
````

### `Sovereign/Physics/ChiralAnomalyCancellation.lean`

Content ID `141981f610ace7be`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L22**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 9 of the 10
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the word "unconditional"; read it as motivation, not as a description of what
is proved. What is proved is exactly the Lean statements.

Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gravitational & Gauge Chiral Anomaly Cancellation (OP-060, HYP-131)

This module formalizes:
1. The chiral grading and index on the 21 generational blocks of the 32D zero-divisor manifold.
2. In each generational block of 16 fermion vertices, exactly 8 are Left-Handed (8_L)
   and 8 are Right-Handed (8_R), forming two disjoint K_{4,4} bipartite subgraphs.
3. The local chiral index tr(γ₅) = 8_L - 8_R = 0 vanishes identically in every block.
4. Complete local gravitational anomaly cancellation: A_grav = tr(γ₅) = 0.
5. Global anomaly cancellation across all 21 generational blocks: ∑ tr(γ₅) = 21 · 0 = 0.
6. Universal parity theorem: the anomaly coefficient is strictly even (identically zero),
   unconditionally refuting the existence of any odd chiral anomaly coefficient.
7. Complete formal settlement of Open Problem OP-060.
-/
````

### `Sovereign/Physics/CosetHarmonicsGlueball.lean`

Content ID `87f9ce1de507103a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L39**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 15 of the 16
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the words "mass gap", "yang-mills", "yang–mills"; read them as motivation, not
as a description of what is proved. What is proved is exactly the Lean statements. No theorem in
this module settles an open problem or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Mass-Gap & Particle Spectrum from V₂(ℝ⁷) ≅ G₂/SU(2) Coset Harmonics (Tier 2 Horizon Target)
  **Epistemic Classification:** [A] Representation Theory & Yang-Mills Gauge Harmonics

This module formally certifies the Laplace-Beltrami spectral gap, Casimir eigenvalue ratios,
and G₂ → SU(3)_c branching rules governing the pure gauge glueball spectrum (including the
X(2370) scalar glueball candidate and tensor glueball 2⁺⁺).

Key Theorems Formally Certified:
1. Universal Laplace-Beltrami Mass-Gap on V₂(ℝ⁷):
   - Every non-trivial representation (p, q) ≠ (0, 0) satisfies λ(p, q) ≥ 6.
   - Ground state λ(0, 0) = 0 is unique.
2. Exact Casimir Eigenvalue Ratios:
   - Fundamental level (1, 0): λ(1, 0) = 6.
   - Adjoint level (0, 1): λ(0, 1) = 12.
   - Exact ratio: λ(0, 1) = 2 · λ(1, 0).
3. Higher Representation Ratios:
   - 27-dim level (2, 0): 3 · λ(2, 0) = 7 · λ(1, 0) (ratio 7/3).
   - 64-dim level (1, 1): 2 · λ(1, 1) = 7 · λ(1, 0) (ratio 7/2).
   - 77-dim level (0, 2): λ(0, 2) = 5 · λ(1, 0) (ratio 5).
4. G₂ → SU(3)_c Branching Dimension Preservation:
   - Fundamental 7 → 3 ⊕ 3̄ ⊕ 1 (dim 7 = 3 + 3 + 1).
   - Adjoint 14 → 8 ⊕ 3 ⊕ 3̄ (dim 14 = 8 + 3 + 3).
   - 27-dim → 8 ⊕ 6 ⊕ 6̄ ⊕ 3 ⊕ 3̄ ⊕ 1 (dim 27 = 8 + 6 + 6 + 3 + 3 + 1).
5. Glueball Mass Squared Calibration:
   - Calibrated against the scalar glueball X(2370) (M ≈ 2395 MeV):
     M²(2⁺⁺) = 2 · M²(0⁺⁺), bounding M(2⁺⁺) in [3380, 3390] MeV,
     in rigorous agreement with Lattice QCD (3400 ± 100 MeV).
-/
````

### `Sovereign/Physics/FaddeevPopovDeterminants.lean`

Content ID `cc169eca79d816fd`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
6 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 22 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "singularit"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/Physics/GlueballColorConfinement.lean`

Content ID `8e91b8382b306fff`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L2–L14**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 5 of the 5
theorems in this module have no quantified variable: they check facts about fixed numbers. The
file never mentions the real numbers, so it contains no continuum model of any kind. The header
below uses the words "mass gap", "yang–mills"; read them as motivation, not as a description of
what is proved. What is proved is exactly the Lean statements. No theorem in this module settles
an open problem or establishes a physical result.

  Sovereign Formal Verification Library
  Module: Sovereign.Physics.GlueballColorConfinement
  Author: Sovereign Research Collective
  Epistemic Classification: [A] Machine-Checked Formal Identities
-/
````

### `Sovereign/Physics/MillenniumFoundations.lean`

Content ID `df9adff940b681df`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L29**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 7 of the 11
theorems in this module have no quantified variable: they check facts about fixed numbers. The
file never mentions the real numbers, so it contains no continuum model of any kind. The header
below uses the word "millennium"; read it as motivation, not as a description of what is proved.
What is proved is exactly the Lean statements. No theorem in this module settles an open problem
or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Autonomous Formal Engine

# Millennium Foundations & Elementary Particle Governance

This module establishes machine-checked formal theorems for:
1. Standard Model Gauge Governance and Embedding in E8 (HYP-181)
2. Exact Chiral Anomaly Cancellation (HYP-182)
3. Hodge Cycles and the Lefschetz (1,1) Theorem (HYP-183)
4. Birch and Swinnerton-Dyer Elliptic Curve Rank Invariant (HYP-184)
5. Riemann Hypothesis Critical Line Reflection & Zero Localization (HYP-185)

Note (audit): the statements below are numerical identities, dimension counts,
or instances of reflexivity, so they do not constrain the mathematics they are
named after (in particular `lefschetz_one_one_dimension_bound` is `x = x`, and
`bsd_rank_zero_soundness` is `0 = 0`).  They are kept unchanged for the record;
`MillenniumStrong.lean` proves a theorem with actual content under each of the
five headings, and shows that the `HodgeDiamond` structure below cannot model a
K3 surface.
-/
````

### `Sovereign/Physics/MillenniumStrong.lean`

Content ID `42edcb8a64f8111a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 7 of the 35
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 12 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "millennium"; read them as motivation, not as a description of what is proved. What
is proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Physics/SedenionMaxwell.lean`

Content ID `55acb0569eb66506`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L3–L35**

````text
/-!
# 16D sedenion Maxwell equations `D F = J`

**Setting.**  Spacetime is `ℝ⁴ = {(t, x₁, x₂, x₃)}`.  The field is `F = E + i B + M`, a
`C²` map into the complexified sedenions (`Fin 16 → ℂ`, see `SedenionMaxwellAlgebra`):
`E + i B` (`embEB`) sits on the quaternion units `e₁, e₂, e₃`, where `i` is the complex unit
and commutes with every sedenion unit.  The remaining 12 complex components on `e₄, …, e₁₅`
form the hidden field `M` (`IsHidden`).  The operator is
`D = -i ∂_t + e₁ ∂₁ + e₂ ∂₂ + e₃ ∂₃`, acting by left sedenion multiplication (`Dop`).

**Results.**

* `sedenion_maxwell_iff` — `D F = J_EM + J_M` holds at a point iff Maxwell's equations
  (`MaxwellAt`: `∇·E = ρ`, `∇·B = ρₘ`, `∇×E + ∂_t B = -jₘ`, `∇×B - ∂_t E = j`) hold there and
  the hidden sector satisfies `D M = J_M`.
* `fieldAssociator_eq_zero` — **the associator `[D, D, F] = (D D) F - D (D F)` is identically
  zero** for every `C²` sedenion field, even though the coefficients of `D` do not associate
  (`coefficient_associator_ne_zero`).  So every `C²` field lies in the associator kernel
  (`assocKernel_of_contDiff`).
* `associator_generates_no_monopole` — so the associator produces **no** magnetic charge.  The
  request's claim that `[D, D, F]` *generates* localized monopole charges is false in this
  formalisation.  Magnetic charge enters only through an explicit source `ρₘ` in `J`.
* `divS_curlS_eq_zero`, `monopole_charge_zero_of_smooth_potential`,
  `sedenion_monopole_needs_string` — if `B = ∇ × A` with a global `C²` potential (no Dirac
  string), then `ρₘ = 0`.  A non-zero monopole charge therefore always rules out a global
  string-free potential.
* `poynting_theorem` — `∂_t u + ∇·S = -j·E - jₘ·B` with `u = (|E|²+|B|²)/2`, `S = E × B`.
* `poynting_conservation_on_assocKernel` — for a `C²` solution of `D F = J` with
  current-free electromagnetic source, `F` is in the associator kernel and
  `∂_t u + ∇·S = 0` everywhere.
* `symmetrised_associator_outside_octHalf` — the cancellation depends on the 4D base: a
  derivative direction carrying a coefficient such as `e₁₀` would break it.
-/
````

### `Sovereign/Physics/SedenionYangMills.lean`

Content ID `ab338fda3de7d2ab`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 3 of the 46
theorems in this module have no quantified variable: they check facts about fixed numbers. The file
mentions the real numbers 68 time(s); every continuum object it uses is one defined explicitly in
this file or in Mathlib, not the equations or field theories its vocabulary names. The header below
uses the word(s) "yang–mills"; read them as motivation, not as a description of what is proved. What
is proved is exactly the Lean statements. No theorem in this module settles an open problem or
establishes a physical result.
-/
````

### `Sovereign/Pipeline/Cavity/Attractor.lean`

Content ID `17425ea1304dffad`; 1 byte-identical path(s); full file source review; see R23; not build-verified.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
27 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 31 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "singularit"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/Pipeline/Fidelity.lean`

Content ID `9e63f7fcafcaa13e`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
14 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 25 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "singularit"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `Sovereign/PoUW/Consensus.lean`

Content ID `d90d4ef0740c9aa1`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L288–L289**

````text
/-- Block `b` is *final* at height `i` in state `st`: under every future schedule, every honest
ledger that reaches height `i` holds `b` there. -/
````

### `Sovereign/ProofHomology/Engine.lean`

Content ID `a53fe8b8c6b96637`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L111–L112**

````text
/-- The main loop: `r` remaining rounds, current depth `d`, current budget `B`. Returns the
certificate (if any) and the total number of gate checks. -/
````

### `Sovereign/Quantum/AssociatorSubsystemCode.lean`

Content ID `586b8466e0511711`; 1 byte-identical path(s); source definitions and proofs reviewed; header triaged; see R42; not build-verified.

**L170–L178**

````text
/-- *Scope (truth-in-labelling):* this theorem checks fixed numerical facts about the finite model
defined in this file. It has no universally quantified variable and does not settle an open
problem. Formerly named `op025_associator_subsystem_code_settled`.

Master Theorem settling Open Problem OP-025:
    Synthesizes a family of subsystem quantum codes [[L², 1, (L-1)², L]] where
    gauge generators correspond to associator 2-cells, stabilizers are generated
    by closed associator cycles, the Hilbert space decomposes as k + r + s = n,
    and k = 1 logical qubits are preserved for all L ≥ 2. -/
````

### `Sovereign/Quantum/MultiregularCSSClassification.lean`

Content ID `9db3cda71aeb9689`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L32**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Classification of CSS Codes from Multiregular Higher-Tower Sectors (OP-029, HYP-128)

This module formally settles Open Problem OP-029 (Level L3, Domain 3: Quantum Error Correction & CSS Codes):
"For multiregular sectors at D=128 (29 sectors) and D=256 (82 sectors), classify which sectors satisfy
A_chi A_chi^T == 0 (mod 2) and determine their CSS parameters [[N, K, d]]."

## Key Theorems Formally Certified:
1. Exact Multiregular Sector Counts:
   - D = 128 (n = 7): exactly 29 multiregular sectors (HYP-112).
   - D = 256 (n = 8): exactly 82 multiregular sectors (HYP-112).

2. Universal CSS Code Parameter Equations for Dimension D = 2^n ≥ 64:
   - Block length (physical qubits): N(D) = 2(D - 4).
   - Check matrix rank over GF(2): r(D) = (D - 8) / 2.
   - Logical dimension: K(D) = N(D) - 2 * r(D) = 2(D - 4) - (D - 8) = D.
   - Quantum distance: d(D) = 2, from identical columns of twin-pair zero divisors.

3. Concrete Parameters for D = 128 and D = 256:
   - D = 128: [[248, 128, 2]] with rank 60 across all 29 multiregular sectors.
   - D = 256: [[504, 256, 2]] with rank 124 across all 82 multiregular sectors.

4. Commutativity & Falsification Refutation:
   - CSS commutativity condition is defined by H_X * H_Z^T == 0 (mod 2).
   - For symmetric codes (H_X = H_Z = A_chi), commutativity is identically equivalent
     to self-orthogonality A_chi * A_chi^T == 0 (mod 2).
   - Therefore, a sector with A_chi A_chi^T == 0 (mod 2) cannot fail commutativity.
-/
````

**L140–L146**

````text
/-- *Scope (truth-in-labelling):* this theorem checks fixed numerical facts about the finite model
defined in this file. It has no universally quantified variable and does not settle an open
problem. Formerly named `op029_multiregular_css_settled`.

Full Settlement of Open Problem OP-029:
    All multiregular sector counts, universal parameters [[248, 128, 2]] and [[504, 256, 2]],
    and commutativity refutation are formally certified. -/
````

### `Sovereign/Quantum/QuantumSingleton.lean`

Content ID `63090ced764da8f7`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L25**

````text
/-
Copyright (c) 2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quantum Singleton bound for stabilizer codes

For a stabilizer code on `n` qubits with `k ≥ 1` logical qubits and distance `d`,
`k + 2(d - 1) ≤ n` (`quantum_singleton`).  The proof here is purely linear-algebraic over
`𝔽₂`, in the symplectic model of `Sovereign/Quantum/SymplecticStabilizer.lean`:

1. **Support and restriction.**  `restrict A` keeps the tensor factors in a region `A` and
   replaces the others by the identity.  Paulis with disjoint supports commute
   (`symp_eq_zero_of_disjoint`).
2. **Correctable regions.**  A region `A` is *correctable* if every element of the
   centralizer supported in `A` is a stabilizer.  Any region with fewer than `d` qubits is
   correctable (`correctable_of_card_lt`).
3. **Cleaning lemma** (`cleaning`): if `A` is correctable, every logical operator is
   equivalent, modulo the stabilizer, to one acting trivially on `A`.  Proof: the orthogonal
   complement of `restrict A (S) + (Paulis supported off A)` is exactly the set of stabilizers
   supported in `A`, and a logical operator is orthogonal to those.
4. **Counting** (`logicalQubits_add_card_le`): if `A`, `B` are disjoint correctable regions,
   then `k + |A| + |B| ≤ n`.  The logical operators supported off `A` surject onto the
   `2k`-dimensional logical space and, after restriction to the remaining region `C`,
   inject modulo the stabilizer (because `B` is correctable), so `2k ≤ 2|C|`.
-/
````

**L211–L211**

````text
-- (2) Restricting `NB` to the remaining region `Cr`.
````

### `Sovereign/Quantum/QuantumThresholdObstruction.lean`

Content ID `4b2129ff59f4a761`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L32**

````text
/-!
# Quantum Threshold Obstruction Theorem (HYP-102, OP-024)
  **Epistemic Classification:** [C] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

Formal verification settling Open Problem OP-024:
1. Symmetric CSS code parameter structures:
   - D=64:  [[120, 64]] with N = 120, K = 64, check weight 56, rank 28.
   - D=128: [[248, 128]] with N = 248, K = 128, check weight 120, rank 60.
2. Exact code distance d = 2 across all dimensions:
   - Preserved from HYP-083 (QuantumCodeDistance.lean).
   - Twin-vertex degeneracy creates non-trivial weight-2 logical operators.
3. Twin pair counting and linear scaling:
   - D=64:  A_2 = 180 twin pairs in parity checks H_X, H_Z.
   - D=128: A_2 = 372 twin pairs in parity checks H_X, H_Z.
   - Exact scaling identity: 2 * A_2(N) = 3 * N across both levels.
4. Threshold vanishing obstruction:
   - Every twin pair e_u + e_v forms an undetectable weight-2 error with syndrome s = 0.
   - Any syndrome-based decoder (including BP-OSD) outputs zero correction, failing
     to correct twin errors.
   - As N increases, weight-2 logical error occurrence probability strictly increases:
     A_2(248) = 372 > A_2(120) = 180.
   - Consequently, the asymptotic crossing threshold is identically zero: p_th = 0.
-/
````

### `Sovereign/Quantum/RateDistanceProduct.lean`

Content ID `602715ab400076c2`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L26**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** 19 of the 22
theorems in this module have no quantified variable: they check facts about fixed numbers. The
header below uses the word "settled"; read it as motivation, not as a description of what is
proved. What is proved is exactly the Lean statements. No theorem in this module settles an open
problem or establishes a physical result.

Copyright (c) 2026 Sovereign Autonomous Research Engine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Research Collective
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

! HYP-084: Asymptotic Rate-Distance Product Vanishing in Cayley-Dickson CSS Towers
Settles Open Problem OP-026:
Proves that in the infinite tower of Cayley-Dickson symmetric CSS stabilizer codes
[[N(D), K(D), d(D)]] with N(D) = 2(D - 4), K(D) = D, and d(D) = 2 (HYP-083):
1. The rate-distance product is given by P(D) = (K * d) / N^2 = 2D / (2(D - 4))^2.
2. The sequence is strictly monotonically decreasing along the tower:
   P(16) = 1/18 > P(32) = 1/49 > P(64) = 2/225 > P(128) = 4/961 > P(256) = 2/992.
3. Asymptotic limit lim_{D -> inf} P(D) = 0, proving that the rate-distance product
   does NOT remain strictly positive.
4. For hypergraph product codes where d = Omega(sqrt(N)) = O(D), the product
   P_HGP(D) <= 4 / D likewise vanishes asymptotically.
-/
````

### `Sovereign/Quantum/SpongeAlgebraicDegree.lean`

Content ID `9a65bf935b27629d`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L19**

````text
/-!
# Exact Algebraic Degree of Ramanujan Sedenion Sponge Permutation (HYP-103, OP-051)

Formal verification settling Open Problem OP-051:
1. Sponge state width: b = 32 bytes = 256 bits.
2. Canonical maximum algebraic degree for invertible permutation: d_max = 255.
3. Round 1 lower bound: d(1) >= 16 from 16-bit ARX carry chains and expander branch multiplexing.
4. Exponential doubling progression under non-linear ARX carry recurrence:
   d(r+1) = min 255 (2 * d(r)).
5. Saturation at maximal algebraic degree: d(r) = 255 for all r >= 5.
6. Refutation of falsification threshold: d(8) = 255 >= 128, with strict margin 127.
-/
````

**L103–L110**

````text
/-- *Scope (truth-in-labelling):* this theorem checks fixed numerical facts about the finite model
defined in this file. It has no universally quantified variable and does not settle an open
problem. Formerly named `op051_sponge_algebraic_degree_settled`.

Master theorem settling Open Problem OP-051:
    The 24-round Ramanujan sedenion sponge permutation achieves algebraic degree 255 at round 8
    (strictly refuting the falsification bound 128 by 127 degrees), and maintains maximal degree
    saturation 255 across all rounds 5 through 24. -/
````

### `Sovereign/Refutation/Loop.lean`

Content ID `c4ed707acc28d9ad`; 1 byte-identical path(s); full file source review; see R20; not build-verified.

**L3–L34**

````text
/-!
# The refutation loop

The automated counterexample synthesizer runs a **refutation loop** alongside the conjecturer.
At each round `t`:

1. the (untrusted) conjecture source `propose t` emits candidate conjectures (it may look at the
   conjectures refuted so far);
2. for each candidate not yet refuted, the (untrusted) counterexample synthesizer `search t`
   proposes a witness environment;
3. the trusted checker `certify` evaluates the candidate at the proposed witness (a decidable
   computation) and, if the candidate fails there, packages the failure as a `Refutation`
   certificate — a structure holding the candidate, the witness and a *proof* that the candidate
   fails at the witness;
4. the certificate is appended to the append-only refutation log.

Each certificate `r` yields the **negation theorem** `r.negation : ¬ S.Valid r.cand`, a Lean proof
term checked by the kernel.  Certificates are immutable values: the log only ever grows by
appending (`run_prefix`), an entry at a fixed position never changes (`run_getElem?_stable`), and
the certificate recorded for a conjecture is fixed forever once it exists (`certOf_stable`).

Guarantees (for arbitrary untrusted `propose` and `search`):

* **monotonicity**: the refuted set never shrinks (`refuted_mono`), and grows strictly exactly
  when a round adds a certificate (`refuted_ssubset_iff`);
* **epistemic safety**: every refuted conjecture is invalid (`refuted_not_valid`), no valid
  conjecture is ever refuted (`valid_not_refuted`), so the refuted set is disjoint from every set
  of valid statements, in particular from every knowledge base of verified theorems
  (`disjoint_of_valid`); each conjecture is refuted at most once (`nodup_cands`);
* **completeness**: a candidate proposed at round `t` for which the synthesizer returns a genuine
  counterexample is refuted after round `t` (`refuted_of_search`).
-/
````

### `Sovereign/Speculative.lean`

Content ID `0fd3872f37bb5ef0`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L4–L22**

````text
/-!
# `Sovereign.Speculative`

Modules whose prose describes continuum physics (Navier–Stokes regularity, blowup, turbulence)
that their Lean statements do not model. They are kept, and they still build and are audited,
but they are separated from the verified core so their headers are not mistaken for results.

* `GlobalRegularity`: every quantity is a natural number or an integer. There is no velocity
  field, no PDE and no real analysis. Its theorems are arithmetic facts and implications
  between the stated hypotheses. The real-valued enstrophy decay estimate that it gestures at
  is proved in `Sovereign.Fluid.EnstrophyDecayReal`.
* `SedenionFluidTrinity`: fixed-number checks plus elementary real inequalities such as
  `0 ≤ ω₀ * T` for `ω₀, T ≥ 0`. It does not bear on the regularity of any Navier–Stokes
  system.

Neither module settles an open problem (see `docs/OPEN_PROBLEM_AUDIT.md`).

This module is an index: it imports every module of the cluster.
-/
````

### `Sovereign/Speculative/GlobalRegularity.lean`

Content ID `c7b8518a2a0daa93`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L127–L130**

````text
/-- Theorem 1.6 (Cauchy Forward Trajectory Zero-Divisor Preservation):
    If the temporal evolution preserves the zero-divisor cross product subspace,
    an initial zero-divisor state u0 x_16 omega0 = 0 remains a zero-divisor state
    for all future times t. -/
````

### `Sovereign/Swarm/Convergence.lean`

Content ID `be45cc9668e709ae`; 1 byte-identical path(s); full file source review; see R21; not build-verified.

**L4–L26**

````text
/-!
# Convergence of the adversarial consensus protocol

The game is played in rounds.  In round `k` the adversary first runs an arbitrary schedule of
game events `adv ω k` — it controls the Byzantine nodes and the network, and it is even allowed
to know all random coins `ω` in advance (a clairvoyant, adaptive adversary).  Then an honest
critic probes the lemma under scrutiny `p`: its probe succeeds with probability `prob`
(independently across rounds; `ω k = true`), in which case it publishes the refutation
synthesized by `synthesize` (`Sovereign.Swarm.Dag`).

The coin sequence `ω : ℕ → Bool` is distributed as `searchMeasure prob`, the i.i.d.
Bernoulli(`prob`) product measure of `Sovereign.Autonomous.Ruin`.

**Convergence theorem** (`convergence`).  Under the Byzantine threshold `f < n/3` and honest
verifiers, starting from any reachable state:

1. an ungrounded (false, unproved or `sorry`-containing) lemma is never accepted, in any round,
   on every sample path;
2. if `prob > 0`, it is rejected — permanently — within finitely many rounds with probability `1`;
3. the probability that it is still not rejected after `k` rounds is at most `(1 - prob) ^ k`;
4. every lemma accepted in some round is grounded and keeps an immutable, verifying consensus
   receipt in all later rounds.
-/
````

### `Sovereign/Swarm/Examples.lean`

Content ID `2ceb50df8b3990b9`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L37–L37**

````text
/-- A proposal citing a premise that is not yet derived. -/
````

### `Sovereign/Taxonomy/AcousticVortex.lean`

Content ID `5413a65f1d7fa032`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L9**

````text
/-
**Scope (truth-in-labelling, added by `scripts/audit/annotate_module_scope.py`).** Every one of the
28 theorems in this module has a quantified variable, but each is a statement about the explicit
objects defined here. The file mentions the real numbers 36 time(s); every continuum object it uses
is one defined explicitly in this file or in Mathlib, not the equations or field theories its
vocabulary names. The header below uses the word(s) "singularit"; read them as motivation, not as a
description of what is proved. What is proved is exactly the Lean statements. No theorem in this
module settles an open problem or establishes a physical result.
-/
````

### `co-scientist-outputs/prismatization-cyclotomic/FiniteCyclotomicSketch.lean`

Content ID `43efd63b3c6e28b7`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L99–L116**

````text
/- Remaining finite theorem obligations (not declarations of proved facts):
  * cyclo3 R k composed with X^3 = cyclo3 R (k+1).
  * shifted cyclo3 is Eisenstein over Z at 3; minpoly identification over Q_3.
  * construction of the h arguments above and coefficient-fixing properties.
  * inclusion injective; composite and Galois-equivariance diagrams commute.
  * SpecialStage k is isomorphic to (ZMod 3)[T]/(T^(2*3^k)).
  * F kills T^ceil((2*3^k)/3), which is nonzero at k=0,1,2.
  * j o rho = F and rho o j = F on adjacent special fibers.

  Actual paper layer, intentionally not represented by a fake structure:
  * perfect characteristic-p perfectoid S;
  * punctured FF disc and Berkovich space with diamond-isomorphism iota;
  * iota-equivariance for the actual Frobenius (Definition 3.3.1);
  * cyclotomic perfected disc with q |-> [epsilon^(1/3)] (Example 4.8.4);
  * analytic Cartier divisor, locally analytic group quotient, descent.

  No claim about X^Div1, a comparison equivalence, or the paper's Sen operator.
-/
````

### `four time frequency shift/RequestProject/HRT/ActiveAnalyticAmplitudeReanchor(1).lean`

Content ID `5c800b02fb91e05f`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L61**

````text
/-!
# Active/analytic amplitude reanchoring run

This run eliminates the residual **opaque-`analytic.H` compatibility**

```
  StandardCanonicalAmplitudeCompatibility D.θ a₀ b₀ ad coeffs analytic.H
```

from the downstream contradiction, by **reanchoring** the active/analytic
interface onto the canonical loop-holonomy amplitude
`canonicalLoopHolonomyAmplitude θ coeffs ad` (which is, definitionally, the
canonical gauge amplitude `canonicalGaugeAmplitude θ coeffs ad`).

## Task B — where `analytic.H` is introduced

The amplitude `analytic.H` is the field `H` of the structure
`CriticalMixedActiveAnalyticInterface θ DK a₀ b₀`
(`ConditionalFinalAssembly.lean`):

* `H : ℝ → ℂ`                                  — **arbitrary data**;
* `hH  : AnalyticOnNhd ℝ H (Ioo a₀ b₀)`        — uses `H`;
* `hHne : ∀ s ∈ Ioo a₀ b₀, H s ≠ 0`           — uses `H`;
* `hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q` — uses `H`.

For the canonical loop-holonomy amplitude:

* `hHne` is **proved** (`canonicalGaugeAmplitude_ne_zero`) on the active arc;
* `StandardCanonicalAmplitudeCompatibility` is **proved** by `rfl`
  (`StandardCanonicalAmplitudeCompatibility_canonical`);
* `hH` (analyticity) and `hSres` (resonance membership of the canonical
  amplitude values on a positive-measure set) are the genuine remaining
  active/analytic content, and are now stated **about the concrete canonical
  amplitude** rather than an opaque `H`.

## Task D/E — the reanchored interface and the opaque-`H`-free endpoint

`StandardActiveAnalyticInterfaceCanUseCanonicalAmplitude` packages an
active/analytic interface whose amplitude `H` **is** the canonical loop-holonomy
amplitude.  For it the compatibility is automatic (`rfl`), so the downstream
contradiction
`critical_mixed_final_contradiction_without_opaque_amplitude` no longer requires
an externally supplied compatibility for an opaque `analytic.H`.

A transparent builder `…ofData` reduces this residual to exactly the genuine
active/analytic content **about the canonical amplitude**: the window is active
(`hActive`), the canonical amplitude is analytic (`hH`), and its values lie in
the resonance group on a positive-measure set (`StandardCanonicalAmplitudeResonanceProperty`).

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

**L102–L107**

````text
/-- **`StandardCanonicalAmplitudeResonanceProperty`.**

The genuine remaining active/analytic content, stated about the **concrete**
canonical loop-holonomy amplitude (not an opaque `H`): a positive-measure active
set `S ⊆ (a₀,b₀)` on which the canonical amplitude takes values in the resonance
group of the return times `DK.q`. -/
````

**L147–L153**

````text
/-- **`canonical_active_analytic_interface` / `…ofData` (Task D builder).**

Transparent constructor of the reanchored interface from the genuine remaining
content **about the canonical amplitude**: activeness of the window (`hActive`),
analyticity of the canonical amplitude (`hH`), and its resonance property
(`res`).  The nonvanishing field `hHne` is discharged automatically via
`canonicalGaugeAmplitude_ne_zero`. -/
````

### `four time frequency shift/RequestProject/HRT/ActiveFibreWindingZeroOnArc(1).lean`

Content ID `f8f2691622b49a72`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L64**

````text
/-!
# Active-fibre winding-zero on the connected active arc

This module performs the **active-fibre winding-zero on arc run**.  The residual
of the active-fibre holonomy data production run was isolated as the single
inter-derivable pair of theorem types

```
StandardActiveFibreHolonomyEqualsGaugeMultiplier   (algebraic form)
StandardActiveFibreWindingZeroOnArc                (winding / loop-holonomy form)
```

The *intended* mathematical argument for closing the winding form is:

1. for almost every active fibre the actual return equation holds
   (`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`);
2. the active fibre is nonzero in `L²`;
3. the measurable winding obstruction gives **zero winding** of the loop
   `x ↦ Bmult(x,s)` for almost every active parameter `s`
   (`measurable_cocycle_winding_eq_zero`);
4. the return multiplier is a jointly analytic, **zero-free** family of loops on
   the active arc, so its integer winding number is **locally constant** in `s`;
5. the active set has positive measure inside the connected arc `(a₀,b₀)`, so the
   winding number — a locally constant `ℤ`-valued function on a connected set —
   is constant, and being `0` on a positive-measure subset it is `0` everywhere.

This run **discharges, fully in Lean, the topological propagation steps (4→5)**:

* `locallyConstant_eq_of_mem_Ioo` — a function that is locally constant *within*
  the connected arc `Set.Ioo a₀ b₀` takes a single value on it (genuine
  Mathlib-backed proof via `IsLocallyConstant.apply_eq_of_isPreconnected` on the
  connected subtype `↥(Set.Ioo a₀ b₀)`);
* `exists_winding_zero_of_ae_on_positive_measure` — a function vanishing a.e. on a
  positive-measure set vanishes at *some* point of that set (measure-theoretic);
* `winding_zero_on_active_arc_of_ae_active_winding_zero` — combining the two:
  from an a.e.-zero winding number on a positive-measure active subset together
  with local constancy on the arc, the winding number is `0` **everywhere** on
  the arc;
* `StandardActiveFibreWindingZeroOnArc_proved` — the winding form of the residual,
  built from the reduced data.

The two genuinely analytic ingredients that remain are isolated as the *smallest*
exact theorem types (the run instructions' acceptable remaining types):

* `StandardWindingLocallyConstantZeroFreeFamily` — local constancy of the integer
  winding number of the zero-free analytic return-multiplier family on the arc;
* `StandardAEActiveFibreWindingZero` — a.e. zero winding of the actual return
  cocycle on a positive-measure active subset (from the measurable winding
  obstruction applied to the actual a.e. cocycle);
* `StandardWindingZeroHolonomyBridge` — the per-fibre identification that zero
  winding of the return loop forces the gauge value to equal the loop holonomy
  `exp(∫₀¹ ell_t)` of a periodic logarithm.

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/ActualL2ZakFiberExtraction(1).lean`

Content ID `2c77ca2cbaed8afd`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L421–L432**

````text
/-- **Task G — final Stage 6B contradiction with the corrected `L²`-level Zak
fibre extraction.**

The corrected replacement for
`critical_mixed_final_contradiction_with_actual_Zak_fiber_extraction`.  On the Zak
side it depends **only** on the corrected `L²`-level residual
`StandardActualL2ZakRepresentativeTheorem` — the fibre function is an honest
`L²`-level representative of the **target** Zak class `Z.Zak f`, and the
Plancherel mass tie is the isometric identity, with **no** compactly supported
representative of `f`.  The remaining hypotheses are the same non-Zak interfaces
as before (Denjoy–Koksma data, analytic-rigidity/periodic-gauge data, and the
local Laurent holonomy root data). -/
````

### `four time frequency shift/RequestProject/HRT/ActualL2ZakRepresentative(1).lean`

Content ID `66e8b42287d4e42e`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L73**

````text
/-!
# Stage 6B — the canonical **frequency-periodic** representative of the actual
`L²`-level Zak target class, and the minimal residual reduction

This module discharges the *generic measure-theoretic* content of the corrected
`L²`-level residual `StandardActualL2ZakRepresentativeTheorem`
(`RequestProject/HRT/ActualL2ZakFiberExtraction.lean`) and reduces that residual
to the single genuinely Zak-analytic obligation, the **a.e. one-step fibre
equation** for the canonical periodic representative.

## Why a periodic representative

The downstream `NontrivialAEFiberExtraction` consumes a fibre function
`F : ℝ → ℝ → ℂ` that is `1`-periodic in the frequency variable.  An arbitrary
`Lp` representative of the target class `concreteAEZakModel.Zak f : ZakTarget` is
only defined a.e. on the fundamental square `(0,1]²` and carries no periodicity.
We therefore build the **canonical periodic representative**
```
zakPeriodicRep G x s := (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s),
```
the periodic extension from the fundamental domain of the chosen `Lp`
representative of `G`.  By construction it is `1`-periodic in *both* variables
(in particular in the frequency variable `s`), and it agrees with `G` almost
everywhere on the fundamental square `(0,1]²` (where `Int.fract` is the identity
off a null set).

## What is proved here (unconditionally, no compact support of `f`)

* `actual_L2_Zak_periodic_representative` — the canonical periodic representative
  exists (its definition `zakPeriodicRep`);
* `actual_L2_Zak_periodic_representative_periodic_s` — `1`-periodicity in the
  frequency variable (Task B);
* `actual_L2_Zak_periodic_representative_ae_eq` — a.e. equality with the chosen
  `Lp` representative on the target measure (Task B);
* `actual_L2_Zak_periodic_representative_memLp` — `L²([0,1]²)` membership of the
  periodic representative (Task B);
* `Lp_eq_to_ae_eq_representatives`, `Lp_relation_to_ae_product_relation`
  — Lp-equality / Lp-relation to a.e. product equality (Task C);
* `ae_product_eq_to_ae_fibre_eq'`, `ae_fiberwise_of_ae_prod'` — product-a.e. to
  fibre-a.e. conversion (Task D).

## The minimal residual reduction (Task E / Task F)

The only content of `StandardActualL2ZakRepresentativeTheorem` *not* discharged
here is the **a.e. one-step fibre equation** for the canonical periodic
representative.  At the level of the abstract a.e. Zak model
`concreteAEZakModel` the lattice/rogue covariance operators are realized by
transport through the isometric extension `zakExt` and carry **no explicit fibre
formula**, so the explicit `oneStepEquation` cannot be read off the abstract
covariance.  This is the genuine remaining Zak-analytic obligation; it is
isolated — *not* as an axiom — as the precisely-typed proposition
`StandardActualZakRepresentativeEquationAE`, the a.e. one-step fibre equation for
`zakPeriodicRep (concreteAEZakModel.Zak f)`.

`standardActualL2ZakRepresentativeTheorem_of_equationAE` then proves the full
residual `StandardActualL2ZakRepresentativeTheorem` from that single blocker by
supplying the canonical periodic representative for the a.e.-representative and
periodicity fields.  The downstream endpoints
`actual_L2_zak_nontrivial_fiber_extraction_closed`,
`zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_closed` and
`critical_mixed_final_contradiction_without_Zak_side_interface` are rewired to
depend on the minimal blocker.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/
````

**L197–L209**

````text
/-- **The minimal remaining Zak-analytic blocker (Task F).**

The single content of `StandardActualL2ZakRepresentativeTheorem` not discharged
by the generic measure theory above: the **a.e. one-step fibre equation** for the
canonical periodic representative `zakPeriodicRep (concreteAEZakModel.Zak f)` of
the target class.

This is the genuine Zak covariance content: at the abstract level the model's
lattice/rogue covariance operators are realized by transport through the
isometric extension `zakExt` and carry no explicit fibre formula, so the explicit
`oneStepEquation` cannot be read off the abstract covariance.  It is isolated as a
precisely-typed proposition (referring to a **representative of the target class**,
with **no** compact-support / boundedness data on `f`), **not** an axiom. -/
````

### `four time frequency shift/RequestProject/HRT/ActualL2ZakTargetRelation(1).lean`

Content ID `c632cbffdeac0564`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L36**

````text
/-!
# Stage 6B — the **target `Lp` one-step Zak relation** (Task C)

This module performs the one genuinely *unconditional* step of the corrected
`L²`-level Zak residual: applying the concrete a.e. Zak isometry
`concreteAEZakModel.Zak` to the normalized four-term HRT relation in the source
`L²(ℝ)` space and using the **abstract covariance fields** of the model
(`lattice_cov` for the two integer-lattice shifts, `rogue_cov` for the rogue
shift `(a, p/m)`) to obtain an equality of target `L²([0,1]²)` classes:
```
c₀ • Zf + c₁ • charLattice r₁ t₁ (Zf) + c₂ • charLattice r₂ t₂ (Zf)
        + c₃ • charRogue a (p/m) (Zf) = 0 .
```

This is the honest "target-side" form of the relation.  It needs **no** explicit
fibre formula for the (abstractly transported) covariance operators — only the
linearity of the isometry and the two covariance fields — so it is proved
unconditionally here.

The remaining content of the minimal blocker
`StandardActualZakRepresentativeEquationAE` is exactly to turn the abstract
covariance operators `charLattice` / `charRogue` appearing here into their
explicit pointwise fibre representatives; that is isolated separately (it is the
genuinely Zak-analytic core, blocked by the abstract transport construction of
the model's covariance operators).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/
````

**L72–L93**

````text
/-- **Canonical remaining Zak-analytic interface (Task G shape
`StandardTargetRelationToRepresentativeEquationAE`).**

The content of the minimal blocker `StandardActualZakRepresentativeEquationAE`
with its source-side hypothesis replaced by the (now unconditionally proved)
*target* `Lp` one-step relation.  Concretely: from a nonzero window `f` whose
target class `Zf := concreteAEZakModel.Zak f` satisfies the explicit target
four-term relation
```
c₀ • Zf + c₁ • charLattice r₁ t₁ Zf + c₂ • charLattice r₂ t₂ Zf
        + c₃ • charRogue a (p/m) Zf = 0 ,
```
the canonical periodic representative `zakPeriodicRep Zf` satisfies the a.e.
one-step fibre equation.

This isolates *exactly* the remaining Zak-analytic content: turning the
abstractly transported covariance operators `charLattice` / `charRogue` (applied
to the target class) into their explicit pointwise fibre representatives on
`zakPeriodicRep Zf`.  It mentions **no** source-side time-frequency shift
operators — it is tied directly to the target representative — and is therefore a
strictly more canonical form of the blocker than
`StandardActualZakRepresentativeEquationAE`. -/
````

### `four time frequency shift/RequestProject/HRT/ActualZakFiberExtraction(1).lean`

Content ID `5b962ad6aebdc282`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L181–L208**

````text
/-- **Task H — the minimal actual-Zak residual.**

**DEPRECATED — `TOO_STRONG_FOR_GENERAL_L2`.**  This residual demands, for an
*arbitrary* `L²` class `f`, a window `g : ℝ → ℂ` that is bounded, measurable,
compactly supported in `[0,N)` **and** satisfies `f =ᵐ g`.  Such a representative
exists only for the dense subclass of bounded compactly supported functions, not
for a general `L²` equivalence class, so this proposition is too strong to be the
correct Zak-side blocker.  It is **superseded** by the corrected `L²`-level
residual `StandardActualL2ZakRepresentativeTheorem`
(`RequestProject/HRT/ActualL2ZakFiberExtraction.lean`), which selects a
representative of the **target** class `Z.Zak f` (which always exists) instead of
a compactly supported representative of `f`.  This definition and its downstream
lemmas are retained only for documentation/back-compat; new Stage 6B endpoints
route through the corrected `L²`-level residual.

The single genuinely Zak-analytic obligation remaining after re-anchoring: from a
nonzero `L²` class `f` satisfying the normalized four-term HRT relation in the
concrete a.e. Zak model, produce

* a concrete window `g` (bounded, measurable, supported in `[0,N)`) representing
  `f` (`f =ᵐ g`), and
* the a.e. one-step Zak fibre equation **for the actual transform**
  `concreteZakDense g`.

This is exactly the actual-Zak content (existence of a genuine window
representative carrying the `L²`-class relation as an a.e. fibre equation of the
*actual* Zak transform).  It is recorded as a precisely-typed proposition, **not**
an axiom, and **not** the model-free `StandardNontrivialFiberConstructionTheorem`. -/
````

**L333–L346**

````text
/-- **Task F — final Stage 6B contradiction with the actual Zak fibre extraction.**

The re-anchored replacement for
`critical_mixed_final_contradiction_without_Zak_extraction_interface`.  On the Zak
side it depends **only** on the actual-Zak residual
`StandardActualZakRepresentativeTheorem` — the fibre function is the genuine Zak
transform `concreteZakDense g` of the actual window, and the Plancherel mass tie
is the actual Zak/Plancherel identity.  It does **not** depend on the model-free
`StandardNontrivialFiberConstructionTheorem`.

The remaining hypotheses are the same non-Zak interfaces as the previous bridges:
the corrected periodic Denjoy–Koksma data (`DK`, `hq`), the analytic-rigidity /
periodic-gauge data (`H`, `J`, …), and the local Laurent holonomy root data
(`ad`, `coeffs`, `hroots`, `hJholo`). -/
````

### `four time frequency shift/RequestProject/HRT/AffineSymplecticZakReduction(1).lean`

Content ID `840fdc31108c9e19`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L77**

````text
/-!
# Certifying the affine-symplectic / metaplectic + Zak-covariance reduction

This module certifies the **reduction** that produces the Stage-6A
return-cocycle witness `CriticalMixedReturnWitness` from a physical four-term
Gabor relation in the critical mixed orbit.  The reduction has two conceptual
halves:

* the **affine-symplectic / metaplectic covariance** half — a unitary change of
  time-frequency coordinates (`SL(2,ℝ)` metaplectic operator composed with an
  affine shift) transporting the physical relation
  `∑ⱼ cⱼ · π(orbitPts j) f = 0` over `L²(ℝ)` into the *normalized* relation
  `d₀ g + d₁ π(λ₁) g + d₂ π(λ₂) g + d₃ π(a, p/m) g = 0`
  inside an abstract `L²`-model `V` equipped with an `L2ZakModel`, where
  `(r₁,t₁),(r₂,t₂)` is a unimodular `ℤ²`-basis and `θ = m·a` is irrational;

* the **Zak-covariance** half — applying the Zak transform to the normalized
  relation produces the one-step Zak fibre equation, hence a
  `NormalizedReturnData`, and (together with the remaining certificate data)
  the full `CriticalMixedReturnWitness`.

## What is genuinely certified here (no `sorry`, no `axiom`)

* `tfShift_add`, `tfShift_smul`, `tfShift_zero_fun`, `tfShift_cocycle`,
  `tfShift_memLp` — the **affine** time-frequency covariance algebra of the
  physical shift `tfShift` (additivity, homogeneity, the affine cocycle
  composition law with its explicit phase, and `L²`-stability).  This is the
  certified affine part of the affine-symplectic covariance.

* `CriticalMixedZakTransport` — the **explicit output bundle** of the
  metaplectic + Zak-covariance reduction: an `L2ZakModel` on an abstract `L²`
  model `V`, the transported element `g`, the normalized arithmetic data, the
  normalized `Z.shift` relation, and the remaining certificate data.  It is a
  *transparent refinement* of `CriticalMixedReturnWitness`: instead of an opaque
  `NormalizedReturnData` it carries the genuine Zak model and normalized
  relation from which the return cocycle is **derived** through the certified
  Zak covariance.

* `returnData_of_zakTransport` — the certified Zak-covariance step: from a
  `CriticalMixedZakTransport` it constructs the `NormalizedReturnData`
  (the *return-cocycle witness* proper) via
  `hrt_relation_to_one_step_zak_equation`.

* `witness_of_zakTransport` — assembles the full `CriticalMixedReturnWitness`
  from a `CriticalMixedZakTransport` (return cocycle + certificate data).

* `AffineSymplecticMetaplecticReduction` — the named interface isolating the
  genuinely deep, Mathlib-absent input: that *every* all-nonzero a.e.-vanishing
  physical relation admits such a normalized Zak transport bundle.  This is the
  exact metaplectic-covariance content.

* `standardGabor_of_affineSymplecticMetaplecticReduction` — the headline
  certification: the affine-symplectic / metaplectic + Zak-covariance reduction
  produces the `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`) input consumed by the
  geometric-assembly layer.  Everything downstream of the transport bundle (Zak
  covariance → return cocycle → witness → contradiction) is fully certified.

## Honest scope

The single remaining gap is the *construction* of the transport bundle from a
physical relation, i.e. inhabiting `AffineSymplecticMetaplecticReduction`.  That
requires (a) the metaplectic representation of `SL(2,ℝ)` with its intertwining
covariance `μ_S π(z) μ_S⁻¹ = (phase) π(Sz)`, and (b) a concrete `L2ZakModel` on
`L²(ℝ)` — both genuinely absent from Mathlib `v4.28.0`.  They are isolated here
as the explicit named interface; the reduction *logic* itself is certified with
no `sorry`.
-/
````

**L131–L139**

````text
/-- **The explicit output bundle of the metaplectic + Zak-covariance reduction.**

This is a transparent refinement of `CriticalMixedReturnWitness`: it carries the
genuine `L2ZakModel` on an abstract `L²`-model `V`, the transported element `g`,
the normalized arithmetic data (`m,p,a`, unimodular `ℤ²`-basis, irrational
`θ = m·a`, the four nonzero normalized coefficients), the **normalized
`Z.shift` relation**, and the remaining certificate data over a common active
window `(a₀,b₀)`.  The return cocycle is *derived* from these by the certified
Zak covariance (`returnData_of_zakTransport`), rather than postulated. -/
````

**L171–L171**

````text
-- remaining certificate data over a common active window `(a₀, b₀)`
````

### `four time frequency shift/RequestProject/HRT/CanonicalAmplitudeHolonomyCompat(1).lean`

Content ID `43f3c2f9f8d868ef`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L87**

````text
/-!
# Canonical amplitude / holonomy compatibility run

This module performs the **canonical amplitude / holonomy compatibility run** for
the conditional final assembly theorem.  It addresses the single residual
analytic↔algebraic bridge

```
  H t = canonicalGaugeAmplitude θ coeffs ad t      (on the active arc),
```

equivalently

```
  gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t      (on the active arc),
```

which the previous *canonical holonomy amplitude run*
(`CanonicalHolonomyAmplitude.lean`) isolated as the field `hHcanon` of
`CriticalMixedCanonicalAmplitudeInterface`, and which the *holonomy-identification
discharge run* (`HolonomyIdentificationDischarge.lean`) isolated as the field
`hJalg` of `CriticalMixedHolonomyIdentificationInterface`.

## Task A — the exact residual

The exact remaining hypothesis is the pointwise identity, on the active arc, of
the analytic gauge value `gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` with
the choice-free algebraic loop holonomy `algReturnHolonomy coeffs ad t`.  Three
mutually equivalent shapes are used in the project:

* `StandardGaugeMultiplierEqualsAlgHolonomy` —
  `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`;
* `StandardCanonicalAmplitudeCompatibility` —
  `H t = canonicalGaugeAmplitude θ coeffs ad t`;
* the `hJholo`/`hJgauge` form carried by `CriticalMixedWindingInterface`.

The classification of each ingredient is recorded in
`CANONICAL_AMPLITUDE_HOLONOMY_STATUS.md`.

## Task C — the algebraic holonomy identification (already proved)

The step "the periodic-log integral of the return multiplier equals the
root-product algebraic holonomy",
`StandardPeriodicLogIntegralEqualsRootHolonomy`, is **already discharged**
unconditionally as `return_multiplier_holonomy_eq_integral_log`
(`HolonomyIdentificationDischarge.lean`).  It is re-exported here and is *not* a
blocker.

## Tasks B/D — the compatibility follows from the active-fibre return cocycle

The key result of this run, `canonical_amplitude_compatibility_of_winding`, shows
that the residual compatibility is **not** independent data: given the active-fibre
winding interface `CriticalMixedWindingInterface` (the holonomy / phase-lift data
`J`, `hJgauge`, `hJholo`) together with the minimal root data, the canonical
amplitude compatibility `H t = canonicalGaugeAmplitude θ coeffs ad t` is *derived*
on the active arc.  The proof:

1. synthesises a continuous `1`-periodic logarithm `ell` of the return loop from
   the root factorisation (`evalBiLaurentPoly_periodic_log_of_roots`);
2. evaluates `hJholo` at `ell` to identify `J t` with `exp(∫₀¹ ell)`;
3. rewrites `J t = gaugeReturnMultiplier H θ t` via `hJgauge`;
4. identifies `exp(∫₀¹ ell)` with `algReturnHolonomy coeffs ad t` via the
   already-proved `return_multiplier_holonomy_eq_integral_log`;
5. converts the gauge identity to the canonical-amplitude form.

## Tasks E/F — the smallest exact blocker and the downstream contradiction

The minimal active-arc compatibility interface
`StandardCanonicalAmplitudeCompatibility` is strictly smaller than the previous
whole-window `CriticalMixedCanonicalAmplitudeInterface` (it is quantified only
over active fibres).  From it, together with the already-discharged analytic
constancy of `H`, we construct the holonomy-constancy interface internally and
restate the conditional final contradiction
(`critical_mixed_final_contradiction_with_canonical_amplitude_compat`).

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/CanonicalHolonomyAmplitude(1).lean`

Content ID `e60067c45109bf91`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L84**

````text
/-!
# Canonical holonomy amplitude run

This module performs the **canonical holonomy amplitude run** for the conditional
final assembly theorem.  Its purpose is to eliminate or minimize the residual
holonomy-constancy interface `CriticalMixedHolonomyConstancyInterface`
(`HolonomyLawBridge.lean`), whose single field is

```
  hAlgPhase : algReturnHolonomy coeffs ad t = H s₀ * exp(-2π i θ t).
```

## Task A — where the abstract amplitude `H` is used

The amplitude `H` enters through the active/analytic Zak-model interface
`CriticalMixedActiveAnalyticInterface` (`ConditionalFinalAssembly.lean`): it is an
analytic, nonvanishing function on the window `(a₀, b₀)` whose values lie in the
resonance group on a positive-measure active set.  The previous run
(`HolonomyLawBridge.lean`) proved its **constancy** on the active window
(`active_analytic_holonomy_constant`).  The only residual content of the
holonomy law is the algebraic-phase identity `hAlgPhase`, which references `H`
only through its single constant value `H s₀`.

The detailed field classification is recorded in
`CANONICAL_HOLONOMY_AMPLITUDE_STATUS.md`.

## Task B — the canonical amplitude

We define the **canonical gauge holonomy amplitude** directly from the algebraic
return holonomy,

```
  canonicalGaugeAmplitude θ coeffs ad t = exp(2π i θ t) · algReturnHolonomy coeffs ad t,
```

so that the existing gauge operation `gaugeReturnMultiplier` recovers the
algebraic return holonomy *definitionally*:

```
  gaugeReturnMultiplier (canonicalGaugeAmplitude θ coeffs ad) θ t
    = algReturnHolonomy coeffs ad t.
```

This is `gaugeReturnMultiplier_canonicalGaugeAmplitude`
(alias `canonicalGaugeAmplitude_gauge_identity`).

## Tasks C/D/F — the transparent compatibility field and the constancy interface

The genuine analytic↔algebraic bridge — that the *abstract* Zak-model amplitude
`H` equals the *canonical* algebraic amplitude — is not derivable from the
available interface data (it is exactly the link between the abstract Zak-model
amplitude and the concrete algebraic return loop, which the previous runs already
identified as the genuine remaining obstacle).  Per the Task F fallback policy we
therefore replace the opaque algebraic-phase identity `hAlgPhase` by the strictly
smaller and fully **transparent** compatibility field

```
  H t = canonicalGaugeAmplitude θ coeffs ad t      (on the active window),
```

packaged as `CriticalMixedCanonicalAmplitudeInterface`.

From this transparent compatibility field, together with the *already proved*
analytic constancy of `H` (`active_analytic_holonomy_constant`), we **construct**
the holonomy-constancy interface internally
(`canonical_amplitude_satisfies_holonomy_constancy_interface`), so that
`hAlgPhase` becomes a direct consequence of the gauge identity
`gaugeReturnMultiplier_canonicalGaugeAmplitude` and the constancy theorem.  The
headline endpoint
`critical_mixed_final_contradiction_with_canonical_amplitude_interface` then
restates the conditional final contradiction using only the transparent
compatibility field in place of the opaque `hAlgPhase`.

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/CanonicalOperatorFormulas(1).lean`

Content ID `b263b2b9b7e972d3`; 2 byte-identical path(s); full file source review; see R49; not build-verified.

**L10–L30**

````text
/-!
# Stage 6B — the target-operator fibre formulas, **proved** for the canonical model

Now that `concreteAEZakModel` is the *canonical* a.e.-level Zak model
`canonicalAEZakModel` (whose covariance operators are the explicitly defined
`explicitCharLattice` / `explicitCharRogue`), the two previously-isolated
target-operator fibre formula blockers

```
StandardTargetLatticeOperatorRepresentativeAE
StandardTargetRogueOperatorRepresentativeAE
```

are **provable**, because the explicit operators expose their fibre action by
construction (`explicitCharLattice_coeFn`, `explicitCharRogue_coeFn`).  This file
proves them and feeds them into the quasiperiodic Zak-side discharge machinery
(`QuasiperiodicZakSideDischarge.lean`), so the entire Zak side is discharged
**unconditionally** (no remaining Zak-side hypotheses).

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/
````

### `four time frequency shift/RequestProject/HRT/ConcreteAEZakContradiction(1).lean`

Content ID `6f20dba67a0d71ad`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L26**

````text
/-!
# Stage 6B — the concrete a.e. Zak model is now unconditional (TASK G)

With `concrete_L2ZakModelAE_closed` (proved in `ConcreteZakDenseDataFull.lean`)
the honest a.e.-level Zak model `L2ZakModelAE (Lp ℂ 2 volume) ZakTarget` exists
*unconditionally* (no `StandardConcreteZakToLpTheorem` hypothesis, no `sorry`,
no axiom).  Consequently the Stage 6B final contradiction
(`critical_mixed_final_contradiction_without_pointwise_Zak_interface`) no longer
needs a Zak model supplied as a hypothesis: it can be instantiated at the
canonical model `concreteAEZakModel`.

The resulting theorem
`critical_mixed_final_contradiction_with_Zak_only_fiber_extraction` therefore
retains, on the Zak side, **only** the active-fibre extraction obligation
`StandardAEFiberExtractionTheorem` — exactly the single remaining Zak blocker.
-/
````

**L42–L50**

````text
/-- **TASK G — Stage 6B final contradiction, with the concrete a.e. Zak model
built in.**

This is `critical_mixed_final_contradiction_without_pointwise_Zak_interface`
instantiated at the canonical concrete model `concreteAEZakModel`.  It removes the
Zak-model hypothesis entirely (the model is now constructed unconditionally) and
retains, on the Zak side, only the active-fibre extraction obligation
`StandardAEFiberExtractionTheorem`.  The remaining hypotheses (`DK`, `hroots`,
`hJholo`, …) are the same non-Zak interfaces as before. -/
````

### `four time frequency shift/RequestProject/HRT/ConcreteZakStage6B(1).lean`

Content ID `b3512a84072973fa`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L33**

````text
/-!
# Stage 6B — concrete `L²(ℝ)` specialization of the Zak no-flat-band bridge

This module specializes the abstract Stage 6B bridge
`zak_relation_feeds_normalized_no_flat_band` (over an arbitrary inner-product
space `V`) to the concrete Hilbert space `L²(ℝ) = Lp ℂ 2 volume`.

The point of the specialization: every *algebraic / analytic* field of the Zak
interface (`Zak_periodic_s`, `lattice_cov`, `rogue_cov`, the Plancherel identity,
the fibre-density regularity and active-set positivity) has been discharged
concretely and unconditionally in the `RequestProject.Zak.*` modules
(`concreteZakDense_*`, `finiteSupportZak_plancherel`, `concreteZakDense_plancherel`,
`concrete_fiberDensity_integrable`, `concrete_active_set_positive_measure`).  The
*only* remaining Zak-side obligation is to produce the `L2ZakModel` term itself on
`L²(ℝ)`, i.e. `StandardL2ZakModelTheorem` (the standard Hilbert-space completion
of the densely-defined Zak transform).  The theorem below makes this precise:
given such a model `Z` for `L²(ℝ)` (equivalently, given
`StandardL2ZakModelTheorem`), the four-term HRT relation feeds the no-flat-band
contradiction.

It still depends on the *other* open interfaces (`ROOT_DATA_INTERFACE`, the
corrected periodic Denjoy–Koksma interface, canonical-amplitude compatibility),
exactly as the abstract bridge does.
-/
````

### `four time frequency shift/RequestProject/HRT/ConditionalDossierCertification(1).lean`

Content ID `05cab055dd054987`; 2 byte-identical path(s); full file source review; see R50; not build-verified.

**L7–L94**

````text
/-!
# Conditional certification of the dossier (interface-conditional theorem)

This module certifies the dossier **exactly as an interface-conditional theorem**.

The unconditional theorem `critical_mixed_orbit_HRT_L2`
(`RequestProject.MainStatement`) is *not* fully Lean-certified: its body is the
sole remaining theorem-body `sorry` of the project, standing for the deep
classical inputs that are genuinely absent from Mathlib `v4.28.0`.

What *is* certified here, with **no `sorry`, no `axiom`, no `unsafe`,
no `@[implemented_by]`**, is the theorem

```
critical_mixed_orbit_HRT_L2_certified_from_standard_inputs
```

which proves the **exact same conclusion** `c = 0`, under the **exact same
hypotheses** as `critical_mixed_orbit_HRT_L2`, taking as **explicit, transparent
hypotheses** precisely the remaining named external standard inputs of the
dossier.  Nothing is hidden in an opaque structure: every standard input is a
visible argument of the theorem.

## The six remaining standard inputs

The remaining gap is *exactly* the following named external inputs (none of which
is proved internally, none of which is hidden as an axiom, all of which are used
transparently as hypotheses):

1. `StandardInsideCountLocallyConstant` — **Rouché / root-count stability**.
   The inside-the-unit-disk root count of the fibre polynomial family is locally
   constant on a zero-free active arc.  (Here passed in its honest *true* form:
   no roots on the unit circle on the arc ⟹ the inside count is locally
   constant.)

2. `StandardCenteredOrbitGridProperty` — the **centered three-distance theorem**.
   For convergent-denominator return times the centered orbit grid property
   holds.  (This is the corrected centered-grid residual; see `TASK A` in the
   status files.  It replaces the previously mis-named, mathematically *false*
   targets `ContinuedFractionReturnData.orbit_partition` and
   `star_discrepancy_le_one`.)

3. `StandardCanonicalAmplitudeResonanceProperty` — **canonical amplitude
   resonance**: the canonical loop-holonomy amplitude lands in the resonance
   group of the return times on a positive-measure active set.

4. `StandardThreePointHRTTheorem` — the **three-point HRT theorem** (any three
   distinct time-frequency translates of a nonzero `L²` function are linearly
   independent).

5. `StandardAffineSymplecticReductionForHRT` — the **affine-symplectic /
   metaplectic covariance** reduction (definitionally equal to input 6).

6. `StandardGaborRelationToNormalizedCriticalMixedRelation` — the
   **Gabor-relation → normalized critical-mixed-relation** transport, which
   produces, from an all-nonzero four-term Gabor relation, the
   Zak/return-cocycle witness `CriticalMixedReturnWitness`.

Inputs 5 and 6 are the *same* project declaration
(`StandardAffineSymplecticReductionForHRT` is an `abbrev` for
`StandardGaborRelationToNormalizedCriticalMixedRelation`); it is the single deep
covariance/Zak-reduction residual `hAffine`.

## Load-bearing vs. transparency note

In the project's *current* assembled pipeline the covariance input `hAffine`
already produces a complete `CriticalMixedReturnWitness` whose fields **are** the
three analytic residuals (1)–(3): its `hroots_min` field is the root-count datum
behind `StandardInsideCountLocallyConstant`, its return data `dk` is the
Denjoy–Koksma datum behind `StandardCenteredOrbitGridProperty`, and its `hSres`
field is the resonance datum behind `StandardCanonicalAmplitudeResonanceProperty`.
Consequently the headline assembly below is discharged through the two
genuinely-sufficient inputs `h3` (three-point HRT) and `hAffine`
(affine-symplectic covariance) via the already-proved pipeline endpoint
`critical_mixed_orbit_HRT_L2_conditional_on_covariance` (which itself routes
through the final geometric assembly adapter, the canonical Zak model, the
root-data reduction, the centered Denjoy–Koksma wiring, the canonical
loop-holonomy amplitude, and the no-flat-band contradiction
`normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`).

The three granular analytic residuals (1)–(3) are nevertheless listed as
explicit, transparent hypotheses of the certified theorem, in their honest
satisfiable forms, so that the remaining gap is *exactly* the named list above
and the certification is faithful to the dossier.  In this particular assembly
they are subsumed by `hAffine`'s witness and are therefore not separately
consumed; per the dossier they are documented here and in
`CONDITIONAL_DOSSIER_CERTIFICATION_STATUS.md`.
-/
````

**L101–L124**

````text
/-- **Conditional dossier certification.**

The exact conclusion `c = 0` of `critical_mixed_orbit_HRT_L2`, proved under the
exact same hypotheses, from precisely the remaining named external standard
inputs of the dossier:

* `hInsideCount` — `StandardInsideCountLocallyConstant` (Rouché / root-count
  stability), in its honest true form;
* `hCenteredGrid` — `StandardCenteredOrbitGridProperty` (centered three-distance
  theorem for convergent denominators);
* `hResonance` — `StandardCanonicalAmplitudeResonanceProperty` (canonical
  amplitude resonance on a positive-measure active set);
* `h3` — `StandardThreePointHRTTheorem` (three-point HRT theorem);
* `hAffine` — `StandardAffineSymplecticReductionForHRT`
  (= `StandardGaborRelationToNormalizedCriticalMixedRelation`, the
  affine-symplectic / metaplectic covariance reduction).

The proof calls the already-proved conditional pipeline
`critical_mixed_orbit_HRT_L2_conditional_on_covariance`, which is genuinely
sufficient from `h3` and `hAffine`.  As documented in the module header,
`hAffine`'s witness already bundles the three analytic residuals
`hInsideCount`, `hCenteredGrid`, `hResonance`; these are listed here as explicit
transparent hypotheses so that the remaining gap is *exactly* the named list, and
they turn out to be unnecessary as *separate* arguments in this assembly. -/
````

### `four time frequency shift/RequestProject/HRT/ConditionalFinalAssembly(1).lean`

Content ID `a2922c578b193fc5`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L59**

````text
/-!
# Conditional final assembly of the critical mixed-arithmetic four-point HRT theorem

This module performs the **conditional final assembly run**: it composes the
strongest available bridge theorems of the project into a single conditional
contradiction theorem, parameterised exactly by the four remaining explicit
interface classes recorded in `FINAL_INTERFACE_AUDIT.md`:

```
  ROOT_DATA_INTERFACE     : hroots_min
  ZAK_MODEL_INTERFACE     : the L2ZakModel `Z` and the active/analytic data
  DK_VARIATION_INTERFACE  : the Denjoy–Koksma return data (deep DK estimate)
  WINDING_INTERFACE       : the holonomy / phase-lift data `hJgauge`, `hJholo`
```

It does **not** touch `critical_mixed_orbit_HRT_L2` (whose proof remains the only
theorem-body `sorry` in the project) and introduces no axioms, `sorry`s, or
`admit`s.

## What is established here

* `zak_relation_feeds_normalized_no_flat_band_root_data_minimal` — the adapter
  that upgrades the Stage 6B endpoint
  `zak_relation_feeds_normalized_no_flat_band` (which fed the *older* Stage 6A
  bridge `normalized_return_cocycle_feeds_no_flat_band_synthesized`, consuming
  the full root-factorisation data `hroots`) to the Run A **root-data-minimal**
  Stage 6A bridge `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`
  (consuming only the minimal geometric interface `hroots_min`).  This combines
  the Stage 6B Zak relation-to-cocycle construction
  (`hrt_relation_to_one_step_zak_equation`) with the Run A root-data-minimal
  bridge.

* `NormalizedCriticalMixedRelationData` — a clean structure bundling a
  normalized nontrivial four-term HRT relation in an `L²` Zak model.  Per Task D,
  we do **not** attempt the affine-symplectic normal form from arbitrary
  `u, v, ν` to the normalized relation; the conditional contradiction is proved
  from this normalized data.

* Interface structures
  `CriticalMixedDKInterface`, `CriticalMixedRootDataInterface`,
  `CriticalMixedActiveAnalyticInterface`, `CriticalMixedWindingInterface`
  packaging the four remaining interface classes as **explicit assumptions**
  (no axioms, no global constants).

* `normalized_critical_mixed_relation_contradiction_with_interfaces` and
  `critical_mixed_final_contradiction_with_interfaces` — the conditional final
  assembly theorems: from the normalized relation data together with the four
  interface packages, derive `False`.
-/
````

**L178–L178**

````text
/-! ## Task B — the four remaining interface packages -/
````

**L238–L262**

````text
/-- **Conditional final contradiction from normalized relation data.**

Starting from a normalized nontrivial four-term HRT relation
(`NormalizedCriticalMixedRelationData`) in an `L²` Zak model `Z`, together with
the four remaining explicit interface packages

* `dk`       — the Denjoy–Koksma return data (`DK_VARIATION_INTERFACE`),
* `rootData` — the minimal root data `hroots_min` (`ROOT_DATA_INTERFACE`),
* `analytic` — the active-fibre / analytic-rigidity data (`ZAK_MODEL_INTERFACE`),
* `wind`     — the holonomy / phase-lift data (`WINDING_INTERFACE`),

the full bridge chain
```
  normalized relation
  -> Zak/polyphase fibre equation       (hrt_relation_to_one_step_zak_equation)
  -> NormalizedReturnData
  -> m-step return cocycle / Laurent return multiplier
  -> finite exceptional set / active arc
  -> root-data-minimal no-flat-band bridge
  -> local Laurent certificate
  -> irrational-character obstruction
  -> False
```
yields a contradiction.  This is the strongest conditional assembly statement of
the project; only the four interface packages above remain to be discharged. -/
````

**L281–L292**

````text
/-- **Conditional final assembly theorem.**

This is the headline conditional endpoint of the run.  It restates
`normalized_critical_mixed_relation_contradiction_with_interfaces`: from a
normalized critical mixed four-term relation and the four remaining explicit
interface packages (`DK_VARIATION_INTERFACE`, `ROOT_DATA_INTERFACE`,
`ZAK_MODEL_INTERFACE`, `WINDING_INTERFACE`), the project derives `False`.

What remains toward the unconditional `critical_mixed_orbit_HRT_L2` is no longer
wiring: it is exactly the discharge of these four interfaces (plus the
arbitrary-to-normalized affine-symplectic normal form, deliberately not attempted
here per Task D). -/
````

### `four time frequency shift/RequestProject/HRT/DenjoyKoksmaValidEndpoints(1).lean`

Content ID `70b59fc878386697`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L91–L101**

````text
/-- **Conditional final contradiction with a valid (periodic) Denjoy–Koksma
interface.**

This is the corrected analogue of
`critical_mixed_final_contradiction_with_interfaces`: it consumes the *faithful,
satisfiable* periodic real Denjoy–Koksma data `RealDenjoyKoksmaPeriodic D.θ`
directly (via `CriticalMixedDKInterface.ofPeriodicDK`), rather than the
final-assembly DK bundle that could in principle be sourced from the false
`RealDenjoyKoksma D.θ` object.  From the normalized relation data and the four
remaining interface packages — with the DK side supplied by the valid periodic
interface — the project derives `False`. -/
````

### `four time frequency shift/RequestProject/HRT/FinalGeometricAssembly(1).lean`

Content ID `c5d5684ceaa43ace`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L58**

````text
/-!
# Final geometric-assembly layer of the critical mixed-arithmetic four-point HRT theorem

This module isolates and (where possible) discharges the **four final
geometric-assembly blockers** of the certification, stated faithfully against the
*actual* data of the main theorem `critical_mixed_orbit_HRT_L2`
(`RequestProject.MainStatement`): the time-frequency shift `tfShift`, the four
orbit points `0, u, v, ν`, an `L²` function `f`, and a coefficient vector
`c : Fin 4 → ℂ`.

The four blockers named in the task are:

* `StandardCriticalMixedNormalForm` — the SL(2,ℤ)/metaplectic *normal-form
  contradiction*: a four-term relation with **all nonzero** coefficients in the
  critical mixed orbit is impossible;
* `StandardFourTermRelationToNormalizedRelation` — *transport* of the explicit
  four-term Gabor relation to the normalized Zak/return-cocycle data;
* `StandardThreePointNonzeroCoefficients` — from the **three-point HRT theorem**,
  all four coefficients of a nontrivial four-term relation are nonzero;
* `StandardNormalizedContradictionImpliesLinearIndependence` — the logical glue
  turning the normal-form contradiction into linear independence (`c = 0`).

## What is proved here (no `sorry`, no `axiom`)

* **Task D** — `StandardThreePointNonzeroCoefficients_proved`: a *genuine*
  reduction of the nonzero-coefficient property to the exact imported three-point
  HRT type `StandardThreePointHRTTheorem`.

* **Task E** — `StandardNormalizedContradictionImpliesLinearIndependence_proved`:
  a *genuine* proof of linear independence from the normal-form contradiction
  plus the three-point HRT input (pure logic: contrapose + Task D).

* **Task B/C** — `StandardCriticalMixedNormalForm_proved` and
  `StandardFourTermRelationToNormalizedRelation_proved`: *genuine* reductions of
  the normal-form contradiction to the exact (deep, metaplectic-covariance) input
  type `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`), realised by feeding the
  Zak/return-cocycle witness into the already-proved project endpoint
  `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`.

* **Task F** — `critical_mixed_orbit_HRT_L2_conditional_on_classical_inputs`:
  the headline conditional theorem.  It proves the *exact conclusion* `c = 0` of
  `critical_mixed_orbit_HRT_L2` from precisely two clearly-named classical
  inputs — the three-point HRT theorem and the geometric normal-form
  contradiction — and nothing else.  No assumption is hidden, no statement is
  weakened, and `critical_mixed_orbit_HRT_L2` itself is untouched.

The only remaining content (the two named hypotheses
`StandardThreePointHRTTheorem` and either `StandardCriticalMixedNormalForm` or,
upstream of it, `StandardGaborRelationToNormalizedCriticalMixedRelation`)
corresponds to the deep external inputs (three-point HRT and the
metaplectic/affine-symplectic covariance producing the Zak witness), which are
genuinely absent from Mathlib `v4.28.0`.
-/
````

**L90–L96**

````text
/-! ## Task D — three-point HRT ⇒ all coefficients nonzero

`StandardThreePointHRTTheorem` is the **exact imported three-point HRT type**:
any nontrivial linear combination of three *distinct* time-frequency translates
of a nonzero `L²` function does not vanish a.e.  We phrase it equivalently over a
four-point injective family with one coefficient set to zero (the remaining three
points are automatically distinct). -/
````

**L149–L159**

````text
/-! ## Tasks B/C — the normal-form contradiction from the Zak/return witness

The deep geometric input — SL(2,ℤ)/metaplectic affine-symplectic covariance plus
the Zak/polyphase reduction — produces, from an all-nonzero four-term relation in
the *physical* `L²` model, a `NormalizedReturnData` together with the four
remaining certificate interfaces.  We bundle that output as a single (universe-
and instance-free) witness, and feed it into the already-proved project endpoint
`normalized_return_cocycle_feeds_no_flat_band_root_data_minimal` to derive the
contradiction.  Constructing the witness from the relation is exactly the
remaining deep covariance content, isolated as the explicit hypothesis
`StandardGaborRelationToNormalizedCriticalMixedRelation`. -/
````

**L161–L167**

````text
/-- **The Zak/return-cocycle witness.**  A bundle of a normalized return-cocycle
datum `nrd` and the four remaining certificate interfaces (Denjoy–Koksma return
data, the analytic/active holonomy amplitude data, the holonomy/phase-lift gauge
data, and the minimal root data) over a common active window `(a₀, b₀)`.  It is
the precise output type of the metaplectic-covariance/Zak reduction.  Every field
is genuine certificate data — `witness_gives_false` shows the project already
derives a contradiction from it. -/
````

### `four time frequency shift/RequestProject/HRT/FinalInterfaceDischarge(1).lean`

Content ID `a3a0c50d904b3c99`; 2 byte-identical path(s); full file source review; see R47; not build-verified.

**L4–L36**

````text
/-!
# Final-interface consolidation (Phase 5)

This module collects, in a single place, the **exact** remaining analytic
interfaces of the critical mixed-arithmetic four-point HRT certification, each
stated as a precisely-typed proposition.  None of these is committed as a
`sorry`/`axiom`; they are the smallest honest residual theorem-types behind the
three deep blockers identified in this run.

Each of these reduces to a named classical theorem that is **not** currently in
Mathlib for this toolchain:

* `StandardRoucheRootCountStability` — Rouché / argument principle: a continuous
  family of complex polynomials with no roots on the unit circle has a locally
  constant inside-the-disk root count.  (This is exactly the canonical datum
  `StandardInsideCountLocallyConstant`.)

* `StandardConvergentDenominatorStarDiscrepancy` — the three-distance /
  best-approximation discrepancy bound: for a continued-fraction convergent
  denominator the orbit star-discrepancy is `≤ 1`.  (This is exactly the field
  `StandardRealDenjoyKoksmaCombinatorics.star_discrepancy_le_one`.  NOTE: the
  *stronger* grid-balanced `ContinuedFractionReturnData.orbit_partition` field is
  mathematically **false** — see the audit file
  `FINAL_FULL_CERTIFICATION_STATUS.md` — so the DK closure must go through the
  discrepancy bound, not through grid-balancedness.)

* `StandardCanonicalAmplitudeResonantOnActiveSet` — measurable-winding holonomy
  quantization: the canonical loop-holonomy amplitude lands in the resonance
  group of the return times on a positive-measure active set.  (This is exactly
  `StandardCanonicalAmplitudeResonanceProperty`.)

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` appear in this file.
-/
````

**L44–L50**

````text
/-- **Exact remaining Rouché root-count interface.**

Definitionally equal to the canonical datum `StandardInsideCountLocallyConstant`:
the inside-disk root count of the fibre polynomial is locally constant on the
open arc.  This is the smallest honest residual behind root-count constancy; it
is provided by Rouché's theorem / the argument principle (continuity of roots
with no boundary crossing), which is not available in the current Mathlib. -/
````

**L55–L60**

````text
/-- **Rouché interface ⟹ the assembled minimal root-data interface.**

This re-exports the already-proved reduction
`standardReturnMultiplierRootDataMinimal_of_localConstancy`, phrased through the
named residual `StandardRoucheRootCountStability`, so that the entire remaining
root-data content is visibly pinned to the single Rouché theorem-type. -/
````

### `four time frequency shift/RequestProject/HRT/HolonomyIdentificationDischarge(1).lean`

Content ID `1d746c2efa0aff36`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L74**

````text
/-!
# Holonomy-identification discharge run

This module performs the **holonomy-identification discharge run** for the
conditional final assembly theorem.  Its purpose is to remove or minimize the
single remaining substantive field `hJholo` of the minimal winding interface
`CriticalMixedMinimalWindingInterface` (in `WindingInterfaceDischarge.lean`).

## Task A — the exact statement of `hJholo`

For a fibre `t ∈ (a₀, b₀)` with nonzero leading coefficient
`evalLaurentCircle ad t ≠ 0`, and for **any** continuous `1`-periodic logarithm
`ell_t` of the bivariate Laurent return loop `evalBiLaurentPoly coeffs Mlau t`,
the field asserts the holonomy identification
```
  gaugeReturnMultiplier H θ t = exp (∫₀¹ ell_t).
```
Here `gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` is the *analytic* gauge
value, while `exp(∫₀¹ ell_t)` is the *algebraic* loop holonomy.

Objects appearing:

* holonomy function `J = gaugeReturnMultiplier H θ` — the geometric gauge;
* gauge holonomy `gaugeReturnMultiplier H θ` — `H t · exp(-2π i θ t)`;
* periodic logarithm `ell_t` — any `IsPeriodicLog` of the return loop;
* bivariate Laurent evaluation loop `evalBiLaurentPoly coeffs Mlau t`;
* active interval/window `(a₀, b₀)`;
* return multiplier — the fibre polynomial `fibrePoly coeffs t`;
* analytic amplitude `H`.

## Task B — adapter equalities (proved here, no axioms)

By the Jensen holonomy formula `complex_jensen_holonomy_product` together with
the canonical root factorisation `return_multiplier_local_root_factorization`,
the algebraic side `exp(∫₀¹ ell_t)` is **independent of the choice of `ell_t`**
and equals the choice-free algebraic loop holonomy
```
  algReturnHolonomy coeffs ad t
    = evalLaurentCircle ad t · ∏_{z ∈ roots(fibrePoly), ‖z‖>1} (−z).
```
This is `return_multiplier_holonomy_eq_integral_log`.  Consequently the `hJholo`
field is *equivalent*, given the root-data interface, to the strictly smaller and
more explicit purely algebraic identification
```
  gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t,
```
with no quantification over periodic logarithms and no integral.

## Tasks C/D — outcome

The remaining identity `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`
equates the *analytic* gauge value `H t · exp(-2π i θ t)` with the *algebraic*
root product.  This is the genuine analytic↔algebraic bridge and cannot be
derived inside the project from the available stages, so full discharge of
`hJholo` (and hence complete removal of the winding interface, Task C) is not
achieved.  Per the Task D fallback policy we therefore isolate exactly this one
equality as the single-field interface
`CriticalMixedHolonomyIdentificationInterface`, which is strictly smaller and
more explicit than `CriticalMixedMinimalWindingInterface` (it drops the
`∀ ell_t` quantifier and the loop integral).  The headline endpoint
`critical_mixed_final_contradiction_with_holonomy_identification_interface`
restates the conditional final contradiction using it.

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/HolonomyLawBridge(1).lean`

Content ID `55ca30e4d0ec4303`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L84**

````text
/-!
# Analytic–algebraic holonomy bridge discharge run

This module performs the **analytic–algebraic holonomy bridge discharge run** for
the conditional final assembly theorem.  Its purpose is to remove or further
minimize the single remaining holonomy-identification field

```
  hJalg : gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t
```

of `CriticalMixedHolonomyIdentificationInterface`
(`HolonomyIdentificationDischarge.lean`).

## Task A — the exact data flow

The field `hJalg` equates the *analytic* gauge value
`gaugeReturnMultiplier H θ t = H t · exp(-2π i θ t)` with the *algebraic* loop
holonomy `algReturnHolonomy coeffs ad t`.  Following the intended mathematical
content:

1. the gauged cocycle is `A_t(x) = exp(2π i θ t) · B_t(x)` with `B_t` the
   algebraic Laurent return loop;
2. the analytic holonomy `H` of `A` is **constant** on the active interval
   `(a₀, b₀)` by the resonance / analytic-rigidity argument
   (`analytic_map_into_resonance_group_constant`);
3. the holonomy of `B` is therefore `exp(-2π i θ t)` times that constant;
4. the previous run proved that the loop holonomy of `B` equals
   `algReturnHolonomy coeffs ad t` (`return_multiplier_holonomy_eq_integral_log`);
5. hence `gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t`.

The classification of each ingredient is recorded in
`HOLONOMY_LAW_BRIDGE_STATUS.md`.

## Task B — the analytic holonomy constancy law (CLOSED_IN_LEAN)

Step 2 above is *fully discharged inside Lean* as
`active_analytic_holonomy_constant`: the analytic, nonvanishing amplitude `H`,
whose values lie in the Haar-null resonance group on the positive-measure active
set `S`, is constant on the whole active window `(a₀, b₀)`.  This is exactly the
analytic-rigidity input previously regarded as the irreducible obstacle, and it
no longer needs to be assumed.

## Tasks C/D/E — the residual algebraic-phase identity

After discharging the analytic-rigidity constancy, the only residual content of
`hJalg` is the *pointwise algebraic-phase identity*

```
  algReturnHolonomy coeffs ad t = H s₀ · exp(-2π i θ t),
```

which references the analytic amplitude **only through its single constant value**
`H s₀` at one reference fibre, together with the rotation phase.  It carries no
analytic-function content whatsoever — the entire analytic-rigidity argument has
been internalized.  This residual is isolated as the single-field interface
`CriticalMixedHolonomyConstancyInterface`, strictly smaller and more explicit
than `CriticalMixedHolonomyIdentificationInterface` (whose field `hJalg` still
refers to the analytic amplitude `H` as a function of the fibre).

From this constancy interface we reconstruct
`CriticalMixedHolonomyIdentificationInterface`
(`CriticalMixedHolonomyConstancyInterface.toHolonomyIdentification`), and the
headline endpoint
`critical_mixed_final_contradiction_with_holonomy_constancy_interface` restates
the conditional final contradiction using it.

Full unconditional discharge of `hJalg` (Task D's interface-free endpoint) is
*not* achieved: it would require the link between the abstract Zak-model
amplitude `H` and the concrete algebraic return loop `evalBiLaurentPoly`, which
is genuinely absent from the available interface data.

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

**L115–L129**

````text
/-- **Minimal `HOLONOMY_CONSTANCY` interface.**

The strictly smaller and more explicit replacement for the holonomy-
identification interface `CriticalMixedHolonomyIdentificationInterface`.  After
the analytic-rigidity constancy of `H` is discharged in Lean
(`active_analytic_holonomy_constant`), the only residual content of `hJalg` is
the *pointwise algebraic-phase identity*

```
  algReturnHolonomy coeffs ad t = H s₀ · exp(-2π i θ t),
```

which references the analytic amplitude only through its single constant value
`H s₀` at one reference fibre `s₀ ∈ (a₀, b₀)`, together with the rotation phase.
There is no analytic-function content remaining. -/
````

### `four time frequency shift/RequestProject/HRT/HolonomyResidualClosure(1).lean`

Content ID `4a6cd53dc3f2f5d8`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L12–L58**

````text
/-!
# Holonomy residual closure run

This module performs the **holonomy residual closure run**.  The active-fibre
winding-zero-on-arc run reduced the remaining holonomy-amplitude interface to
exactly three residual theorem types

```
StandardAEActiveFibreWindingZero                  (a.e. winding zero on active set)
StandardWindingLocallyConstantZeroFreeFamily      (local constancy on the arc)
StandardWindingZeroHolonomyBridge                 (zero-winding ⇒ holonomy)
```

This run **reduces each of the three residuals to a strictly smaller and more
canonical upstream interface**, and proves — fully in Lean, with no new
`sorry`/`axiom`/`admit` — that the upstream interface implies the residual.  The
three upstream interfaces are exactly the *acceptable final blockers* of the run
instructions:

* `StandardMeasurableWindingObstructionForActiveFibres` — the genuine **inputs**
  of the already-formalised measurable winding obstruction
  (`measurable_cocycle_winding_eq_zero`) holding for a.e. active fibre.  From it we
  *derive* the a.e.-winding-zero residual `StandardAEActiveFibreWindingZero`
  (`StandardAEActiveFibreWindingZero_proved`).

* `StandardWindingHomotopyInvarianceZeroFreeLoops` — the statement that the
  integer winding number, viewed as a real-valued function, varies **continuously**
  on the zero-free analytic family over the arc (the content of homotopy
  invariance of the winding number for nonvanishing loops).  From continuity of an
  integer-valued function we *derive* local constancy
  `StandardWindingLocallyConstantZeroFreeFamily`
  (`StandardWindingLocallyConstantZeroFreeFamily_proved`).

* `StandardZeroWindingPeriodicLogHolonomyBridge` — the canonical, choice-free
  per-fibre identification `gauge = algReturnHolonomy` at zero-winding fibres.  Via
  the already-proved `return_multiplier_holonomy_identification` and the root data
  this *derives* the periodic-log/integral bridge
  `StandardWindingZeroHolonomyBridge`
  (`StandardWindingZeroHolonomyBridge_proved`).

Finally the three upstream interfaces (with the root data) are assembled into the
downstream endpoints (`StandardActiveFibreWindingZeroOnArc_fully_proved`,
`StandardCanonicalAmplitudeCompatibility_fully_proved`, and the final
contradiction `critical_mixed_final_contradiction_holonomy_residuals_reduced`).

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/ImportedRemainingCertificates(1).lean`

Content ID `1cd68a74118ce8be`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L52**

````text
/-!
# Imported remaining certificates — clean adapter layer

This module is the single clean place collecting the **exact** remaining
classical-input interfaces of the critical mixed-arithmetic four-point HRT
certification, together with the honest *conditional* adapter endpoints that
already feed each interface into the downstream certificate.

## Status of the remaining blockers (see `IMPORTED_REMAINING_CERTIFICATES_STATUS.md`)

Three of the remaining blockers are isolated in the project as precisely-typed
`Prop`/`Type` residuals (each is a named classical theorem that is **not** in
Mathlib for this toolchain — verified by source search: no `three_gap`,
`Rouche`, or `argument_principle` declarations exist in Mathlib `v4.28.0`):

* `StandardInsideCountLocallyConstant` / `StandardRoucheRootCountStability`
  (Rouché / argument principle: the inside-disk root count of a continuous
  family of fibre polynomials with no boundary roots is locally constant);
* `StandardCenteredOrbitGridProperty`
  (the centered three-distance / best-approximation theorem for continued-fraction
  convergent denominators);
* `StandardCanonicalAmplitudeResonanceProperty`
  (measurable-winding holonomy quantization: the canonical loop-holonomy amplitude
  lands in the resonance group on a positive-measure active set).

The remaining four classical inputs named in the task
(`StandardCriticalMixedNormalForm`, `StandardFourTermRelationToNormalizedRelation`,
`StandardThreePointNonzeroCoefficients`,
`StandardNormalizedContradictionImpliesLinearIndependence`) are the final
geometric-assembly content (`SL(2,ℤ)`/metaplectic normal form, the three-point
HRT theorem, and the linear-independence extraction).  These are **not** present
as Lean declarations anywhere in the project; they correspond to the deep
infrastructure that the single remaining theorem-body `sorry`
(`critical_mixed_orbit_HRT_L2` in `MainStatement.lean`) represents, and which is
not in Mathlib.  They are therefore left as genuinely-absent classical inputs and
documented (not stubbed, not axiomatised) in the status file.

Because none of the eight blockers is provable unconditionally from Mathlib or an
existing certified project endpoint, this file does **not** introduce any
unconditional `_proved` endpoint for them (doing so would require `sorry` or an
axiom).  Instead it pins each *existing* residual to a single canonical alias and
re-exports the honest *conditional* adapter that already feeds it into the
certificate.  No `sorry`, `admit`, `axiom`, `unsafe`, or `@[implemented_by]`
appears here.
-/
````

### `four time frequency shift/RequestProject/HRT/NontrivialAEFiberExtraction(1).lean`

Content ID `d7dfa4b80ffa4b8b`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L15–L57**

````text
/-!
# Stage 6B — the *nontrivial* a.e. fibre extraction (repair run)

The previously discharged `StandardAEFiberExtractionTheorem`
(`AEFiberExtraction (Lp ℂ 2 volume) ZakTarget`) is a pure **existence** statement
with **no nonvanishing constraint** on the extracted fibre function, and with the
model `Z`, window `f` and HRT relation `_hrel` all unused in the conclusion.
Consequently it is satisfied by the **zero fibre function** `F = 0`, so it does
not connect a nonzero `L²` window to nonzero active fibres or to genuine
return-cocycle data: it is *formally valid but too weak*.

This module formulates the honest strengthening:

* `oneStepEquation` — the one-step Zak fibre equation as a predicate of `(x,s)`.
* `NontrivialAEFiberExtraction` — a strengthened extraction structure carrying a
  **nonzero window**, the Plancherel/isometry tie `∫₀¹ (fibre density) = ‖window‖²`
  (so `F` genuinely represents the `L²` Zak transform's mass, ruling out `F = 0`),
  the **a.e.** one-step fibre equation, and (derived) **positive-measure active
  fibres**.
* `PointwiseNontrivialFiberData` — the variant carrying the *pointwise* one-step
  equation consumed downstream by `NormalizedReturnData`, again with the nonzero
  Plancherel tie (so still not satisfiable by `F = 0`).

We prove:

* the basic `Lp`/a.e. extraction lemmas that the zero-function shortcut skipped
  (TASK C);
* active-set positivity from a nonzero window via the concrete Zak Plancherel
  identity (TASK D);
* that the strengthened structures are **not** satisfiable by `F = 0`
  (`NontrivialAEFiberExtraction.window_ne_zero_forces_F_ne_zero`);
* the **genuine, non-vacuous downstream bridge** from `PointwiseNontrivialFiberData`
  to the Stage 5 no-flat-band contradiction (TASK F);
* the precise isolation of the two remaining analytic obligations as Lean
  propositions (TASK H): producing the nontrivial extraction from a nonzero
  window/relation, and upgrading the a.e. one-step equation to the pointwise data
  consumed downstream.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.  The weak
zero-witness theorem is left in place (documented as insufficient); **none** of
the strengthened results below use it, and the zero function is never used as a
witness for any strengthened statement.
-/
````

**L254–L258**

````text
/-- A `PointwiseNontrivialFiberData` term yields the Stage 6A `NormalizedReturnData`
needed by the Stage 5 no-flat-band machinery.  (The remaining structural data
— `m > 0`, irrationality of `m·a`, nonvanishing of the coefficients, the
unimodular basis — is supplied as hypotheses, exactly as in
`zak_relation_feeds_normalized_no_flat_band_AE`.) -/
````

**L322–L322**

````text
/-! ## TASK H — isolation of the two remaining analytic obligations -/
````

**L324–L332**

````text
/-- **Remaining obligation 1 — the genuine nontrivial extraction.**

For the concrete a.e. Zak model, a **nonzero** window satisfying a normalized
four-term HRT relation produces a `NontrivialAEFiberExtraction`.  This is the
honest analytic content skipped by the zero witness: choosing an `L²`
representative of `Z.Zak f`, transferring the `L²`-class one-step equation to the
a.e. fibre equation, and recording the Plancherel tie.  It is *not* an axiom; it
is the precisely-typed remaining proposition.  (It is *unsatisfiable* by `F = 0`,
since the Plancherel tie with `window = f ≠ 0` forces positive fibre mass.) -/
````

**L343–L366**

````text
/-- **Remaining obligation 2 — the a.e.-to-pointwise fibre upgrade.**

**DEPRECATED / AVOIDABLE (AE refactor run).**  `StandardPointwiseFiberUpgradeTheorem`
is *not* the correct target for `L²` data: it asks for an a.e. fibre equation to
be upgraded to a pointwise-everywhere fibre equation, which is generally **too
strong** for an arbitrary `L²` quotient class (representatives are only defined up
to a null set).  It is **replaced** by the a.e.-level normalized return-cocycle
machinery in `AENormalizedReturnCocycle.lean` /
`AEReturnCocycleToNoFlatBand.lean`: the structure `AENormalizedReturnData`
consumes the honest **a.e.** one-step equation directly, the a.e. `m`-step return
cocycle is obtained by a.e. iteration
(`AENormalizedReturnData.ae_normalized_m_step_return_cocycle`), and
`critical_mixed_final_contradiction_with_nontrivial_AE_Zak_no_pointwise_upgrade`
derives the no-flat-band contradiction from
`StandardNontrivialFiberExtractionTheorem` alone, **without** this upgrade.  This
definition is retained (not deleted) only for documentation and backward
compatibility; downstream Stage 6B results no longer depend on it.

The Stage 5 no-flat-band machinery consumes the one-step equation **pointwise**
(`NormalizedReturnData.hone : ∀ x s`).  Upgrading the honest **a.e.** one-step
equation of a `NontrivialAEFiberExtraction` to the pointwise
`PointwiseNontrivialFiberData` (repairing the null set of bad fibres while keeping
the multiplicative relation and the Plancherel tie) is isolated here.  Not an
axiom. -/
````

### `four time frequency shift/RequestProject/HRT/NontrivialFiberExtractionConstruction(1).lean`

Content ID `f73d8a21f4570148`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L65**

````text
/-!
# Stage 6B — reducing the nontrivial a.e. fibre extraction to a pure
fibre-construction statement

The honest Zak-side blocker recorded by the previous run is
`StandardNontrivialFiberExtractionTheorem`
(`RequestProject/HRT/NontrivialAEFiberExtraction.lean`):

```
∀ (Z : L2ZakModelAE (Lp ℂ 2 volume) ZakTarget) (m p a c₀ c₁ c₂ c₃) (hc₃ : c₃ ≠ 0)
  (r₁ t₁ r₂ t₂) (f : Lp ℂ 2 volume) (hf : f ≠ 0)
  (hrel : c₀ • f + c₁ • Z.shift r₁ t₁ f + c₂ • Z.shift r₂ t₂ f
            + c₃ • Z.shift a (p/m) f = 0),
  Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂)
```

A crucial observation about the `NontrivialAEFiberExtraction` structure: its only
tie to the window `f` is

* `window := f`, `h_window_ne := hf`, and
* the Plancherel mass tie `∫₀¹ fiberDensity F s ds = ‖window‖²`.

The fibre function `F` is **not** required to be (a representative of) `Z.Zak f`;
it is only required to be `1`-periodic in `s`, have interval-integrable fibre
density, carry total fibre mass `‖f‖²`, and satisfy the **a.e.** one-step Zak
fibre equation `oneStepEquation … F x s`.  Consequently the abstract model `Z`,
its opaque covariance operators `charLattice`/`charRogue`, and the HRT relation
`hrel` play **no role** in populating the structure: the entire content reduces
to the existence of *some* fibre function `F : ℝ → ℝ → ℂ` with the four listed
properties and an adjustable positive total mass.

This module isolates exactly that residue as the pure functional-equation
proposition `StandardNontrivialFiberConstructionTheorem`, and proves the
reduction

```
StandardNontrivialFiberConstructionTheorem → StandardNontrivialFiberExtractionTheorem
```

(`standardNontrivialFiberExtractionTheorem_of_construction`).  The reduction is
honest plumbing: given a nonzero window `f`, apply the construction at the target
mass `M = ‖f‖² > 0` and assemble the structure with `window := f`.

It also rewires the final Stage 6B contradiction so that, on the Zak side, it
depends **only** on `StandardNontrivialFiberConstructionTheorem` — the abstract
a.e. Zak model, its covariance operators, and the HRT relation no longer appear
as a Zak-side interface
(`critical_mixed_final_contradiction_without_Zak_extraction_interface`).

The remaining Zak-side obligation is therefore the smallest possible exact
statement: construct a single fibre function solving the a.e. one-step Zak fibre
equation with prescribed positive total mass.  This is recorded — *not* as an
axiom — as `StandardNontrivialFiberConstructionTheorem`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/
````

### `four time frequency shift/RequestProject/HRT/PeriodicDKClosure(1).lean`

Content ID `99fbee808168d6e6`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L34**

````text
/-!
# Closure of the corrected periodic Denjoy–Koksma interface

`RequestProject.Rotation.PeriodicKoksma` proves **Koksma's inequality**
(`koksma_real_periodic`, packaged as `standardPeriodicKoksmaInequality_proved`),
the analytic reduction from the orbit star-discrepancy bound to the periodic real
Denjoy–Koksma estimate.  Consequently the entire faithful periodic interface
`RealDenjoyKoksmaPeriodic θ` is constructible from the *single* remaining
combinatorial input

```
StandardRealDenjoyKoksmaCombinatorics θ
```

(the three-gap / best-approximation star-discrepancy bound for continued-fraction
denominators), via `RealDenjoyKoksmaPeriodic.ofStarDiscrepancy`.

This module records the **closed** downstream endpoints: each consumes
`StandardRealDenjoyKoksmaCombinatorics θ` directly (instead of a
`RealDenjoyKoksmaPeriodic θ` term), thereby exhibiting that the whole corrected
periodic Denjoy–Koksma chain — through the complex estimate, the uniform
return-sum convergence, the resonance corollary, and the final conditional
contradiction — is reduced to exactly one combinatorial theorem type.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/
````

### `four time frequency shift/RequestProject/HRT/QuasiperiodicTargetOperatorFormula(1).lean`

Content ID `a0021963dc1e4c79`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L57**

````text
/-!
# Stage 6B — the quasiperiodic target-operator formulas, reduced to their
exact minimal representative interface

This module addresses the two remaining Zak-side target-operator formula blockers
isolated in `ActualZakQuasiperiodicRepresentative.lean`:

```
StandardTargetLatticeOperatorFormulaQuasiAE
StandardTargetRogueOperatorFormulaQuasiAE
```

## Why the blockers are *exactly* the remaining content

The canonical concrete a.e. Zak model `concreteAEZakModel` is obtained as a
`Classical.choice` of `Nonempty (L2ZakModelAE …)`; the abstractly transported
covariance operators `concreteAEZakModel.charLattice` /
`concreteAEZakModel.charRogue` are therefore only known through the **abstract
covariance laws** (`lattice_cov`, `rogue_cov`) of the model.  No explicit
pointwise/fibre representative of these operators is available from the model
structure alone, so the explicit a.e. fibre action of the covariance operators is
the genuinely missing Zak-analytic input.  It is isolated here (NOT as an axiom),
in the smallest exact form.

## What is proved here (no `sorry`, no axiom)

* `StandardTargetLatticeOperatorRepresentativeAE` — the **minimal modulation
  form** of the lattice operator formula: on the fundamental square the lattice
  covariance operator acts as multiplication by the lattice character
  `exp(-2π i (t x + r s))` on the *target class itself* (no quasiperiodic
  representative needed, since the two agree a.e. on the square).
* `StandardTargetRogueOperatorRepresentativeAE` — the minimal rogue form; the
  rogue operator genuinely transports the fibre off the fundamental square, so
  the quasiperiodic representative cannot be eliminated, and this coincides with
  `StandardTargetRogueOperatorFormulaQuasiAE`.
* `StandardTargetLatticeOperatorFormulaQuasiAE_iff_representative` — the lattice
  blocker is **equivalent** to its minimal modulation form (the only difference
  is replacing the target class by its a.e.-equal quasiperiodic representative).
* `StandardTargetRogueOperatorFormulaQuasiAE_iff_representative` — the rogue
  blocker equals its minimal form definitionally.
* `charLattice_apply_quasiRep_ae_closed`,
  `charRogue_apply_quasiRep_ae_closed` — the explicit a.e. fibre actions, now
  derived from the *minimal* representative interface.

These reductions discharge no genuine analytic content on their own (the
representative interface is logically equivalent to the original blocker); their
purpose is to record the blocker in its smallest, most canonical form, tied
directly to the target class and the lattice/rogue characters.
-/
````

### `four time frequency shift/RequestProject/HRT/QuasiperiodicZakSideDischarge(1).lean`

Content ID `0fea664550763313`; 2 byte-identical path(s); full file source review; see R48; not build-verified.

**L9–L42**

````text
/-!
# Stage 6B — discharging the whole quasiperiodic Zak side from the two
target-operator formulas

This module proves that the two remaining target-operator formula blockers

```
StandardTargetLatticeOperatorRepresentativeAE
StandardTargetRogueOperatorRepresentativeAE
```

are **sufficient** to discharge the corrected quasiperiodic Zak-side blocker
`StandardActualZakQuasiRepresentativeEquationAE` and all downstream endpoints.

The argument:

1. `oneStepEquation_ae_square_of_operatorFormulas` — applying the (unconditional)
   target `Lp` one-step relation `target_Lp_one_step_Zak_relation` and the two
   operator formulas, the one-step fibre equation for the quasiperiodic
   representative holds a.e. on the fundamental square `zakSquareMeasure`.
2. `oneStepEquation_quasiRep_succ_x_iff` / `oneStepEquation_quasiRep_succ_s_iff`
   — the one-step equation for the quasiperiodic representative is invariant under
   the integer translations `x ↦ x+1`, `s ↦ s+1` (the matching characters cancel,
   using `zakQuasiPeriodicRep_quasiperiodic_x` and `zakQuasiPeriodicRep_periodic_s`).
3. `ae_iterated_of_ae_square_of_periodic` — a general measure-theoretic transport:
   a `ℤ²`-translation-invariant property that holds a.e. on the half-open unit
   square holds a.e. (iterated) on all of `ℝ²` (the square tiles `ℝ²`, and the
   bad set is contained in a countable union of null translates).
4. `StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas` — the
   assembled discharge of the corrected blocker.
5. The closed downstream endpoints.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/
````

### `four time frequency shift/RequestProject/HRT/ReturnCocycleToNoFlatBand(1).lean`

Content ID `49c0bae15d4c72e9`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L167–L190**

````text
/-
**Part D + E — synthesizing the periodic logarithm input.**

This upgrades `normalized_return_cocycle_feeds_no_flat_band_integrated` by
**eliminating the explicit periodic-logarithm hypotheses `ell` and `hell`**.

The imported certificate's `ell`/`hell` inputs are *not* independent data: a
periodic logarithm of the bivariate Laurent loop `evalBiLaurentPoly coeffs M t`
is completely determined (up to the harmless `2πi`-integer ambiguity) by the
root factorisation `hroots`, via
`CriticalMixedHRT.evalBiLaurentPoly_periodic_log_of_roots`.  Hence we construct
`ell` internally from `hroots` (by classical choice) and discharge `hell`.

What remains of the holonomy identification is reformulated as the single,
choice-free hypothesis `hJholo`, which identifies the geometric holonomy `J t`
with the loop-determined value `exp(∫₀¹ ell_t)` for *any* periodic logarithm
`ell_t` of the loop (the value is independent of the choice by
`exp_integral_periodic_log_eq`).  This is strictly weaker to supply than the
previous `ell` + `hell` + `hJlog` triple, while remaining provably equivalent.

The per-fibre root factorisation `hroots` (encoding the bivariate z-factorisation
of the return multiplier) is retained as the final explicit local-certificate
interface datum, per the task's documented fallback policy.
-/
````

### `four time frequency shift/RequestProject/HRT/ReturnMultiplierRootData(1).lean`

Content ID `1b1be013536b6224`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L48**

````text
/-!
# Return-multiplier root data — canonical factorisation of the fibre polynomial

The imported local holonomy certificate
(`local_holonomy_certificate_full_periodic_log_form`) consumes, per fibre `t`,
the *root factorisation data* `hroots`:

* an explicit root enumeration `r : Fin d → ℂ`,
* the off-circle condition `∀ i, ‖r i‖ ≠ 1`,
* the winding bookkeeping `M = #{i : ‖r i‖ < 1}`, `#{i : 1 < ‖r i‖} = m`,
* the polynomial factorisation identity
  `C (ad(t)) · ∏ᵢ (X − r i) = ∑ⱼ C (coeffsⱼ(t)) Xʲ`.

This module shows that the **factorisation existence** and the **root
enumeration** parts of this data are *not* independent input: starting from the
polynomial-in-`z` representation `∑ⱼ C (coeffsⱼ(t)) Xʲ` of the return multiplier
(constructed in `ReturnMultiplierPolynomialInZ.lean`), and using only the
nonvanishing of its leading coefficient `evalLaurentCircle ad t ≠ 0`, the
fundamental theorem of algebra (`IsAlgClosed.splits` over `ℂ`) produces a
canonical root enumeration `r` with both the factorisation identity *and* the
multiset identity `roots = Multiset.map r univ.val`.

The latter multiset identity lets every root-count over `Fin d` be transferred
to a count over the canonical roots multiset, so the only genuinely substantive
remaining data are the **geometric** facts: the roots avoid the unit circle, and
the inside/outside counts equal `M` and `m`.  These are isolated as the minimal
root-data interface in `RootDataAdapter.lean`.

Main declarations:

* `polyOfCoeffs` — the fibre polynomial `∑ⱼ C (c j) Xʲ`;
* `polyOfCoeffs_coeff`, `polyOfCoeffs_natDegree`, `polyOfCoeffs_leadingCoeff`;
* `multiset_eq_map_fin` — a multiset of card `n` is `Multiset.map f univ.val`;
* `polyOfCoeffs_root_factorization` — the canonical factorisation + multiset id;
* `fibrePoly` — the certificate's per-fibre polynomial in `coeffs`/`t`;
* `return_multiplier_local_root_factorization` — the canonical factorisation,
  stated directly on the certificate's polynomial-in-`z` representation;
* `root_count_transfer`, `root_offcircle_transfer` — count / off-circle bridges
  from the canonical roots multiset to the `Fin d` enumeration.
-/
````

### `four time frequency shift/RequestProject/HRT/RootCountLocalConstancy(1).lean`

Content ID `ea6c12aaa1951e3a`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L45**

````text
/-!
# Root-count constancy from local constancy — canonical reduction of `Mlau`

`RootDataMinimalInterface.lean` reduced the certificate's root-data interface to a
single genuinely-missing analytic input, `StandardRootCountConstancyOnActiveArc`:
per fibre `t` in the active arc, the inside-disk root count of the fibre
polynomial equals a fixed integer `Mlau`.  In that form `Mlau` appears as free
"magic" data: a single integer that the count must equal at *every* fibre.

This module makes `Mlau` **canonical** and isolates the irreducible analytic input
in its smallest natural form.  The classical content behind root-count constancy
is *local*: as the parameter `t` varies and no root crosses the unit circle, the
number of roots strictly inside the unit disk is **locally constant** (Rouché /
continuity of roots).  Global constancy on the connected open arc then follows
from preconnectedness, and `Mlau` is no longer free data — it is pinned to the
count at any single reference fibre.

Main declarations:

* `fibreInsideCount` — the inside-disk root count of the fibre polynomial.
* `StandardInsideCountLocallyConstant` — the canonical (Rouché) analytic input:
  the inside-disk root count is locally constant on the open arc.  This is the
  smallest exact analytic datum remaining.
* `rootCount_constancy_of_locallyConstant` — local constancy together with a
  reference value at one fibre yields the global constancy datum
  `StandardRootCountConstancyOnActiveArc`; `Mlau` is pinned to the reference
  fibre.
* `standardReturnMultiplierRootDataMinimal_of_localConstancy` — assembles the full
  canonical reduced root-data interface `StandardReturnMultiplierRootDataMinimal`
  from the degree compatibility, the zero-free active arc, local constancy, and a
  reference value.
* `normalized_return_cocycle_feeds_no_flat_band_root_data_local_constancy` — the
  Stage 6A → Stage 5 bridge driven by the local-constancy interface, with the
  global root count, off-circle condition, outside count, factorisation, root
  enumeration, and periodic-log input all synthesised internally.
-/
````

**L112–L125**

````text
/-- **Stage 6A → Stage 5 bridge driven by the local-constancy interface.**

This is the strongest no-`sorry` Stage 6A bridge in Run A.  Compared with
`normalized_return_cocycle_feeds_no_flat_band_root_data_closed`, the inside-count
datum (`hin`, which carried the free integer `Mlau`) is replaced by:

* `hlc` — the inside-disk root count is *locally constant* on the active arc
  (the canonical Rouché/continuity content);
* `ht₀`, `hMlau` — `Mlau` is the inside count at a single reference fibre `t₀`.

The global root count, the off-circle condition, the outside count, the
factorisation identity, the root enumeration, and the periodic-logarithm input
are all synthesised internally.  The remaining holonomy identification is the
choice-free `hJholo`. -/
````

### `four time frequency shift/RequestProject/HRT/RootDataAdapter(1).lean`

Content ID `7538ced846d89bd0`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L146–L159**

````text
/-- **Stage 6A → Stage 5 bridge driven by the minimal root-data interface.**

This is the strongest no-`sorry` form of the Stage 6A bridge produced in this
run.  Compared with `normalized_return_cocycle_feeds_no_flat_band_synthesized`,
the explicit root-factorisation data `hroots` is replaced by the strictly
smaller minimal interface `hroots_min` (no caller-supplied root enumeration and
no caller-supplied factorisation identity — these are synthesised internally
from the polynomial-in-`z` representation by the FTA).  The periodic-logarithm
input is synthesised internally exactly as in `..._synthesized`, and the
remaining holonomy identification is the choice-free `hJholo`.

What is left in `hroots_min` is exactly the irreducible geometric content of the
local certificate: the roots of the canonical fibre polynomial avoid the unit
circle, and their inside / outside counts equal `Mlau` and `mlau`. -/
````

### `four time frequency shift/RequestProject/HRT/RootDataMinimalInterface(1).lean`

Content ID `bbafd0bf0541d6e7`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L217–L232**

````text
/-- **Stage 6A → Stage 5 bridge driven by the canonical reduced interface.**

This is the strongest no-`sorry` Stage 6A bridge produced in this run.  Compared
with `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`, the minimal
geometric interface `hroots_min` is itself replaced by the strictly smaller
canonical reduced interface:

* `hzf` — the return multiplier is zero-free along the active arc
  (`(fibrePoly coeffs t).eval (circleParam x) ≠ 0`); this *replaces* the
  off-circle root condition and the outside count;
* `hin` — the inside-disk root count equals `Mlau`;
* `hmM` — the single global numeric compatibility `(mlau : ℤ) = d - Mlau`.

The off-circle condition, the outside count, the factorisation identity, the root
enumeration, and the periodic-logarithm input are all synthesised internally.
The remaining holonomy identification is the choice-free `hJholo`. -/
````

### `four time frequency shift/RequestProject/HRT/StandardAEFiberExtraction(1).lean`

Content ID `66d3fa2b77e1dfbd`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L51**

````text
/-!
# Stage 6B — discharging the active-fibre extraction obligation

This module discharges the single remaining Zak-side blocker
`StandardAEFiberExtractionTheorem` (`AEFiberExtraction (Lp ℂ 2 volume) ZakTarget`)
and propagates the discharge through the Stage 6B bridge.

## What `AEFiberExtraction` actually requires

Unfolding the definition in `ZakToNormalizedCocycleAE.lean`, the proposition is:
for every a.e. Zak model `Z`, normalized data, and four-term relation, there
*exists* a fibre function `F : ℝ → ℝ → ℂ` that is `1`-periodic in its second
argument and satisfies the one-step Zak fibre equation

```
F (x - a) (s + p/m) = -c₃⁻¹ · exp(2πi (p/m) x) · P(x,s) · F x s        (∀ x s)
```

Two structural facts about this obligation:

* The conclusion only asserts the **existence** of such an `F`; it imposes **no
  nonvanishing requirement** on `F`, and the model `Z`, the vector `f`, and the
  HRT relation `_hrel` are **unused** in the conclusion.
* The downstream consumer `NormalizedReturnData` (and hence the proven
  no-flat-band machinery `normalized_return_cocycle_feeds_no_flat_band_synthesized`)
  uses these same fibre equations in their **pointwise** `∀ x s` form, never
  requiring `F` to be nonzero.

Consequently the honest discharge of the proposition *as stated* is the zero
fibre function `F = 0`: it is trivially `1`-periodic and satisfies the one-step
equation (both sides vanish).  This is sound (no `sorry`, no axiom) and removes
the Zak-side interface from every downstream contradiction theorem.

Note that the genuine "extract a pointwise-everywhere representative" reading is
*not* provable for arbitrary `L²` data: an a.e. equation on a quotient class only
yields the fibre equation almost everywhere, and one cannot in general repair a
null set of bad points while keeping the multiplicative relation valid at *every*
`(x,s)`.  The pointwise-everywhere proposition recorded by the previous run is
therefore discharged by the zero witness, with the genuine analytic content of
the no-flat-band obstruction residing entirely in the (non-Zak) return-multiplier
root data and holonomy hypotheses.
-/
````

### `four time frequency shift/RequestProject/HRT/ThreePointHRTAndCovariance(1).lean`

Content ID `fec4b1ee875b1ce8`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L65**

````text
/-!
# Three-point HRT and covariance certificate layer

This module continues the final geometric-assembly certification of
`critical_mixed_orbit_HRT_L2` by working on the two final
geometric/covariance certificate families:

1. the **three-point HRT theorem**;
2. the **affine-symplectic / metaplectic covariance** and normalized-relation
   transport.

It builds on `RequestProject.HRT.FinalGeometricAssembly`, which already isolated
the deep inputs as the exact named hypotheses

* `StandardThreePointHRTTheorem` — the three-point HRT theorem (phrased as a
  four-point injective family with one zero coefficient), and
* `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`) — the metaplectic /
  affine-symplectic covariance producing the Zak return-cocycle witness.

## What is genuinely proved here (no `sorry`, no `axiom`)

* `StandardThreePointGaborLinearIndependence` — the *direct* three-point phrasing
  (three distinct time-frequency translates of a nonzero `L²` function are
  linearly independent), and the **genuine equivalence** with the
  four-point-with-one-zero phrasing `StandardThreePointHRTTheorem`:

  - `StandardThreePointHRTTheorem_proved` :
    `StandardThreePointGaborLinearIndependence → StandardThreePointHRTTheorem`
  - `StandardThreePointGaborLinearIndependence_proved` :
    `StandardThreePointHRTTheorem → StandardThreePointGaborLinearIndependence`

  This connects whichever phrasing a future certified import provides to the
  exact phrasing consumed by the geometric-assembly layer.  It is real,
  `sorry`-free finite-index combinatorics (drop / re-insert the zero coordinate),
  not an alias.

* `StandardThreePointNonzeroCoefficients_fully_proved` — honest re-export of the
  geometric-assembly endpoint `StandardThreePointNonzeroCoefficients_proved`.

* `StandardFourTermRelationToNormalizedRelation_fully_proved` and
  `StandardCriticalMixedNormalForm_fully_proved` — honest re-exports of the
  genuine covariance reductions
  `StandardFourTermRelationToNormalizedRelation_proved` and
  `StandardCriticalMixedNormalForm_proved`.

## Honest scope statement (Tasks C, E)

The **three-point HRT theorem** itself (in either phrasing) and the
**metaplectic / affine-symplectic covariance** theorem are genuine deep results
absent from Mathlib `v4.28.0`; they remain isolated here as exact named
hypotheses, not discharged.  Consequently the sharper Task-E theorem
`critical_mixed_orbit_HRT_L2_conditional_on_analytic_inputs_only` (depending only
on the three deep analytic/classical inputs and *not* on three-point HRT or
covariance) is **not** provable in this run; it would require discharging exactly
those two deep inputs.  The honest current state is the
covariance-conditional theorem
`critical_mixed_orbit_HRT_L2_conditional_on_covariance`
(`FinalGeometricAssembly`), reproduced here through the equivalence as
`critical_mixed_orbit_HRT_L2_conditional_via_linearIndependence`.
-/
````

**L84–L92**

````text
/-- **Task B (forward adapter).**  The direct three-point linear-independence
statement implies the four-point-with-one-zero phrasing
`StandardThreePointHRTTheorem` consumed by the geometric-assembly layer.

Genuine reduction (no `sorry`): given an injective `P : Fin 4 → ℝ × ℝ`, an index
`i` with `d i = 0`, and an a.e.-vanishing four-term combination, drop the `i`-th
coordinate to obtain a three-term combination over the injective family
`P ∘ i.succAbove`; linear independence forces the remaining three coefficients to
vanish, and `d i = 0` finishes. -/
````

### `four time frequency shift/RequestProject/HRT/ZakToNormalizedCocycleAE(1).lean`

Content ID `1cde42567d60e0e2`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L77–L84**

````text
/-- **The active-fibre extraction proposition (TASK E blocker, abstract form).**

For an a.e.-level Zak model `Z : L2ZakModelAE V W`, every normalized four-term
HRT relation produces *pointwise* fibre data: a fibre function `F : ℝ → ℝ → ℂ`
that is `1`-periodic in the frequency variable and satisfies the one-step Zak
fibre equation for **every** `(x,s)`.  This is the active-fibre extraction step
(choice of `L²` representative + restriction to the full-measure active fibre
set).  It is *not* an axiom; it is the precisely-typed remaining obligation. -/
````

**L212–L216**

````text
/-- **The isolated active-fibre extraction obligation (TASK H blocker).**

The remaining a.e.-level Zak obligation, for the concrete model: the active-fibre
extraction proposition for `L²(ℝ)` valued in `L²([0,1]²)`.  Recorded as a
precisely-typed proposition; *not* an axiom. -/
````

### `four time frequency shift/RequestProject/HRT/ZeroWindingPeriodicLogBridge(1).lean`

Content ID `32c1d7285e1d3e35`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L74**

````text
/-!
# Zero-winding periodic-log holonomy bridge run

This module performs the **zero-winding periodic-log holonomy bridge run**.  The
holonomy-residual-closure run reduced the holonomy-amplitude interface to exactly
three upstream blockers, the last of which is the *zero-winding periodic-log
holonomy bridge*

```
StandardZeroWindingPeriodicLogHolonomyBridge θ a₀ b₀ ad coeffs H W
```

whose single field is the choice-free per-fibre identification

```
  ∀ t ∈ (a₀,b₀), evalLaurentCircle ad t ≠ 0 → W t = 0 →
    gaugeReturnMultiplier H θ t = algReturnHolonomy coeffs ad t.
```

This run **splits that bridge into its two genuine mathematical ingredients** and
proves that they (together with the already-available root data) imply the
bridge, thereby reducing it to the strictly smaller, more canonical blocker.

## Decomposition

The intended proof of the bridge is:

1. **Periodic-log existence** — from zero winding (here, from the explicit root
   factorisation supplied by the root data) the bivariate Laurent return loop
   `evalBiLaurentPoly coeffs Mlau t` admits a continuous `1`-periodic logarithm
   `ell`.  This is the blocker `StandardZeroWindingPeriodicLogExists`, and it is
   **fully proved** here (`StandardZeroWindingPeriodicLogExists_proved`) via the
   already-available `evalBiLaurentPoly_periodic_log_of_roots`.

2. **Loop-holonomy identity** — the analytic gauge value
   `gaugeReturnMultiplier H θ t` equals the loop holonomy `exp(∫₀¹ ell)` of any
   periodic logarithm of the return loop.  This is the blocker
   `StandardPeriodicLogIntegralEqualsLoopHolonomy`; it is the genuine
   analytic↔geometric content (the abstract amplitude `H` is *a priori*
   unrelated to `coeffs`), and is left as the single remaining holonomy input.

3. **Root-product holonomy** — the loop holonomy equals the choice-free algebraic
   holonomy: `exp(∫₀¹ ell) = algReturnHolonomy coeffs ad t`.  This is **already
   proved unconditionally** as `return_multiplier_holonomy_eq_integral_log`.

Chaining (1)–(3) gives `gauge = exp(∫ ell) = algReturnHolonomy`, i.e. the bridge.

## Outcome

* `StandardZeroWindingPeriodicLogHolonomyBridge_proved` — the bridge from the two
  ingredients plus root data.
* `zero_winding_periodic_log_holonomy_bridge` — the bridge reduced to the single
  genuinely-missing blocker `StandardPeriodicLogIntegralEqualsLoopHolonomy`
  (periodic-log existence is discharged internally).
* `StandardWindingZeroHolonomyBridge_fully_proved`,
  `StandardCanonicalAmplitudeCompatibility_with_two_holonomy_inputs`,
  `critical_mixed_final_contradiction_holonomy_two_inputs` — the downstream
  endpoints now consuming the two pure-winding blockers
  (`StandardMeasurableWindingObstructionForActiveFibres`,
  `StandardWindingHomotopyInvarianceZeroFreeLoops`) together with the single
  loop-holonomy input `StandardPeriodicLogIntegralEqualsLoopHolonomy`.

No axioms, `sorry`s, or `admit`s are introduced.
-/
````

**L118–L118**

````text
/-! ## Ingredient 2 — loop-holonomy identity (the single remaining blocker) -/
````

**L120–L131**

````text
/-- **`STANDARD_PERIODIC_LOG_INTEGRAL_EQUALS_LOOP_HOLONOMY`.**

The second — and only genuinely missing — ingredient of the bridge: at every
active, zero-winding fibre, the analytic gauge value
`gaugeReturnMultiplier H θ t` equals the loop holonomy `exp(∫₀¹ ell)` of *any*
continuous `1`-periodic logarithm `ell` of the bivariate Laurent return loop.

This is the irreducible analytic↔geometric bridge: the abstract analytic
amplitude `H` is *a priori* unrelated to the algebraic return data `coeffs`/`ad`,
so this identity is the precise remaining input.  It is strictly more canonical
than the previous bridge field, since it is stated purely via the geometric loop
holonomy `exp(∫₀¹ ell)` with no reference to the algebraic root product. -/
````

### `four time frequency shift/RequestProject/MainStatement(1).lean`

Content ID `142042cab9fa0889`; 2 byte-identical path(s); full file source review; see R46; not build-verified.

**L6–L34**

````text
/-!
# The critical mixed-arithmetic four-point HRT theorem: faithful statement

This file gives a faithful Lean statement of the main theorem (Theorem 1.1)
of the dossier.

The proof of the main theorem requires substantial analytic infrastructure
that is **not** present in Mathlib and would have to be built from scratch,
namely:

* the unitarity / quasi-periodicity theory of the **Zak transform**;
* the **three-point HRT theorem** (all coefficients of a nontrivial four-term
  Gabor relation are nonzero);
* the two **imported, separately-certified algebraic endpoints**
  (local Laurent holonomy certificate `C1`, and the no-Laurent
  irrational-character obstruction `C2`).

Accordingly the main theorem is recorded here with its proof left as `sorry`.
The genuinely self-contained new lemmas of the dossier that *are* within
Mathlib's reach are proved in the companion files:

* `RequestProject.TrinomialZeros`  — Lemma 5.1 (finite torus zero set);
* `RequestProject.ResonanceGroup`  — Lemma 6.6 (Haar-null resonance group);
* `RequestProject.NoLaurentObstruction` — Theorem 3.2 / `C2`.

The remaining lemmas (which depend on the pointwise Birkhoff ergodic theorem
and the Denjoy–Koksma inequality, neither in Mathlib) are recorded as stated
`sorry`s in `RequestProject.PendingLemmas`.
-/
````

### `four time frequency shift/RequestProject/Rotation/CenteredOrbitGrid(1).lean`

Content ID `6563b17684ea337c`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L4–L41**

````text
/-!
# Centered orbit grid ⇒ centered star-discrepancy bound

The corrected continued-fraction interface
`ContinuedFractionStarDiscrepancyData θ`
(`RequestProject.Rotation.StarDiscrepancyCorrection`) carries the *true* centered
orbit star-discrepancy bound

```
∀ n x, ∃ c, ∀ t ∈ [0,1], |orbitDiscrepancy θ (q n) x t − c| ≤ 1
```

(equivalently oscillation `≤ 2`).  This module reduces that analytic-over-all-`t`
bound to a strictly *combinatorial* and *finite* statement about the sorted orbit
points — the **centered orbit grid** property: for each `n` and base point `x`
there is a sorting permutation `σ` of the `q n` orbit points
`fract (x − j θ)` and a recentering constant `c` placing the `i`-th sorted point
in the *shifted* grid cell `[(i−c)/(q n), (i+1−c)/(q n))`.

This is the honest centered replacement of the **false** grid-balanced
`orbit_partition` field (which used `c = 0`, see
`star_discrepancy_le_one_false`).  It is exactly the three-distance /
best-approximation content for convergent denominators: the `q n` orbit points
divide `[0,1)` into at most two/three gap lengths, all close to `1/(q n)`, so the
sorted points track an evenly spaced grid up to the single shift `c`.

The reduction proved here (`centered_discrepancy_abs_le_one_of_centered_grid`) is
the converse direction of the project's `koksma_order_stat_centered`: a centered
grid for the sorted points yields the centered discrepancy bound directly, with
the *same* constant `c`.

This isolates the remaining number-theoretic gap as the single combinatorial
`Prop` `StandardCenteredOrbitGridProperty θ q`, strictly smaller than the
all-`t` discrepancy field, and wires it into a constructor for
`ContinuedFractionStarDiscrepancyData θ`.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]` are introduced.
-/
````

### `four time frequency shift/RequestProject/Rotation/ConcreteDenjoyKoksma(1).lean`

Content ID `719828b74e4ada85`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L30**

````text
/-!
# Reducing the variation-approximation hypothesis to L¹ density of derivatives
(Run C, Task 1, target 3)

Stage 2B's uniform return-sum theorem is conditional on the abstract predicate
`TrigApproxInVariation D φ`: that `φ` can be approximated, in the variation
functional carried by `D`, by mean-zero trigonometric polynomials.

For a *concrete* Denjoy–Koksma return data
`D = DenjoyKoksmaReturnData.ofConcrete R dk` (whose `HasBV`, `variation`, `mean`
are the genuine objects `ConcreteHasBV`, `concreteVariation`, `periodMean`), we
prove that `TrigApproxInVariation D φ` follows from the **standard `L¹` density
statement**: that for every `ε > 0` there is a mean-zero trigonometric
polynomial `P = trigPoly a s` (`0 ∉ s`) such that the remainder `φ - P` is `C¹`
on `[0,1]` with `∫₀¹ ‖(φ - P)'‖ < ε`.

This is the honest reduction requested: the only remaining input is the
classical density of trigonometric polynomials in `L¹` (here, density of their
derivatives, supplied by Fejér/Cesàro means), and the variation side is
discharged by the `C¹` variation bound `concreteVariation_le_integral_norm_deriv`
of `C1VariationApprox`.
-/
````

### `four time frequency shift/RequestProject/Rotation/ContinuedFractionTowers(1).lean`

Content ID `bbfe487859d14aa6`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L50**

````text
/-!
# Star-discrepancy combinatorics for the orbit (the isolated remaining target)

The faithful (periodic) real Denjoy–Koksma interface `RealDenjoyKoksmaPeriodic θ`
(see `RequestProject.Rotation.OrbitPartition`) carries the analytic inequality
over *all* `1`-periodic bounded-variation zero-mean functions.  Classically that
analytic statement follows from a single purely *combinatorial* fact about the
orbit — the **star-discrepancy bound** — via **Koksma's inequality**.

This module isolates that combinatorial fact:

```
|#{ j < Q : fract (x - j θ) ≤ t } − Q · t| ≤ 1   for all t ∈ [0,1].
```

For continued-fraction return denominators `Q = q n` this bound is the classical
three-gap / best-approximation discrepancy estimate (not in Mathlib).  It is a
*strictly smaller and more combinatorial* interface than the analytic
`dk_real_periodic` field: it makes no reference to bounded variation, integrals,
or arbitrary functions — only to counting orbit points.

## What is proved here (no `sorry`)

* the orbit-counting / discrepancy definitions;
* the candidate strictly-smaller interface `StandardRealDenjoyKoksmaCombinatorics`;
* the periodicity reduction `periodic_eval_fract` (Birkhoff sums of a periodic
  function only see the fractional parts of the orbit), an ingredient of Koksma's
  inequality;
* the boundary value `orbitDiscrepancy_one` of the discrepancy function.

## What remains (the exact isolated gap)

Two classical facts not in Mathlib:

1. **Koksma's inequality** (analytic reduction): from `star_discrepancy_le_one`,
   derive the `dk_real_periodic` field of `RealDenjoyKoksmaPeriodic θ`.  Its proof
   is Stieltjes integration by parts pairing the discrepancy with the Stieltjes
   measure of a bounded-variation function, machinery currently absent from
   Mathlib.
2. **The discrepancy bound itself** for continued-fraction denominators (the
   three-gap / best-approximation estimate).

Given a proof of (1) as `koksma_real_periodic`, the constructor
`RealDenjoyKoksmaPeriodic.ofCombinatorics` (below in commented form) would build
the faithful interface from `StandardRealDenjoyKoksmaCombinatorics`.
-/
````

### `four time frequency shift/RequestProject/Rotation/DenjoyKoksmaDischarge(1).lean`

Content ID `1822ed2da6ae7167`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L12–L42**

````text
/-!
# Denjoy–Koksma discharge run

The Stage 2B return data `DenjoyKoksmaReturnData θ` carries the Denjoy–Koksma
estimate as a field, and `DenjoyKoksmaReturnData.ofConcrete` instantiates it from
the *complex-valued* Denjoy–Koksma inequality

```
∀ g : ℝ → ℂ, ConcreteHasBV g → periodMean g = 0 →
  ∀ (n : ℕ) (x : ℝ),
    ‖∑ j ∈ Finset.range (R.q n), g (x - j θ)‖ ≤ concreteVariation g
```

This module performs a genuine, no-`sorry` **reduction** of that complex
estimate to the standard **real-valued** Denjoy–Koksma inequality (with the same
constant `1`), packaged in the explicit hypothesis structure
`RealDenjoyKoksma θ` (this is a `structure`, *not* an axiom).

The reduction is the elementary "optimal direction" projection: for a fixed
complex Birkhoff sum `S`, projecting `g` onto the unit phase `w = conj S / ‖S‖`
turns the complex sum norm `‖S‖` into the real sum `∑ (w · g)·re`, whose real
variation is `≤ concreteVariation g` (the projection `z ↦ (w·z).re` is
`1`-Lipschitz) and whose real mean vanishes. The real Denjoy–Koksma inequality
then yields `‖S‖ ≤ concreteVariation g`.

Consequently the remaining blocker `DK_VARIATION_INTERFACE` is reduced from the
complex estimate to the canonical real Denjoy–Koksma theorem
(`RealDenjoyKoksma.dk_real`), which is the standard formulation found in the
literature (Kuipers–Niederreiter / Herman). The reduction itself is fully
proved here.
-/
````

### `four time frequency shift/RequestProject/Rotation/DenjoyKoksmaPeriodicDischarge(1).lean`

Content ID `cc0f8fea5f20e51f`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L14–L40**

````text
/-!
# Corrected (periodic) Denjoy–Koksma discharge

`RequestProject.Rotation.RealDenjoyKoksma` proves that the previous run's
`RealDenjoyKoksma θ` structure is **uninhabitable**: its `dk_real` field omits the
periodicity hypothesis required by the classical Denjoy–Koksma theorem
(`dk_real_predicate_false`, `realDenjoyKoksma_isEmpty`).  Consequently every
endpoint of `RequestProject.Rotation.DenjoyKoksmaDischarge` that takes a
`RealDenjoyKoksma θ` argument — `concrete_denjoy_koksma_estimate`,
`DenjoyKoksmaReturnData.ofStandardDK`, `concrete_denjoy_koksma_return_data`,
`c1_zeroMean_returnSum_tendstoUniformly_concrete` — is *vacuously* applicable
(its hypothesis can never be supplied) and must not be used as certification
evidence.

This module rebuilds those four endpoints on the **faithful, satisfiable**
interface `RealDenjoyKoksmaPeriodic θ` (see
`RequestProject.Rotation.OrbitPartition`), whose Denjoy–Koksma field is
restricted to `1`-periodic functions.  The complex reduction uses the already
proved `complex_denjoy_koksma_of_real_periodic`.

Because the complex periodic estimate only holds for `1`-periodic functions, the
abstract `HasBV` predicate of the resulting `DenjoyKoksmaReturnData θ` is taken
to be `ConcreteHasBV g ∧ Function.Periodic g 1`.  This keeps the Denjoy–Koksma
bound field *true* (it is only ever invoked on periodic functions), in contrast
to `ofStandardDK`, whose `HasBV = ConcreteHasBV` predicate would require the
false non-periodic estimate.
-/
````

### `four time frequency shift/RequestProject/Rotation/HolonomyQuantization(1).lean`

Content ID `e84878e1f8403355`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L11–L55**

````text
/-!
# Stage 3A: measurable holonomy quantization (conditional form)

This module formalizes **Stage 3A** of the certification plan: the measurable
holonomy-quantization step, under the standing assumption that a periodic
logarithm of the multiplicative cocycle is already available.

The geometric situation (cf. Lemma 6.5 of the dossier) is the following.  Let
`θ` be irrational and let `D : DenjoyKoksmaReturnData θ` provide the
continued-fraction return times `qₙ`.  Let `h : ℝ → ℂ` be a nonzero
`L²`-function (over one period) and let `b : ℝ → ℂ` be a non-vanishing cocycle
satisfying the functional equation
```
  h (x - θ) = b x * h x.
```
Given a periodic logarithm `ell` of `b` (`exp (ell x) = b x`), set
```
  c   = ∫₀¹ ell,      φ = ell - c,      H = exp c.
```
The holonomy-quantization theorem asserts that
```
  H ^ qₙ → 1,
```
i.e. the holonomy `H` lies in the resonance group `G_θ`.

## Proof architecture

1. `cocycle_iterate` — iterating the one-step cocycle through the return time
   `N` gives the exact `N`-step identity
   `h (x - N θ) = H^N · exp (∑_{j<N} φ (x - jθ)) · h x`.
2. `tendstoUniformly_exp_returnSum` — the Stage 2B uniform return-sum theorem,
   composed with `exp`, gives `exp (∑_{j<qₙ} φ(· - jθ)) → 1` uniformly.
3. `eLpNorm_mul_sub_one_tendsto_zero` — multiplying a fixed `L²` function by a
   sequence converging to `1` uniformly converges to it in `L²`.
4. `holonomy_limit_one_of_uniform` — the abstract `L²` combination: if
   `h ∘ Tₙ =ᵐ Hₙ · gₙ · h` with `|Hₙ| = 1`, `gₙ → 1` uniformly and
   `h ∘ Tₙ → h` in `L²`, then `Hₙ → 1`.
5. `measurable_cocycle_holonomy_quantized_of_periodic_log` — the assembly.
6. `measurable_cocycle_holonomy_resonant` — the corollary placing `H` in the
   resonance group `resonanceGroupC D.q`.

`L²` translation continuity (`htrans`) is carried as an explicit hypothesis, as
permitted by the certification plan (Mathlib does not yet provide it in the form
needed here); it is **not** introduced as an axiom.
-/
````

### `four time frequency shift/RequestProject/Rotation/HolonomyQuantizationPeriodic(1).lean`

Content ID `a029ad762d2fa845`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L19**

````text
/-!
# Part C: unconditional Stage 3A (modulo the Denjoy–Koksma interface)

We remove the explicit `htrans` (L² translation continuity) and `hRe` (zero real
holonomy mean) hypotheses from Stage 3A, deriving them from periodicity via the
Part A strong-continuity theorem and the Part B zero-mean bridge.

The only remaining conditional input is the existing Denjoy–Koksma /
variation-approximation interface (`DenjoyKoksmaReturnData` and
`TrigApproxInVariation`).
-/
````

### `four time frequency shift/RequestProject/Rotation/MeasurableWinding(1).lean`

Content ID `e0b9f32954da0b78`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L25**

````text
/-!
# Stage 3B: measurable winding obstruction — winding-number wrapper

This module records the winding-number formulation of the measurable winding
obstruction proved (in phase-lift conditional form) in `PhaseLiftWinding`.

For a phase `ψ(x) = b(x)/‖b(x)‖ = exp(2πi (d x + g x))` with `g` `1`-periodic,
the **winding number** of the loop `x ↦ ψ(x)` over one period is exactly the
integer `d`: the periodic remainder `g` contributes nothing to the net winding,
so `wind ψ = d`.  Hence `measurable_cocycle_winding_eq_zero_of_phase_lift`
(which proves `d = 0`) is precisely the statement `wind ψ = 0`.

Mathlib does not currently provide a winding-number API in the exact form needed
to *identify* `wind ψ` with the phase-lift degree `d` directly; that
identification (`wind ψ = d` from the periodic phase lift) is the remaining
adapter, documented here as the next task.  We record the obstruction in
winding-number form below, taking the (geometrically evident) identification
`wind = d` as the explicit interface hypothesis, so that the conclusion
`wind = 0` is available to downstream assembly without any axiom. -/
````

### `four time frequency shift/RequestProject/Rotation/PeriodicKoksma(1).lean`

Content ID `2096dd8e2b584040`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L28**

````text
/-!
# Koksma's inequality and the corrected periodic Denjoy–Koksma estimate

The corrected periodic real Denjoy–Koksma field
`RealDenjoyKoksmaPeriodic.dk_real_periodic` (see
`RequestProject.Rotation.OrbitPartition`) is the classical periodic
Denjoy–Koksma inequality.  Classically it follows from the purely combinatorial
orbit star-discrepancy bound `|#{j<Q : fract(x-jθ) ≤ t} − Q·t| ≤ 1`
(`StandardRealDenjoyKoksmaCombinatorics.star_discrepancy_le_one`) via **Koksma's
inequality**.

This module proves Koksma's inequality (`koksma_real_periodic`), via the
elementary order-statistic / interval-localization argument:

* sort the `Q` fractional parts `y_j = fract(x-jθ)` into `z_0 ≤ … ≤ z_{Q-1}`;
* the discrepancy bound localizes the `k`-th order statistic: `z_k ∈ [k/Q,(k+1)/Q]`;
* on each interval `I_k = [k/Q,(k+1)/Q]`, `|h(z_k) − Q∫_{I_k} h| ≤ Var(h; I_k)`;
* summing and using additivity of the variation over the partition gives the bound.

The result discharges the periodic DK estimate `dk_real_periodic` modulo the
single remaining combinatorial input `StandardRealDenjoyKoksmaCombinatorics`
(the three-gap star-discrepancy bound for continued-fraction denominators), via
the constructor `RealDenjoyKoksmaPeriodic.ofCombinatorics`.
-/
````

### `four time frequency shift/RequestProject/Rotation/UniformReturnSumsPlan(1).lean`

Content ID `342a68e09263d819`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L5–L52**

````text
/-!
# Plan: uniform continued-fraction return sums (Stage 2B, not yet formalized)

This module records the formalization plan for the next stage, building on the
finite Fourier-mode return-sum infrastructure now available in
`RequestProject.Rotation.FourierReturnSums`.  It introduces **no** new axioms,
`sorry`s, or unproven statements: the intended theorem signatures below are
recorded only as comments, to be discharged in a later run.

## What is already available (Stage 2A, proved)

* `CriticalMixedHRT.RotationReturnData θ` — the reusable interface packaging a
  return-time sequence `(qₙ, pₙ)` with `qₙ > 0` and `qₙ θ - pₙ → 0`.
* `CriticalMixedHRT.fourierModeReturnSum_uniform_bound` /
  `fourierModeReturnSum_tendstoUniformly` — for `k ≠ 0`, the single Fourier-mode
  return sum `∑_{j<qₙ} e^{2πi k (x - jθ)}` tends to `0` uniformly in `x`.
* `CriticalMixedHRT.trigPoly_return_uniform_bound` /
  `trigPoly_return_tendstoUniformly` — for a finite mean-zero trigonometric
  polynomial `P(x) = ∑_{k ∈ s} a_k e^{2πi kx}` (`0 ∉ s`),
  `‖∑_{j<qₙ} P(· - jθ)‖∞ → 0`.

## Stage 2B target (Denjoy–Koksma; deferred)

The eventual uniform return-sum theorem for general `C¹` mean-zero functions is:

```text
theorem continued_fraction_return_sum_tendsto_zero_uniformly
    {θ : ℝ} (R : RotationReturnData θ) (hθ : Irrational θ)
    (φ : ℝ → ℂ) (hφ_per : Function.Periodic φ 1)
    (hφ_C1 : ContDiff ℝ 1 φ) (hφ_mean : ∫ x in (0:ℝ)..1, φ x = 0) :
    TendstoUniformly
      (fun n (x : ℝ) => ∑ j ∈ Finset.range (R.q n), φ (x - j * θ))
      (fun _ => (0 : ℂ)) atTop
```

### Intended proof

1. Approximate `φ'` in `L¹(𝕋)` by a mean-zero trigonometric polynomial `R`
   (Fejér / Weierstrass), and let `P` be its mean-zero antiderivative.
2. Apply the **Denjoy–Koksma inequality** to the bounded-variation function
   `φ - P` to bound `‖∑_{j<qₙ} (φ - P)(· - jθ)‖∞` by `2‖φ' - R‖_{L¹}`,
   which is small.
3. Bound `‖∑_{j<qₙ} P(· - jθ)‖∞` by the already-proved finite trigonometric
   polynomial return theorem `trigPoly_return_uniform_bound`.

Denjoy–Koksma itself (step 2) is **not** present in the current Mathlib and is
left to a dedicated future module; nothing in the current build depends on it.
-/
````

### `four time frequency shift/RequestProject/Zak/ConcreteL2ZakModel(1).lean`

Content ID `7e47582f8538ef48`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L12–L45**

````text
/-!
# Stage 6B — concrete covariance data and the isolated `L²` Zak completion gap

The companion modules establish, *concretely and unconditionally* (axioms
`propext, Classical.choice, Quot.sound`), the entire algebraic / analytic content
of the abstract `L2ZakModel` interface, realized on the classical dense test
class via `concreteZakDense`:

* `concreteZakDense_periodic_s`, `concreteZakDense_quasiperiodic_x`,
  `concreteZakDense_lattice_covariance_int`, `concreteZakDense_rogue_covariance_real`
  — the quasiperiodicity and time-frequency covariance fields;
* `finiteSupportZak_plancherel`, `concreteZakDense_plancherel`
  — the orthogonality / Plancherel identity on the dense class;
* `concrete_fiberDensity_integrable`, `concrete_active_set_positive_measure`
  — the Fubini/fibre-density regularity and active-set positivity.

This module collects the covariance fields into a concrete reusable bundle
`concreteZakCovarianceData`, and isolates the single remaining obligation of
`ZAK_MODEL_INTERFACE` as the precise Lean type `StandardL2ZakModelTheorem`.

## What remains

The remaining gap is *not* any of the identities above (all proved); it is the
**Hilbert-space realization**: extending the densely-defined Zak transform from
the dense class of bounded compactly-supported windows to all of
`Lp ℂ 2 volume` as a genuine element of the `L2ZakModel` structure.  The
abstract structure asks for an honest pointwise map `Zak : V → (ℝ → ℝ → ℂ)`
satisfying a pointwise (Riemann-interval) Plancherel identity for *every*
`v : V`.  For genuine `L²` classes the Zak transform is only defined a.e. on
fibres, so realizing the structure requires the standard L²(ℝ) Zak-transform
completion theorem (isometric extension + a.e. fibration), which is not
currently available in Mathlib.  We isolate it as `StandardL2ZakModelTheorem`
and do **not** assert it (no `axiom`).
-/
````

**L85–L91**

````text
/-- **The isolated remaining `ZAK_MODEL_INTERFACE` obligation.**

The single fact still required to make Stage 6B unconditional: the existence of a
genuine `L2ZakModel` on the Hilbert space `L²(ℝ) = Lp ℂ 2 volume`, i.e. the
standard L²(ℝ) Zak-transform completion theorem (isometric extension of the
densely-defined Zak transform with the Plancherel identity).  This is *not* an
axiom; it is a precisely-typed Lean proposition recording the remaining gap. -/
````

**L95–L98**

````text
/-- The remaining gap is *exactly* inhabiting the `L2ZakModel` interface on
`L²(ℝ)`: given the standard completion theorem, a concrete `L2ZakModel` for
`L²(ℝ)` exists.  (Trivial unfolding; recorded to make the reduction target
explicit.) -/
````

### `four time frequency shift/RequestProject/Zak/ConcreteZakAEModel(1).lean`

Content ID `f0e888633e8d2c68`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L10–L37**

````text
/-!
# Stage 6B — the concrete a.e.-level `L²(ℝ)` Zak model (TASKs C/D)

This module assembles the honest a.e.-level Zak model `L2ZakModelAE` on the
concrete Hilbert space `L²(ℝ) = Lp ℂ 2 volume` out of:

* the concrete dense test subspace `concreteZakDenseSubspace` and its density
  `concreteZakDenseSubspace_dense` (TASK B), and
* the general dense-data reduction `l2ZakModelAE_of_dense_data` (proved in
  `ZakTargetSpace.lean`).

The target space is the genuine `L²([0,1]²)` quotient `ZakTarget` (a complete
inner-product space).

The remaining concrete input — the densely-defined Zak isometry on
`concreteZakDenseSubspace` valued in `ZakTarget`, together with the
time-frequency shift operators and the lattice/rogue covariance identities
witnessed on the dense class — is packaged as the structure
`ConcreteZakDenseData`.  Producing such a term is exactly the standard
`L²(ℝ)` Zak-to-`L²([0,1]²)` isometric-lift theorem; it is isolated (NOT as an
axiom) as the precisely-typed proposition `StandardConcreteZakToLpTheorem`.

Given that data, `concrete_L2ZakModelAE_of_data` produces a genuine
`L2ZakModelAE (Lp ℂ 2 volume) ZakTarget` with **no** `sorry` and **no** axiom:
the Plancherel/unitary identity is automatic (the model's Zak transform is a
linear isometry) and the covariance identities are propagated from the dense
class to all of `L²(ℝ)` by `operator_intertwining_extends_from_dense`.
-/
````

**L93–L101**

````text
/-- **The isolated remaining concrete-lift obligation (TASK C).**

The single fact still required to construct the concrete a.e. Zak model: the
existence of the concrete dense Zak isometry data, i.e. the standard isometric
lift of the densely-defined classical Zak transform `concreteZakDense` (on
continuous compactly supported windows) into the `L²([0,1]²)` quotient
`ZakTarget`, with its time-frequency covariance.  This is *not* an axiom; it is a
precisely-typed proposition recording the remaining gap, reduced from the
previous run's `StandardL2ZakModelTheorem`. -/
````

### `four time frequency shift/RequestProject/Zak/ConcreteZakPlancherel(1).lean`

Content ID `0770d6995dcca588`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L9–L29**

````text
/-!
# Stage 6B — orthogonality and the finite-support Plancherel identity

The unitarity of the Zak transform rests on the orthonormality of the integer
Fourier characters `t ↦ e^{-2π i k t}` on the unit interval `[0,1]`.  This module
proves that orthogonality in the self-contained form

* `intervalIntegral_exp_two_pi_int` — `∫₀¹ e^{2π i m t} dt = if m = 0 then 1 else 0`;

and deduces the **finite-support (per-fibre) Plancherel identity**

* `finiteSupportZak_plancherel` —
  `∫₀¹ ‖∑ k ∈ s, c k · e^{-2π i k t}‖² dt = ∑ k ∈ s, ‖c k‖²`

for any finite coefficient family `c : ℤ → ℂ` supported on `s : Finset ℤ`.  This
is exactly the per-fibre Parseval identity for the concrete Zak transform
`concreteZakDense` applied to a window whose integer translates have finite
support; it is the orthogonality core of the full L²(ℝ) Plancherel identity
(`∫₀¹∫₀¹ ‖Zf‖² = ∫_ℝ ‖f‖²`), whose remaining content is the Tonelli swap plus the
decomposition of `∫_ℝ` into integer unit intervals.
-/
````

### `four time frequency shift/RequestProject/Zak/L2Zak(1).lean`

Content ID `2e860cbbdb20f21a`; 2 byte-identical path(s); machine-indexed; substantive review pending.

**L8–L35**

````text
/-!
# Stage 6B (Part A) — the `L²` Zak-transform interface

Mathlib does not (currently) provide the `L²(ℝ)` Zak transform together with its
quasiperiodicity, Plancherel and time-frequency covariance identities.  Rather
than postulate it as a custom `axiom`, this module records it as an **explicit
unitary interface** — a structure `L2ZakModel` over an abstract inner-product
space `V` (the stand-in for `L²(ℝ)`).

A model bundles:

* the Zak transform `Zak : V → (ℝ → ℝ → ℂ)` and the time-frequency shift
  `shift x ω = M_ω T_x = π(x,ω)`;
* `ℂ`-linearity of `Zak` (pointwise on the fibre variables);
* the second-variable `1`-periodicity (`Zak f x (s+1) = Zak f x s`), i.e. the
  Zak quasiperiodicity in the frequency direction;
* the **integer lattice covariance**
  `Zak (shift m n f) x s = e^{-2πi(n x + m s)} · Zak f x s`  (`m n : ℤ`);
* the **rogue (real) covariance**
  `Zak (shift a b f) x s = e^{-2πi b x} · Zak f (x-a) (s+b)`  (`a b : ℝ`);
* the **Plancherel / unitary** identity in the integrated form
  `∫₀¹∫₀¹ ‖Zak f x s‖² dx ds = ‖f‖²`.

All Stage 6B reductions are proved *inside* this interface; the concrete
construction of a model from `Mathlib`'s `L²` API is the remaining external
obligation (documented as such), and is exactly what would make the monolithic
theorem unconditional.
-/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/CrossHalfUniversal.lean`

Content ID `0c87954435a69394`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L39**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Universal cross-half zero-divisor combinatorics for every Cayley–Dickson dimension

The modules `SedenionStratification` (`D = 16`), `Trigintaduonion` (`D = 32`) and
`HigherTower` (`D = 128, 256`) record the cross-half zero-divisor invariants
*dimension by dimension*: the first two by exact evaluation in the algebra, the last one
as hand-checked arithmetic identities about the specific numerals `15624`, `248`, …

This module proves the corresponding statements **once and for all**, for every
Cayley–Dickson dimension `D = 2ⁿ` simultaneously, from the index criterion

  `s • eᵢ + t • e_{H+j}` (with `H = D/2`) is a cross-half zero divisor
  ⟺ `i ≠ 0`, `j ≠ 0`, `i ≠ j`,

which is *kernel-verified in the actual algebra* for `D = 16`
(`crossOctet_annihilator_iff_index`) and `D = 32` (`zd32_iff_index`).

Main results (all for arbitrary `k`, with `H = 2ᵏ` and `D = 2H = 2ᵏ⁺¹`):

* `zdIdx_card` : there are `(H-1)(H-2)` cross-half zero-divisor index pairs, hence
  `zdVerts_card_universal` : `(D-2)(D-4)` signed cross-half zero divisors;
* `nonZD_card_universal` : the remaining cross-half vectors number exactly `6D - 8`;
* `sector_card` : every non-zero XOR charge `χ ∈ 𝔽₂^{n-1} ∖ {0}` carries exactly
  `H - 2` index pairs, i.e. `2(D-4)` signed zero divisors (`sector_verts_card_universal`);
* `charge_count_mul_sector_card` : the `D/2 - 1` non-zero charges times the common
  sector size recovers the total, and `zdIdx_card_eq_sum` proves that the sectors really
  do partition the zero-divisor set;
* `zd_triangular_universal` : `(D-2)(D-4) = 8 · T_{(D-4)/2}` — the eightfold-triangular
  law, for every `D = 2ⁿ` at once;
* `transpose_involutive`, `transpose_ne_self`, `sector_card_even` : the transposition
  `τ : (i,j) ↦ (j,i)` is a fixed-point-free, charge-preserving involution of every sector.

The last section derives the previously hand-written numerical invariants for
`D = 16, 32, 64, 128, 256` as instances of the universal theorems, and links the general
count back to the kernel-verified sedenion and trigintaduonion computations.
-/
````

**L132–L133**

````text
/-- **Universal non-zero-divisor count.** The remaining cross-half vectors — those with
`i = 0`, `j = 0` or `i = j` — number exactly `6D - 8`. -/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/DualUnityBoundaryDefs.lean`

Content ID `68c4004f0995c24a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L62–L63**

````text
/-- Twelve vectors complementary to `kerVecs p`: on a paired index producing a kernel
vector, the opposite sign combination; on the remaining indices, both basis vectors. -/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/LANABicategoryAssociator.lean`

Content ID `4cfdb043f0501ff4`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L29**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Higher-Categorical Bicategory Associator 2-Cell Closure (OP-046, HYP-130)

This module formalizes:
1. The weak higher-categorical bicategory `ℬ_IUTT` of Hodge Theaters:
   - 0-cells: Hodge Theaters `T` carrying base volume.
   - 1-cells: Θ-morphisms `f : T₁ ⟶ T₂` carrying dilation factor `λ(f) > 0`.
   - 2-cells: 2-morphisms / modifications `α : f ⟹ g` carrying norm `‖α‖ ≥ 0`
     and bounding the boundary discrepancy `|λ(f) - λ(g)| ≤ ‖α‖ / 2`.
2. The non-commutative LANA Interim Report Figure 7 diagram:
   - Path 1: Multiradial evaluation across Θ-link (`λ = Δ > 1`).
   - Path 2: Tautological base evaluation (`λ = 1.0`).
   - Theorem: Path 1 ≠ Path 2 in the underlying 1-category.
3. The Sedenion Associator 2-Cell Closure:
   - Norm `‖α_assoc‖ = 2.0`, corresponding to `[e₁, e₂, e₄] = 2 e₇`.
   - Theorem: The associator 2-cell strictly fills the Figure 7 diagram
     for all `Δ ≤ 1 + ‖α_assoc‖ / 2 = 2.0`.
4. The Φ-Surgery Contraction Operator:
   - Contraction factor `κ = 0.64 = 16 / 25 < 1`.
   - Theorem: Φ-surgery strictly resolves Compatibility condition (9-1):
     `λ(S_Φ(Path 2)) < λ(Path 1)` for all `Δ ≥ 1.0`.
5. Mac Lane Pentagon Coherence:
   - Strict pentagon commutativity for composable 1-morphisms.
   - Vanishing of the Cayley–Dickson 3-cocycle coboundary `δω = 0` (product of phases = 1).
6. Complete resolution of Open Problem OP-046.
-/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/SedenionStratification.lean`

Content ID `361ee88394aed72f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L2–L32**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Machine-checked cross-octet stratification of the integer sedenions

The theorems in `Sovereign.Algebra.LeechSedenionFano` and `MonographTheorems` (removed by the 2026 curation)
record the *numerical* content of the monograph (`42 * 4 = 168`, …).  They are true,
but they say nothing about the sedenion algebra itself.

This module states and proves the corresponding *structural* facts about the actual
Cayley–Dickson algebra `CDSedenion = CD (CD (CD (CD ℤ)))`:

* the 256 cross-octet vectors `± e i ± e (8 + j)` are pairwise distinct and non-zero;
* such a vector annihilates another cross-octet vector **iff** `i ≠ 0`, `j ≠ 0`, `i ≠ j`
  (`crossOctet_annihilator_iff_index`);
* exactly 168 of them are zero divisors and exactly 88 are not
  (`crossOctetZD_length`, `crossOctetNonZD_length`);
* the annihilation relation is symmetric, is 8-regular on the 168 zero divisors, and
  therefore has 672 undirected edges;
* annihilation conserves the XOR charge `i ^^^ j`, and the 168 zero divisors split into
  the 7 charge sectors `χ ∈ {1, …, 7}` of 24 vectors each.

That the 88 remaining vectors are not zero divisors *in the whole algebra* (a statement
about infinitely many potential partners, hence not a finite check) is proved separately
in `Sovereign.Algebra.SedenionNonZeroDivisors`.

The finite verifications below are discharged by kernel-external evaluation
(`native_decide`) because they involve tens of thousands of exact integer sedenion
products.
-/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/SubalgebraAssociativity.lean`

Content ID `7389506fd48f9f26`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L28**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Falsification of the 2-Generated Subalgebra Theorem (OP-008, HYP-113)

This module formalizes the negative resolution (falsification) of Open Problem OP-008:
"Prove that every 2-generated subalgebra of every CD tower algebra is associative
(the Artin-style theorem for the tower)."

## Mathematical Foundation:
1. Artin's classical theorem states that an alternative algebra is one where every
   2-generated subalgebra is associative.
2. Cayley-Dickson algebras of dimension D = 2^n ≥ 16 are strictly non-alternative.
3. While any two single basis vectors e_a, e_b span an associative subalgebra (TowerAlternative.lean),
   linear combinations fail to generate associative subalgebras.
4. Concrete Integer Witness in CDSedenion:
   - x = e₁ + e₁₀
   - y = e₄
   - x² = -2 e₀
   - x² · y = -2 e₄
   - x · (x · y) = -2 e₄ - 2 e₁₅
   - [x, x, y] = (x² · y) - x · (x · y) = 2 e₁₅ ≠ 0.
   Therefore, Alg(x, y) contains elements that do not associate, conclusively falsifying
   the conjecture under its explicit falsification protocol:
   "A pair (x, y) generating a non-associative subalgebra."
-/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/TowerAlternative.lean`

Content ID `59c74f978cf76fe5`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L31**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Basis alternativity and the quaternionic subalgebras of the Cayley–Dickson tower

Beyond the octonions no algebra of the Cayley–Dickson tower is alternative.  This module
proves that the failure never happens *on basis vectors*: in every dimension `2ⁿ`

* `assocNeg_left_alt`  : `(e_a e_a) e_b = e_a (e_a e_b)`,
* `assocNeg_right_alt` : `(e_a e_b) e_b = e_a (e_b e_b)`,
* `assocNeg_xor_triple`: `(e_a e_b) e_{a ⊕ b} = e_a (e_b e_{a ⊕ b})`,

and, combining these with flexibility (`assocNeg_self` of `TowerAssociator`),

* `basis_span2_assoc` : *every two-generated index subgroup spans an associative
  subalgebra* — for all indices `x, y, z` in `{0, a, b, a ⊕ b}` the triple
  `(e_x, e_y, e_z)` associates, in every dimension.

The two sign lemmas behind this are `epsNeg_left_shift` and `epsNeg_right_shift`, the two
remaining "shift" laws of the Cayley–Dickson sign function, both derived from the
commutation and cyclic laws of `TowerAssociator`.

A consequence for the zero-divisor geometry is a universal degree bound: for distinct
non-real indices `i ≠ j` at least four middles `k ∈ {0, i, j, i ⊕ j}` associate
(`assoc_middles_four`), so at most `2ⁿ - 4` middles fail to associate
(`nonassoc_middles_card_le`).  Under the identification of annihilation with
non-associativity (`crossSign_eq_assocNeg`) this says that in dimension `D = 2ⁿ⁺¹` no
cross-half zero divisor has more than `D - 8` annihilation partners inside its charge
sector, which is exactly the degree attained by the doubling-pole sectors.
-/
````

### `hankel/output-final_aristotle/Sovereign/Algebra/TowerFlexibility.lean`

Content ID `ecfd3891c6892c6a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L28**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Resolution of Flexibility Beyond Basis Vectors (OP-007, HYP-114)

This module formalizes the affirmative resolution of Open Problem OP-007:
"Is every Cayley–Dickson algebra of the tower flexible on *all* elements, not just basis vectors?"

## Mathematical Framework:
1. An algebra A is flexible if for all x, y ∈ A:
   (x · y) · x = x · (y · x), or equivalently [x, y, x] = 0.
2. In `TowerAssociator.lean`, `basis_flexible` proves that every algebra of the tower
   is flexible on basis vectors: (e_a · e_b) · e_a = e_a · (e_b · e_a).
3. In `TowerCocycle.lean`, `assoc3_conj` and `assocNeg_reverse` establish the reversal
   invariance of the associator:
   conj [x, y, z] = - [conj z, conj y, conj x]
   assocNeg n a b c = assocNeg n c b a.
4. By trilinearity of the associator and polarization:
   [x, y, x] = ∑_a x_a² y_b [e_a, e_b, e_a] + ∑_{a < c} x_a x_c y_b ([e_a, e_b, e_c] + [e_c, e_b, e_a]).
   Since [e_a, e_b, e_a] = 0 and [e_a, e_b, e_c] + [e_c, e_b, e_a] = 0 identically,
   the associator [x, y, x] vanishes for all elements x, y.
5. In particular, linear combinations that strictly fail alternativity (such as the OP-008
   witness x = e₁ + e₁₀, y = e₄ where [x, x, y] = 2 e₁₅ ≠ 0) nevertheless strictly
   satisfy the flexibility identity:
   (x · y) · x = x · (y · x).
-/
````

### `hankel/output-final_aristotle/Sovereign/Combinatorics/TowerSectorProfile.lean`

Content ID `8d978151e7e919b8`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L35**

````text
/-
Copyright (c) 2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The non-recursive profile of a charge-sector census (evidence layer)

`TowerSectorCensusClosedForm` determines the census of every charge sector by the recursion
`sectorClosed`, and `TowerSectorCensusClasses` shows that the census depends on the charge
only through the descent word `sectorKey n chi`.  Reading that descent as a *fold of affine
maps* over the bits of the word removes the recursion on the census entirely:

* `sectorStep m b` — one descent step at level `m`: `v ↦ 2v + 4` on a low bit and
  `v ↦ 2ᵐ⁺¹ - (2v + 4)` on a high bit;
* `sectorPush` — the image of a degree under a list of steps;
* `sectorProfile n w v` — the conjectured census of the class `w`: one *main* family, the
  image of the octonionic degree `4` under all `n - 3` steps with multiplicity `6 · 2^(n-3)`,
  together with one contribution per step `t`, the image of the level-`(t+4)` top degree
  `2^(t+4) - 4` under the remaining steps, with multiplicity `2^(n-3-t)`.

**Open target** (item R1 of `RESEARCH_ROADMAP_NEXT.md`):

```
theorem sectorCount_eq_sectorProfile (n chi v : Nat) (hn : 3 ≤ n) (hchi0 : chi ≠ 0)
    (hchi : chi < 2 ^ n) : sectorCount n chi v = sectorProfile n (sectorKey n chi) v
```

This module does **not** prove that statement.  It proves it as an *instance* in the first
four dimensions of the tower, by kernel evaluation against the proved determination theorem
`sectorCount_eq_sectorClosed`:

* `sectorCount_eq_sectorProfile_dim16`, `…_dim32`, `…_dim64`, `…_dim128`.

The evaluation is exhaustive in both the charge and the degree, so each of these is the full
statement of the conjecture in that dimension; what is missing is the induction on the level.
-/
````

**L57–L60**

````text
/-- The conjectured non-recursive census of the sector class `w` in dimension `2ⁿ`: the main
family of `6 · 2^(n-3)` pairs carried by the image of the octonionic degree `4`, plus, for
each step `t` of the descent, `2^(n-3-t)` pairs carried by the image of the level-`(t+4)` top
degree under the remaining steps. -/
````

### `hankel/output-final_aristotle/Sovereign/Fluid/GlobalRegularity.lean`

Content ID `8f8964f57f6a7ec5`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L125–L128**

````text
/-- Theorem 1.6 (Cauchy Forward Trajectory Zero-Divisor Preservation):
    If the temporal evolution preserves the zero-divisor cross product subspace,
    an initial zero-divisor state u0 x_16 omega0 = 0 remains a zero-divisor state
    for all future times t. -/
````

### `hankel/output-final_aristotle/Sovereign/Fluid/UniversalRegularity.lean`

Content ID `d9c84e2058222feb`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L25**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Universal Regularity vs. Biregularity Classification across the Cayley–Dickson Tower (OP-003, HYP-112)

This module formalizes the resolution of Open Problem OP-003:
"Prove HYP-070's criterion (χ < 8 or χ = 2^k) for all D = 2^n ≥ 16, not just D ∈ {16, 32}."

## Mathematical Foundation:
1. **Universal Regularity Criterion**:
   For every Cayley-Dickson dimension D = 2^n ≥ 16, a charge sector χ ∈ {1, ..., D/2 - 1}
   is (D - 8)-regular if and only if:
       χ < 8  ∨  ∃ k ≥ 3, χ = 2^k.
   The number of regular sectors in dimension D = 2^n is identically n + 3.

2. **Biregularity Refinement & Multiregularity Emergence**:
   The naive assumption that non-regular sectors are "biregular otherwise" holds only in D = 32.
   In D ≥ 64 (n ≥ 6), multiregular sectors with 3 or more degree levels emerge strictly.
   - Biregular sectors: exactly 7(n - 4) + (n - 4)(n - 5) / 2 sectors.
   - Multiregular sectors: (2^(n - 1) - 1) - (n + 3) - [7(n - 4) + (n - 4)(n - 5)/2] sectors.
   At D = 64 (n = 6), multiregularSectorCount 6 = 7 > 0, formally settling the biregular-otherwise
   conjecture and establishing the exact universal tripartite partition.
-/
````

### `hankel/output-final_aristotle/Sovereign/Geometry/ArnoldCurvatureReduction.lean`

Content ID `f7c2fc1415123716`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L44**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Formalization of Infinite-Dimensional Arnold Curvature Reduction (OP-033, HYP-129)

This module formally settles Open Problem OP-033 (Level L3, Domain 4: Non-Associative Hydrodynamics & PDE):
"Kernel-formalize in Lean 4 the momentum map reduction μ: sdiff(M)* → g_2* and the sectional curvature formula
yielding 0 ≤ K ≤ 5/4 on V_2(ℝ^7)."

## Key Theorems Formally Certified:
1. Infinite-Dimensional Fluid Algebra sdiff(M) and Momentum Map:
   - SDiff(M) is the infinite-dimensional Lie group of volume-preserving diffeomorphisms.
   - Dual space sdiff(M)* comprises fluid vorticity fields ω.
   - The momentum map μ: sdiff(M)* → g_2* projects vorticity onto the 14D Lie algebra g_2.
   - The coadjoint quotient by SU(2) is the 11-dimensional Stiefel manifold V_2(ℝ^7) ≅ G_2 / SU(2).

2. Dimension and Tangent Bundle Decomposition of V_2(ℝ^7):
   - dim V_2(ℝ^7) = 2 * 7 - 3 = 11.
   - Vertical tangent space V_P ≅ so(2) has dimension 1.
   - Horizontal tangent space H_P has dimension 2 * (7 - 2) = 10.
   - Exact sum: dim V_P + dim H_P = 1 + 10 = 11.

3. Canonical Riemannian Sectional Curvature Formula on V_2(ℝ^7):
   - For an orthonormal 2-plane in T_P V_2(ℝ^7) spanned by tangent vectors X, Y:
     - Vertical components: A_X, A_Y ∈ so(2).
     - Horizontal components: K_X, K_Y.
     - Vertical bracket term: T_1 = (1/4) ‖[A_X, A_Y]‖² ≥ 0.
     - Horizontal-vertical cross term: T_2 = ‖(1/2)(K_X A_Y - K_Y A_X) + P · skew‖² ≥ 0.
     - Grassmannian term: T_3 = -K_Gr ≥ 0.
   - Total sectional curvature: K(X, Y) = T_1 + T_2 + T_3 ≥ 0.
   - Universal canonical bounds: 0 ≤ K ≤ 5/4 (in scaled integer units: 0 ≤ 4 * K ≤ 5).

4. Curvature Transition Jump and Geodesic Conjugate Point Bound:
   - Bulk Arnold curvature: K_bulk < 0 (divergence / Lagrangian turbulence).
   - Boundary Stiefel curvature: 0 ≤ K_boundary ≤ 5/4 (elliptic focusing).
   - Strict jump: 4 * K_bulk < 4 * K_boundary across the transition threshold.
   - Universal first conjugate point focusing time: t_conj ≥ 2π / √5.

5. Refutation of OP-033 Falsification Criterion:
   - Since K(X, Y) = T_1 + T_2 + T_3 is a sum of non-negative squares, K(X, Y) ≥ 0 for every 2-plane.
   - It is impossible for any 2-plane in V_2(ℝ^7) to have negative sectional curvature (K < 0).
-/
````

**L184–L188**

````text
/-- Full Formal Resolution of Open Problem OP-033:
    The momentum map reduction quotient matches dim V_2(ℝ^7) = 11,
    the tangent bundle splits as 1 + 10 = 11,
    sectional curvature is unconditionally non-negative and bounded by 5/4,
    and negative sectional curvature is impossible. -/
````

### `hankel/output-final_aristotle/Sovereign/Graph/GeodesicFlowObstruction.lean`

Content ID `e3e5afc795b8e3a2`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L23**

````text
/-
Copyright (c) 2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discrete Geodesic Flow Center Subspace & Anosov Obstruction (OP-040 / HYP-106)

This module formalizes the negative settlement (falsification) of Open Problem OP-040:
"Compute the Lyapunov spectrum of the discrete geodesic flow on the Ramanujan graph
 Γ = C_6[bar{K_4}] and verify whether it satisfies the Anosov property."
Falsification criterion: "A zero Lyapunov exponent on the discrete phase space."

Mathematical Content:
1. The discrete phase space \vec{E} has dimension 2|E| = 192 directed edges.
2. By the Ihara-Bass formula, the cycle space H_1(Gamma, R) has dimension b_1 = |E| - |V| = 72,
   producing (1 - u^2)^72 in the characteristic polynomial of the Hashimoto matrix B.
3. Including the two bipartite trivial cycle roots (mu = \pm 1), exactly 146 eigenvalues
   satisfy |mu| = 1, inducing 146 identically zero Lyapunov exponents:
     lambda = ln(|mu|) = ln(1) = 0.
4. The 146 zero Lyapunov exponents span 76.04% of the discrete phase space (E^c),
   rigorously obstructing uniform hyperbolicity and falsifying the Anosov property.
5. On the full 168-vertex graph, the 7 isolated charge sectors make the global flow non-ergodic.
6. On the quotient graph C_6, all 12 Lyapunov exponents are identically zero (deterministic rotation).
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/NonPoleIntegrality.lean`

Content ID `565369daf337e16d`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L22**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Algebraic Integrality of the Non-Pole Zero-Divisor Spectrum (OP-002, HYP-111)

This module formalizes the affirmative resolution of Open Problem OP-002:
"Prove that every eigenvalue of every non-pole sector at every tower level
D = 2^n is an algebraic integer."

## Mathematical Foundation:
1. For any Cayley-Dickson dimension D = 2^n ≥ 16 and any charge sector χ ∈ {1, ..., D/2 - 1},
   the annihilation subgraph G_{D, χ} has vertex order N = 2(D - 4).
2. Its adjacency operator A_{D, χ} is a symmetric matrix over ℤ with entries in {0, 1}.
3. The characteristic polynomial P_{D, χ}(x) = det(x · I - A_{D, χ}) is monic with integer coefficients
   (P_{D, χ} ∈ ℤ[x]).
4. Consequently, every eigenvalue λ in any extension ring K is integral over ℤ (`IsIntegral ℤ λ`).
5. Every eigenvalue is algebraic over ℤ (`IsAlgebraic ℤ λ`), strictly precluding transcendental eigenvalues.
6. By the integral closure of ℤ in ℚ, every rational eigenvalue is a rational integer,
   precluding non-integral fractional eigenvalues.
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/RegularSubfamilies.lean`

Content ID `a40846f101834d27`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L33**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Persistent Regular Sub-Families Across the Cayley–Dickson Tower (OP-012, HYP-115)

This module formalizes the affirmative resolution of Open Problem OP-012:
"HYP-074 proves the annihilation graph is regular iff D = 16. Does any *sub*-family
(e.g., pole sectors, quaternionic pairs) remain regular for all D?"

## Mathematical Framework:
1. Global Irregularity: HYP-074 establishes that the total annihilation graph
   is regular if and only if D = 16. At D ≥ 32, vertex degrees vary.
2. Persistent Regular Sub-Families:
   Despite global irregularity, two infinite sub-families remain strictly regular
   with degree identically equal to D - 8 across all D = 2^n ≥ 16:
   (a) The Octonionic Sub-Family:
       S_oct = {χ ∈ ℕ | 1 ≤ χ ≤ 7}.
       For all χ ∈ S_oct and all D = 2^n ≥ 16, χ < 8 satisfies the universal regularity
       criterion (HYP-112).
   (b) The Doubling Pole Sub-Family:
       S_pole(n) = {2^k | 3 ≤ k ≤ n - 2}.
       Every doubling pole (including the principal pole χ = D/4 = 2^(n-2)) satisfies
       the 2^k power-of-two criterion and remains strictly (D-8)-regular.
3. Sector Cardinality Scaling:
   The total number of persistent regular sectors is:
       |S_oct| + |S_pole(n)| = 7 + (n - 4) = n + 3 = log₂(D) + 3.
4. Falsification Protocol:
   A sub-family claimed regular that becomes irregular at some D.
   We prove that for all n ≥ 4 and all χ ∈ S_oct ∪ S_pole(n), χ satisfies the regularity
   criterion unconditionally, with 0 falsifying dimensions.
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/SectorCellStructure.lean`

Content ID `a708db999ce2cad2`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L20**

````text
/-
Copyright (c) 2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twin-star structure of the cell graph, in every dimension

For the algebra of dimension `2ⁿ⁺²` (level `n + 1` of the cell signs, `M = 2ⁿ`) and a charge
`χ ≠ M`, put `τ = M` if `χ < M` and `τ = χ ⊕ M` otherwise.  This module proves, **for every
`n`**, that the cell adjacency bit `cellAdj (n+1) χ` has the following shape:

* **universal cell** — `τ` interacts with every other cell;
* **closed twins** — every other cell `r` interacts with `r ⊕ τ`, and `r`, `r ⊕ τ` interact with
  exactly the same remaining cells;

and that for `χ = M` all distinct cells interact.

Everything is reduced, through the doubling recursion of `epsNeg`, to the commutation law
`epsNeg_xor_swap` and the cyclic law `epsNeg_cyclic` one level down; no finite computation is
involved.
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/SectorGraphInvariants.lean`

Content ID `a8bcdeb6c2d89168`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L21**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Sector-Level Graph Invariants Across the Doubling Tower (Target R6)
  **Epistemic Classification:** [A] Spectral Graph Theory & Structural Graph Invariants

This module establishes the exact structural invariants of the charge-sector
subgraphs of the annihilation graph, fulfilling Target R6 of the research roadmap:

* `sector_pair_count` — every non-zero charge sector $\chi$ carries exactly
  $2^n - 2$ admissible index pairs in dimension $2^n$;
* `sectorVertexCount` — every non-zero charge sector has $4(2^n - 2) = 2^{n+2} - 8$ vertices;
* `regular_sector_vertex_crossDegree` — in any regular sector (where $\text{sectorKey } n\ \chi = 0$),
  every admissible vertex has maximal degree $2^{n+1} - 8$;
* `regularSectorTotalDegree` — the sum of vertex degrees in a regular sector is
  $4(2^n - 2)(2^{n+1} - 8)$;
* `regularSector_edge_count_handshake` — by the handshake lemma, the exact edge count
  of a regular sector graph is $4(2^n - 2)(2^n - 4)$.
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/SpectralFieldStabilization.lean`

Content ID `9b1b8bdb4629db6a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L35**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Spectral Number Field Stabilization across Cayley-Dickson Doubling Tower (HYP-145, Settles OP-026)
  **Epistemic Classification:** [A] Algebraic & Number-Theoretic Identities

This module formally settles Open Problem OP-026 on the algebraic number field
extensions generated by regular sector quotient spectra in high dimensions.

Key Theorems Formally Certified:
1. Dimension D = 64 (Chingon) Regular Sector Discriminant:
   The characteristic polynomial has irreducible quadratic factor:
     P_64(x) = x^2 + 4x - 224.
   Discriminant: Δ_64 = 4^2 - 4 * 1 * (-224) = 16 + 896 = 912 = 16 * 57.
   Roots: x = -2 ± 4 * √57.
   Splitting field: ℚ(√57).

2. Dimension D = 128 (Universal CD) Regular Sector Discriminant:
   The characteristic polynomial has irreducible quadratic factor:
     P_128(x) = x^2 - 912.
   Discriminant: Δ_128 = 0^2 - 4 * 1 * (-912) = 3648 = 64 * 57.
   Roots: x = ± 4 * √57.
   Splitting field: ℚ(√57).

3. Quadratic Field Isomorphism & Invariant Square-Free Discriminant:
   The square-free kernel of both discriminants is identical:
     sqFreePart(912) = 57,
     sqFreePart(3648) = 57.
   Since 57 = 3 * 19 is square-free, the splitting fields ℚ(√912) and ℚ(√3648)
   are canonically isomorphic to the real quadratic field ℚ(√57).
   Thus, the spectral number field does NOT grow in degree, but stabilizes
   at ℚ(√57).
-/
````

### `hankel/output-final_aristotle/Sovereign/Graph/ZeroDivisorModularKernel.lean`

Content ID `122cb3a05c88a78f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L38**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Formal Proof of Sedenion Zero-Divisor Modular Kernel & Non-Invertibility (HYP-125, OP-052)

This module formally settles Open Problem OP-052 (Level L3, Domain 6: Cryptography &
Post-Quantum Security):

1. Sedenion Coordinate Extraction:
   - Component projection `sedCoord` mapping `CDSedenion` to 16 integer coordinates.
   - Exact basis projection and isolation on low-octet coordinates.

2. Explicit Kernel Vector Construction:
   - For any cross-octet zero divisor V with indices `vi, vj` and signs `s1, s2`:
     `kerTestVec vi vj a = e a + e (8 + (a ^^^ vi ^^^ vj))` for `a ∈ {0, ..., 7}`.
   - Coordinate isolation: for all `m < 8`, `sedCoord (kerTestVec vi vj a) m = if a = m then 1 else 0`.
   - Linear independence over 𝔽₂: the projection of `{kerTestVec 0, ..., kerTestVec 7}` onto the
     first 8 coordinates is the 8×8 identity matrix I₈.

3. Universal Modulo 2 Kernel Vanishing:
   - For all 168 zero divisors V ∈ crossOctetZD and all 8 basis index offsets `a < 8`:
     every coordinate of `V * kerTestVec vi vj a` is an even integer:
     `sedCoord (V * kerTestVec vi vj a) m % 2 = 0` for all `m < 16`.
   - Modulo 2 kernel dimension is at least 8 (nullity ≥ 8 over 𝔽₂).

4. Modulo 2¹⁶ Modular Kernel Vanishing:
   - Scaled 2-torsion kernel vectors: `kerTestVecMod vi vj a = smulSed (2¹⁵) (kerTestVec vi vj a)`.
   - Every coordinate of `V * kerTestVecMod vi vj a` is a multiple of 2¹⁶ = 65536:
     `sedCoord (V * kerTestVecMod vi vj a) m % 65536 = 0` for all `m < 16`.
   - Non-triviality: coordinate `a` is 32768 ≠ 0 (mod 65536), so the vectors are strictly non-zero mod 2¹⁶.

5. Unconditional Non-Invertibility:
   - Because `V * X ≡ 0 (mod 2¹⁶)` for non-zero `X = kerTestVecMod vi vj 0`, no linear map or inverse
     permutation W can recover X from 0: `W(0) = 0 ≠ X (mod 2¹⁶)`.
   - Refutation of OP-052 falsification condition: zero-divisor multiplications are unconditionally
     non-invertible over ℤ_{2¹⁶}¹⁶.
-/
````

### `hankel/output-final_aristotle/Sovereign/Meta/MillenniumImpactAudit.lean`

Content ID `67ba5162e35b80ff`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L12–L68**

````text
/-!
# What the Stiefel/cubature theorems do — and do not — change for the Clay problems

The latest batch of results in this development
(`StiefelSpectrumStrong`, `StiefelFrameCensus`, `StiefelCubature`) consists of

* arithmetic laws for the `G₂` Weyl dimension, the `SU(2)`-singlet multiplicity and the
  Casimir eigenvalue on `V₂(ℝ⁷) ≅ G₂/SU(2)`,
* the census of the 168 sedenion cross-octet zero-divisor 2-frames, and
* the exact cubature identity `Mᵀ M = 24 · I₂₁` together with the diagonalisation of the
  projected annihilation operator, whose spectrum is `{-8 (×7), 0 (×14)}`.

This module answers, formally, the question of what those theorems do to the Clay
Millennium problems.  It has three parts.

## 1. The logical audit

`implication_from_theorem_iff`: if `p` is already a theorem, then `(p → q) ↔ q`.  So a
"reduction" of any open problem `C` to one of the finished theorems above is *logically
identical to `C` itself*: it transports no difficulty.  The instances
`cubature_reduction_iff`, `frame_census_reduction_iff`, `spectral_coincidence_reduction_iff`
and `stiefel_to_riemann_iff` record this for the concrete theorems and, in the last case,
for the Riemann hypothesis as stated here (`RiemannHypothesisStatement`).  Each of the
three theorems is moreover a statement about a *finite* object (a fixed 168 × 21 integer
matrix, a fixed 168-element list) or about an explicit quadratic form in two natural
numbers, so nothing in them is even expressible in the analytic vocabulary of the Clay
problems.

## 2. Why the "mass gap" of the discrete model is not a mass gap

The one number in the new batch that has the shape of a Clay-type statement is the
spectral gap `-8` of the projected annihilation operator.  Here it is explained away:

* `annihilation_bipartite`: the annihilation graph on the 168 zero divisors is **bipartite**,
  the two sides being the two values of the cross-product harmonic sign
  `crossSign (i, j, s, t) = s · t · sign(eᵢ × eⱼ)`.
* `sector_sign_eigenvector`: consequently each of the seven charge sectors contributes a
  `±1` eigenvector of the adjacency operator with eigenvalue exactly `-8`, and these are
  the seven cross-product directions that `StiefelCubature.projected_adjacency` sees.
* `abs_eigenvalue_le_row_bound` and `annihilation_eigenvalue_abs_le_eight`: `8` is the
  *a priori* bound for the modulus of any eigenvalue of an `8`-regular graph.

So `-8` is the extremal value permitted by regularity, attained for the trivial reason
that a `ℤ/2` sign symmetry makes the graph bipartite (`annihilation_gap_is_extremal`).  A
gap forced by bipartiteness carries no dynamical information, which is exactly the
difference between it and the Yang–Mills mass gap.

## 3. The one genuine bridge: the lowest continuum eigenspace

`stiefel_spectral_gap` and `stiefel_gap_attained_iff`: the smallest non-zero Casimir
eigenvalue on `V₂(ℝ⁷)` is `6`, attained only at the highest weight `(1,0)`, and
`lowest_eigenspace_dim_eq_21` its eigenspace has dimension
`g2_dim 1 0 · su2_singlet_mult 1 0 = 7 · 3 = 21` — precisely the number of harmonics that
the 168 discrete frames integrate exactly (`harmonic_dimension`).  This is a statement
about a compact 11-manifold and a finite graph; it is not a statement about the
Navier–Stokes equations on `ℝ³`, and no claim to the contrary is made here.
-/
````

### `hankel/output-final_aristotle/Sovereign/Meta/ReasoningStoreAudit.lean`

Content ID `88e35181baae2c8f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L92–L95**

````text
/-! The one remaining emitted certificate — the sedenion annihilation
`(e₁ + e₁₀)(e₄ − e₁₅) = 0` — is the only one that mentions the algebra at all; it lives in
`ReasoningStoreAuditSedenion` (its `MonographTheorems` dependency cannot be imported
alongside `AutonomousDiscovery`, see the note there). -/
````

### `hankel/output-final_aristotle/Sovereign/Meta/SkeletonEngineCore.lean`

Content ID `efebe84076e2ec5a`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L144–L148**

````text
/--
`decompose done todo goal` is the list of leaf obligations obtained by exhaustively
applying invertible structural rules.  `done` holds hypotheses already inspected (atoms
and implications), `todo` holds hypotheses still to inspect.
-/
````

### `hankel/output-final_aristotle/Sovereign/Meta/StateOfThoughtStopping.lean`

Content ID `68f6f6b44e3b9fce`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L19**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The windowed stopping rule as a counter automaton

Roadmap item 2.2 of `docs/STATE_OF_THOUGHT_ROADMAP.md`. The training-free stopping rule
`tfStop` of the appendix fires at step `t` when over the last `r` steps the entropy and the
velocity stay below their thresholds and the consistency is positive.

* `tfStop_mono_threshold` : the rule is monotone in both thresholds;
* `runLen` : a one-counter automaton reading the feature stream (length of the current run of
  "good" steps);
* `tfStop_iff_runLen` : the rule fires at `t` iff `min r (t + 1) ≤ runLen t`, so it can be
  evaluated online with a single counter instead of a window buffer;
* `tfStop_of_good_from` : if the conditions hold at every step from `t₀` on, the rule fires
  at step `t₀ + r − 1`, i.e. within `r − 1` steps (bounded latency);
* `tfStop_not_of_bad` : conversely it never fires while the current step is bad.
-/
````

### `hankel/output-final_aristotle/Sovereign/Meta/TopologicalEntropyBarrier.lean`

Content ID `045120a22166a7ba`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L178–L184**

````text
/-- Master Theorem: Persistent topological Shannon entropy S_top ≥ 0.80 bits is an exact
    necessary and sufficient condition to prevent collapse into degenerate trivial tautologies
    during autonomous theorem generation.
    - Necessary: S_top < 0.50 bits collapses with probability > 1 - 2^{-3000}.
    - Sufficient: S_top*(1/4) > 0.80 bits ensures exploration of non-contractible 1-cycles (H₁ ≥ 1)
      in the MANIFOLD_STABLE regime.
    - Settles Open Problem OP-063. -/
````

### `hankel/output-final_aristotle/Sovereign/NumberTheory/BakerLatticeBound.lean`

Content ID `96051e8a48d2beaa`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L18**

````text
/-
  Sovereign Formal Verification Library
  Module: Sovereign.BakerLatticeBound
  Open Problem: OP-047 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-146 (Effective Baker-Type Lower Bounds from Leech Lattice and Cayley–Dickson Twisted-XOR Embeddings)

  This module formalizes:
  1. The Leech lattice Lambda_24 geometric invariants:
       - Dimension = 24.
       - Minimal squared Euclidean norm = 4.
       - Minimal vector length = 2.
       - Kissing number = 196,560.
  2. The discrete Phi-surgery logarithmic quantum:
       - Delta_log = ln(25/16) = 2 * ln(5/4) > 0.
  3. The geometric Baker-type lower bound on linear forms in logarithms:
       - |Lambda| >= (2 * Delta_log) / (||b||^n + 1).
  4. The master resolution theorem for OP-047.
-/
````

### `hankel/output-final_aristotle/Sovereign/NumberTheory/EffectiveABCConstant.lean`

Content ID `a99dc91ec57fae05`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L15**

````text
/-
  Sovereign Formal Verification Library
  Module: Sovereign.EffectiveABCConstant
  Open Problem: OP-042 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-153 (Effective Uniform Constant C_ε for Masser–Oesterlé ABC Conjecture)

  This module formalizes:
  1. The explicit, computable uniform ABC constant:
       C_ε = exp(K_leech / ε)
     where K_leech = (25 / 16) / ln(25 / 16) ≈ 3.5011 is determined by the
     minimax Φ-surgery contraction factor κ = 16/25 and the Leech minimal norm.
  2. Strict positivity and monotonicity of C_ε for all ε > 0.
  3. Boundedness on extremal ABC hits, including the Reyssat triple (q ≈ 1.6299).
  4. The master resolution theorem settling OP-042.
-/
````

### `hankel/output-final_aristotle/Sovereign/NumberTheory/HallsConjectureReduction.lean`

Content ID `90cbec3cc77c84ea`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L18**

````text
/-
  Sovereign Formal Verification Library
  Module: Sovereign.HallsConjectureReduction
  Open Problem: OP-049 (Level L1, Domain 5: Number Theory & ABC/IUTT)
  Hypothesis: HYP-145 (Hall's Conjecture Exponent Reduction from ABC and Davenport Polynomial Sharpness)

  This module formalizes:
  1. The formulation of Marshall Hall's Conjecture (1970) and Weak Hall's Conjecture:
       |x^3 - y^2| >= C_eps * x^(1/2 - eps) for all non-trivial integer solutions.
  2. The exact mathematical reduction showing that the Masser–Oesterlé ABC conjecture
     implies the Weak Hall bound with explicit exponent delta = 3 * eps_0 / (1 + eps_0).
  3. Davenport's Theorem (1965) and Mason–Stothers polynomial ABC theorem:
       deg(g^2 - f^3) >= (1/2) * deg(f) + 1
     with certified sharpness on the Davenport witness (f = t^2 + 2, g = t^3 + 3t).
  4. Kernel-checked arithmetic verification of Noam Elkies' 1998 world-record near-miss:
       x = 5853886516781223, y = 447884928428402042307918
       |y^2 - x^3| = 1641843.
-/
````

### `hankel/output-final_aristotle/Sovereign/Physics/AlbertF4Obstruction.lean`

Content ID `a1a0637fc27d472f`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L27**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exceptional Lie Algebra 𝔣₄ & Albert Algebra Non-Embedding Obstruction (OP-057, HYP-132)

This module formalizes:
1. The dimensional structure of the exceptional Lie algebra 𝔣₄ = Der(𝔥₃(𝕆)) (dim 52),
   the Albert exceptional Jordan algebra 𝔥₃(𝕆) (dim 27), and the general linear
   endomorphism algebra 𝔤𝔩(7, ℝ) of the 7 biregular sectors (dim 49).
2. The Dimensional Obstruction Theorem:
   dim(𝔤𝔩(7)) = 49 < 52 = dim(𝔣₄), mathematically prohibiting any injective linear map,
   subalgebra embedding, or injective Lie algebra homomorphism 𝔣₄ ↪ 𝔤𝔩(7).
3. The Simplicity and Kernel Collapse Theorem:
   Because 𝔣₄ is a simple Lie algebra (having no non-trivial proper ideals),
   any Lie algebra homomorphism ϕ : 𝔣₄ → 𝔤𝔩(7) must have dim(im(ϕ)) ∈ {0, 52}.
   Since dim(im(ϕ)) ≤ 49 < 52, it is impossible for dim(im(ϕ)) = 52.
   Therefore dim(im(ϕ)) = 0, proving that every homomorphism ϕ : 𝔣₄ → 𝔤𝔩(7) is identically zero.
4. The Minimal Representation Dimension Obstruction:
   The minimal non-trivial representation dimension of 𝔣₄ is d_min = 26.
   Since the sector space dimension is 7 < 26 (a gap of 19 dimensions),
   no non-trivial linear action of 𝔣₄ on the 7 sectors exists.
5. The Discrete Klein Quadric Sector Automorphism Group:
   The sector automorphism group Aut(Sectors₇) ≅ PSL(2, 7) has finite order 168
   and 0-dimensional Lie algebra, strictly excluding any continuous Lie symmetry.
6. Complete formal settlement of Open Problem OP-057 in the negative (FALSIFIED).
-/
````

### `hankel/output-final_aristotle/Sovereign/Physics/ChiralAnomalyCancellation.lean`

Content ID `7bd6e95ea4f48de1`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L17**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gravitational & Gauge Chiral Anomaly Cancellation (OP-060, HYP-131)

This module formalizes:
1. The chiral grading and index on the 21 generational blocks of the 32D zero-divisor manifold.
2. In each generational block of 16 fermion vertices, exactly 8 are Left-Handed (8_L)
   and 8 are Right-Handed (8_R), forming two disjoint K_{4,4} bipartite subgraphs.
3. The local chiral index tr(γ₅) = 8_L - 8_R = 0 vanishes identically in every block.
4. Complete local gravitational anomaly cancellation: A_grav = tr(γ₅) = 0.
5. Global anomaly cancellation across all 21 generational blocks: ∑ tr(γ₅) = 21 · 0 = 0.
6. Universal parity theorem: the anomaly coefficient is strictly even (identically zero),
   unconditionally refuting the existence of any odd chiral anomaly coefficient.
7. Complete formal settlement of Open Problem OP-060.
-/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/AssociatorSubsystemCode.lean`

Content ID `5b992bcc7b98dcb7`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L170–L174**

````text
/-- Master Theorem settling Open Problem OP-025:
    Synthesizes a family of subsystem quantum codes [[L², 1, (L-1)², L]] where
    gauge generators correspond to associator 2-cells, stabilizers are generated
    by closed associator cycles, the Hilbert space decomposes as k + r + s = n,
    and k = 1 logical qubits are preserved for all L ≥ 2. -/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/ExpanderHashCollisionBound.lean`

Content ID `97da61037c85d1d6`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L39**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expander-Based Hash Collision Lower Bound & Birthday Resistance (HYP-126, OP-020)

This module formally settles Open Problem OP-020 (Level L3, Domain 2: Spectral Graph Theory & Expanders):

1. Ramanujan Expander Rapid Mixing & Spectral Ratio:
   - Degree d = 8, second eigenvalue λ₂ = 4.
   - Strict Ramanujan optimality: λ₂ = 4 < 2√7 ≈ 5.2915 (λ₂² = 16 < 4(d - 1) = 28).
   - Spectral contraction ratio ρ = λ₂ / d = 1 / 2.
   - Rapid mixing decay after 24 rounds: ρ²⁴ = (1/2)²⁴ = 1 / 16,777,216.

2. Classical Birthday Collision Lower Bound:
   - For a hash function with output space size S = 2ᵇ (b bits of output):
     The collision probability of Q queries is bounded by the union bound over pairs:
     P_coll(Q) ≤ Q(Q - 1) / (2 * 2ᵇ).
   - Therefore, to achieve collision probability P_coll(Q) ≥ 1/2, the number of queries
     must satisfy Q(Q - 1) ≥ 2ᵇ.
   - This strictly implies Q² > 2ᵇ, which entails Q > 2^(b / 2).
   - Thus, any algorithm achieving P_coll ≥ 1/2 requires at least Q ≥ 2^(b / 2) queries,
     matching the birthday bound Ω(2^(b / 2)).

3. Canonical Parameters & Exact Query Bounds:
   - b = 64:  Q > 2³² = 4,294,967,296.
   - b = 128: Q > 2⁶⁴ = 18,446,744,073,709,551,616.
   - b = 256: Q > 2¹²⁸.

4. Non-Associative Meet-in-the-Middle (MITM) Obstruction:
   - Sedenion non-associativity: (e₁ * e₂) * e₄ ≠ e₁ * (e₂ * e₄).
   - Zero-divisor non-invertibility: det(M(V)) = 0, nullity ≥ 8, ker ≥ 2⁶⁸.
   - Bidirectional MITM trees of depth m / 2 cannot be joined or inverted.

5. Refutation of OP-020 Falsification Criterion:
   - A collision-finding algorithm beating the bound (i.e. finding a collision with
     probability ≥ 1/2 using Q ≤ 2^(b / 2) queries under uniform mixing) is mathematically
     impossible.
-/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/FanoMagicStateDistillation.lean`

Content ID `817186e796eb41e9`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L29**

````text
/-
Copyright (c) 2024-2026 Sovereign Engine Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Magic State Distillation Overhead on Fano [24,4,8] Octad Codes (HYP-127, OP-027)

This module formally settles Open Problem OP-027 (Level L3, Domain 3: Quantum Error Correction & CSS Codes):

1. Code Parameters & Weight Distribution:
   - Block length n = 24, logical dimension k = 4, minimum distance d = 8.
   - Check matrix rank: n - k = 20.
   - Exact weight distribution: A₀ = 1, A₈ = 6 (the 6 octad stabilizers), A₁₆ = 9.
   - Triply-even property: every non-zero codeword weight w ∈ {8, 16} satisfies w % 8 = 0.

2. Exact Distillation Yield:
   - 24-to-4 protocol yield: γ = k / n = 4 / 24 = 1 / 6.
   - Comparison with Bravyi-Kitaev 15-to-1 yield: γ₁₅ = 1 / 15.
   - Exact yield advantage: (1 / 6) / (1 / 15) = 5 / 2 = 2.5× higher yield.

3. Exact Error Suppression Order:
   - Minimum distance d = 8 guarantees that all errors of weight 1 ≤ w ≤ 7 are detected.
   - Leading undetected logical errors have weight 8 (octad stabilizers).
   - Error suppression exponent: d = 8 ≥ 3.
   - Bounding inequality: for all ε ∈ [0, 1], ε⁸ ≤ ε³.
   - Therefore, the output error rate scales strictly as O(ε⁸) ⊆ O(ε³).

4. Refutation of OP-027 Falsification Criterion:
   - The output error rate scales as O(ε⁸), strictly meeting and exceeding the O(ε³) threshold.
-/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/MultiregularCSSClassification.lean`

Content ID `8dafaa84cbf87ffd`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L32**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Formal Synthesis Engine

# Classification of CSS Codes from Multiregular Higher-Tower Sectors (OP-029, HYP-128)

This module formally settles Open Problem OP-029 (Level L3, Domain 3: Quantum Error Correction & CSS Codes):
"For multiregular sectors at D=128 (29 sectors) and D=256 (82 sectors), classify which sectors satisfy
A_chi A_chi^T == 0 (mod 2) and determine their CSS parameters [[N, K, d]]."

## Key Theorems Formally Certified:
1. Exact Multiregular Sector Counts:
   - D = 128 (n = 7): exactly 29 multiregular sectors (HYP-112).
   - D = 256 (n = 8): exactly 82 multiregular sectors (HYP-112).

2. Universal CSS Code Parameter Equations for Dimension D = 2^n ≥ 64:
   - Block length (physical qubits): N(D) = 2(D - 4).
   - Check matrix rank over GF(2): r(D) = (D - 8) / 2.
   - Logical dimension: K(D) = N(D) - 2 * r(D) = 2(D - 4) - (D - 8) = D.
   - Quantum distance: d(D) = 2, from identical columns of twin-pair zero divisors.

3. Concrete Parameters for D = 128 and D = 256:
   - D = 128: [[248, 128, 2]] with rank 60 across all 29 multiregular sectors.
   - D = 256: [[504, 256, 2]] with rank 124 across all 82 multiregular sectors.

4. Commutativity & Falsification Refutation:
   - CSS commutativity condition is defined by H_X * H_Z^T == 0 (mod 2).
   - For symmetric codes (H_X = H_Z = A_chi), commutativity is identically equivalent
     to self-orthogonality A_chi * A_chi^T == 0 (mod 2).
   - Therefore, a sector with A_chi A_chi^T == 0 (mod 2) cannot fail commutativity.
-/
````

**L140–L142**

````text
/-- Full Settlement of Open Problem OP-029:
    All multiregular sector counts, universal parameters [[248, 128, 2]] and [[504, 256, 2]],
    and commutativity refutation are formally certified. -/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/QuantumThresholdObstruction.lean`

Content ID `c8dc5250c6683b66`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L31**

````text
/-!
# Quantum Threshold Obstruction Theorem (HYP-102, OP-024)
  **Epistemic Classification:** [C] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

Formal verification settling Open Problem OP-024:
1. Symmetric CSS code parameter structures:
   - D=64:  [[120, 64]] with N = 120, K = 64, check weight 56, rank 28.
   - D=128: [[248, 128]] with N = 248, K = 128, check weight 120, rank 60.
2. Exact code distance d = 2 across all dimensions:
   - Preserved from HYP-083 (QuantumCodeDistance.lean).
   - Twin-vertex degeneracy creates non-trivial weight-2 logical operators.
3. Twin pair counting and linear scaling:
   - D=64:  A_2 = 180 twin pairs in parity checks H_X, H_Z.
   - D=128: A_2 = 372 twin pairs in parity checks H_X, H_Z.
   - Exact scaling identity: 2 * A_2(N) = 3 * N across both levels.
4. Threshold vanishing obstruction:
   - Every twin pair e_u + e_v forms an undetectable weight-2 error with syndrome s = 0.
   - Any syndrome-based decoder (including BP-OSD) outputs zero correction, failing
     to correct twin errors.
   - As N increases, weight-2 logical error occurrence probability strictly increases:
     A_2(248) = 372 > A_2(120) = 180.
   - Consequently, the asymptotic crossing threshold is identically zero: p_th = 0.
-/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/RateDistanceProduct.lean`

Content ID `718b52781fbc37a8`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L1–L20**

````text
/-
Copyright (c) 2026 Sovereign Autonomous Research Engine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sovereign Research Collective
  **Epistemic Classification:** [A] Arithmetic Identities

  All theorems in this file are arithmetic identities verified by `rfl` or `decide`.

! HYP-084: Asymptotic Rate-Distance Product Vanishing in Cayley-Dickson CSS Towers
Settles Open Problem OP-026:
Proves that in the infinite tower of Cayley-Dickson symmetric CSS stabilizer codes
[[N(D), K(D), d(D)]] with N(D) = 2(D - 4), K(D) = D, and d(D) = 2 (HYP-083):
1. The rate-distance product is given by P(D) = (K * d) / N^2 = 2D / (2(D - 4))^2.
2. The sequence is strictly monotonically decreasing along the tower:
   P(16) = 1/18 > P(32) = 1/49 > P(64) = 2/225 > P(128) = 4/961 > P(256) = 2/992.
3. Asymptotic limit lim_{D -> inf} P(D) = 0, proving that the rate-distance product
   does NOT remain strictly positive.
4. For hypergraph product codes where d = Omega(sqrt(N)) = O(D), the product
   P_HGP(D) <= 4 / D likewise vanishes asymptotically.
-/
````

### `hankel/output-final_aristotle/Sovereign/Quantum/SpongeAlgebraicDegree.lean`

Content ID `eb7e55d7ac010d42`; 1 byte-identical path(s); machine-indexed; substantive review pending.

**L7–L18**

````text
/-!
# Exact Algebraic Degree of Ramanujan Sedenion Sponge Permutation (HYP-103, OP-051)

Formal verification settling Open Problem OP-051:
1. Sponge state width: b = 32 bytes = 256 bits.
2. Canonical maximum algebraic degree for invertible permutation: d_max = 255.
3. Round 1 lower bound: d(1) >= 16 from 16-bit ARX carry chains and expander branch multiplexing.
4. Exponential doubling progression under non-linear ARX carry recurrence:
   d(r+1) = min 255 (2 * d(r)).
5. Saturation at maximal algebraic degree: d(r) = 255 for all r >= 5.
6. Refutation of falsification threshold: d(8) = 255 >= 128, with strict margin 127.
-/
````

**L102–L105**

````text
/-- Master theorem settling Open Problem OP-051:
    The 24-round Ramanujan sedenion sponge permutation achieves algebraic degree 255 at round 8
    (strictly refuting the falsification bound 128 by 127 degrees), and maintains maximal degree
    saturation 255 across all rounds 5 through 24. -/
````

