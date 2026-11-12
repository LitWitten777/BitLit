# State of Thought × sedenions: what is formalised

This note covers seven Lean modules in `Sovereign/Meta/`. All seven build with no `sorry`.
They formalise the *State of Thought* controller definitions (arXiv:2609.16055) as they were
transcribed in the request (I did not consult the paper itself), and they test the proposed
sedenionic reading of the 16-dimensional descriptor.

| Module | Content |
|---|---|
| `StateOfThoughtFeatures.lean` | sentence center, dispersion, velocity, consistency, entropy, normalisation, descriptor, controller heads, training-free baseline |
| `StateOfThoughtCayleyDickson.lean` | Cayley–Dickson tower `CDA R n` over any commutative ring (convention `(a,b)(c,d) = (ac − d̄b, da + bc̄)`, the same as `Sovereign.CD`) |
| `StateOfThoughtSedenion.lean` | descriptor read as a sedenion `(m_t, m_i, m_t − m_i, m_t ⊙ m_i) ∈ ℍ⁴` |
| `StateOfThoughtCensus.lean` | the 168 signed cross-half zero divisors in this convention |
| `StateOfThoughtLeftMul.lean` | left multiplication as an explicit 16×16 matrix; checkable certificates that a rational sedenion is not a zero divisor over ℝ |
| `StateOfThoughtTraps.lean` | which descriptors are zero-divisor traps: balance law, off-center traps, exact classification on the `{−1,0,1}` grid |
| `StateOfThoughtCurvature.lean` | structural identities for the associator ("inferential curvature") |

## Paper-side facts (all proved)

* `dispersion_eq_mean_sq_dev`: `δ_t = (1/n)Σ‖h_i − u_t‖²`. So `δ_t ≥ 0`, and `δ_t = 0` exactly when all token embeddings coincide.
* `abs_consistency_lt_one`: `|c_t| < 1` for `ε > 0`. `consistency_pos_of_same_direction`: consecutive steps that point the same way give `c_t > 0`.
* `meanEntropy_nonneg`: `H_t ≥ 0`.
* `normalize_inj`, `normalize_eq_zero_iff`: the normalisation loses no information, and `m_t = 0` exactly when `s_t = μ`.
* `controller_params`: 544 + 33 = 577, 5, and 582 in total.
* `stop_iff_logit`: `σ(w·m + b) > τ` holds exactly when `w·m + b > log(τ/(1−τ))`. The stopping head is therefore a linear threshold rule.
* `tfScore_eq_descriptor`: the training-free score depends on `(m_t, m_j)` only through the drift and interaction blocks of the descriptor. `tfScore_mono` shows it rises with `c_j` and falls with `H_j`. `tfStop_mono` shows the window rule is monotone in the window length.

## Sedenion-side facts (all proved)

* `re_mul_conj`: at every level of the tower, `Re(x ȳ) = ⟨x, y⟩`.
* `first_zero_divisor_level`: over an ordered field, level `n` has zero divisors exactly when `n ≥ 4`. The witness is `(e₃ + e₁₀)(e₆ − e₁₅) = 0` (`sedenion_zero_divisor`), and levels ≤ 3 are covered by norm multiplicativity (`nsq_mul_three` for the octonions).
* `assoc_two`: the quaternions are associative. `assoc_three_left_alternative` and `assoc_three_basis`: the octonions are alternative but not associative. `assoc_four_not_alternative`: the sedenions are not alternative, since `[x,x,y] = 2e₁₅` for `x = 1 + e₁ + e₁₀` and `y = e₄`.
* `sedenion_score_blocks`: the proposed parameter-free score `Re(S_t · S̄_i)` is exactly the Euclidean dot product of the two descriptors. It equals the sum of the four block dot products. **Consequence:** this invariant carries no non-associative information. It is a fixed bilinear kernel, a special case of what a linear layer on `d_{t,i}` can express.
* `normalized_descriptor_zero_divisor` / `descriptor_zero_divisor`: descriptor zero-divisor traps exist. Suppose the current state sits at the normalisation center (`m_t = 0`) and the historical state is a nonzero pure-imaginary quaternion (`m_i = (0,a,b,c)`). Then `S_{t,i}` is annihilated by the explicit nonzero sedenion `c e₁ − a e₃ − c e₁₃ + a e₁₅` (or, if `a = c = 0`, by `b e₁ − b e₁₃`).
* `descriptor_associator_ne_zero`: the associator of three descriptor sedenions along a trajectory can be nonzero (`4e₂` in the explicit example).
* `crossHalf_zd_census`, `crossHalf_zd_iff` (both checked with `native_decide`): exactly 168 of the 256 signed vectors `±e_i ± e_{8+j}` have a signed two-term annihilator, namely those with `i ≠ 0`, `j ≠ 0` and `i ≠ j`. This matches `Sovereign.zd_card_16`.

## Trap classification (all proved, `StateOfThoughtTraps.lean`)

* `sedenion_zero_divisor_balanced`: if `x = (a,b)` and `y = (c,d)` are nonzero sedenions (pairs of octonions) with `xy = 0`, then `‖a‖ = ‖b‖` and `‖c‖ = ‖d‖`. Works over any ordered field. The proof takes norms of the two octonion equations `ac = d̄b`, `da = −bc̄` and uses octonion norm multiplicativity.
* `descriptor_trap_balance`: so a descriptor trap must satisfy `2⟨m_t, m_i⟩ = ‖m_t ⊙ m_i‖²`. Most state pairs fail this test at once.
* `offcenter_trap₁`, `offcenter_trap₂`: **traps are not confined to `m_t = 0`.** The pair `m_t = (0,−2,0,0)`, `m_i = (0,−1,0,0)` is annihilated by `e₂ + e₁₄`. The pair `m_t = (0,−1,1,2)`, `m_i = (0,−2,0,0)` is annihilated by `e₆ + 2e₇ − 2e₉ + e₁₃`. Earlier I read the grid scan as suggesting that `m_t = 0` was the only trap family. That is true only on the grid.
* `grid_trap_iff`: on the grid `m_t, m_i ∈ {−1,0,1}⁴` (6561 pairs), `S_{t,i}` has a nonzero right annihilator **exactly** when `m_t = 0` and `m_i` is pure imaginary. This replaces the earlier unverified Python scan with a theorem. How the proof works:
  - the family direction is `descriptor_zero_divisor`;
  - grid pairs that fail the balance law are excluded by `descriptor_trap_balance`;
  - the remaining 662 grid pairs are excluded by invertibility certificates. For each one, an untrusted Gauss–Jordan routine proposes an inverse of the 16×16 left-multiplication matrix, and Lean checks the product against the identity (`native_decide`, about 2 minutes). `eq_zero_of_certCheck` then transfers this to "no nonzero real annihilator".
* `coord16_mul_eq` (`StateOfThoughtLeftMul.lean`): `(xy)_i = Σ_j lmat x i j · y_j`, where `lmat x i j = ±x_{i⊕j}`. It is proved over any commutative ring.

## Curvature identities (all proved, `StateOfThoughtCurvature.lean`)

* `re_assoc_four`: the sedenion associator is purely imaginary, `Re[x,y,z] = 0`.
* `assoc_four_flexible`: the sedenions are flexible, `[x,y,x] = 0`. `assoc_four_self`: `[x,x,x] = 0`.
* `descriptor_curvature_return`: **the associator curvature of a return trajectory `A → B → A` is exactly 0,** whatever the middle state is. So the proposed curvature metric cannot detect period-2 reasoning loops. Any loop detector has to use something else, for example the trap test above or longer windows.

## Full zero-divisor theorem and Stiefel link (all proved)

Files: `StateOfThoughtStiefel.lean`, `StateOfThoughtZeroDivisors.lean`, `StateOfThoughtStiefelKernel.lean`.

* `sedenion_zero_divisor_iff`: over any ordered field, a nonzero sedenion `x = (a, b)` has a nonzero right annihilator **exactly** when `Re a = Re b = 0`, `‖a‖ = ‖b‖` and `⟨a, b⟩ = 0`.
  - Forward direction: the polynomial identities `re_fst_mul_nsq`, `re_snd_mul_nsq` (`Re a · ‖y‖² = 0` and `Re b · ‖y‖² = 0` whenever `xy = 0`) and `dot_mul_nsq` (`⟨a,b⟩ · ‖y‖² = 0` once the real parts vanish), together with the balance law.
  - Converse: `stiefelAnnihilator_mul` shows `(a, b) · (‖b‖² c, (a c) b) = 0` for every `c` orthogonal to `1, a, b, a b` (over any commutative ring). `exists_imag_orthogonal` supplies a nonzero such `c` by a dimension count (4 linear conditions on 8 coordinates).
* `unit_sedenion_zero_divisor_iff_stiefel`: when `‖a‖ = ‖b‖ = 1`, `(a, b)` is a zero divisor iff `(a, b)` is an orthonormal pair of imaginary octonions, i.e. a point of the Stiefel manifold `V₂(ℝ⁷)`. (The Stiefel manifold itself is not defined as a Lean object; the statement is the defining equations.)
* `annihilator_eq_stiefel`: over a field of characteristic 0, for such a pair (with `‖b‖ ≠ 0`) the right annihilator is **exactly** `{(‖b‖² c, (a c) b) : c ⊥ 1, a, b, a b}`, the image of a 4-dimensional space.
* `descriptor_trap_iff`: the descriptor sedenion `S_{t,i}` is a trap iff `m_t 0 = m_i 0 = 0`, `2⟨m_t, m_i⟩ = ‖m_t ⊙ m_i‖²` and `⟨m_t, m_t − m_i⟩ + ⟨m_i, m_t ⊙ m_i⟩ = 0`. So traps require both dispersion coordinates to sit exactly at the normalisation mean.
* `offcenter_trap_family`: `m_t = (0, p, q, r)`, `m_i = (0, 2/p, 0, 0)` with `p ≠ 0` and `p² + q² + r² + 4/p = 2` is always a trap. This was previously derived by hand only.

The certificate coefficients were found offline by solving linear systems; Lean checks each identity with `linear_combination`, so nothing from the offline computation is trusted.

## Stopping rule (all proved, `StateOfThoughtStopping.lean`)

* `tfStop_mono_threshold`: the Appendix D rule is monotone in both thresholds.
* `tfStop_iff_runLen`: the rule fires at `t` iff a single counter `runLen t` (length of the current run of good steps) has reached `min r (t+1)`. So it can be run online with one counter.
* `tfStop_of_good_from`: once the conditions hold from step `t₀` on, the rule fires at step `t₀ + r − 1`.
* `tfStop_not_of_bad`: it never fires at a step where the conditions fail.

## Not verified

* Using projections onto octonionic or quaternionic subalgebras as a control law is still not formalised.

See `docs/STATE_OF_THOUGHT_ROADMAP.md` for the plan.
