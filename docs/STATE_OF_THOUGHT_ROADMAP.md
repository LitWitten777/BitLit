# State of Thought × sedenions — roadmap for future work

This roadmap continues the formalisation in `docs/STATE_OF_THOUGHT.md` (modules
`Sovereign/Meta/StateOfThought*.lean`). It starts with what is settled, then lists open items
in order of priority. Each item gives the Lean statement to aim for, a suggested method, and
what the result would change about the controller design.

## 0. Status as of this run (all machine-checked, no `sorry`)

| Area | Settled results |
|---|---|
| Paper definitions | dispersion is a variance; `|c_t| < 1`; `H_t ≥ 0`; normalisation is injective; 577 + 5 = 582 parameters; the sigmoid stop is a linear threshold; monotonicity of the training-free score |
| Cayley–Dickson tower | `Re(x ȳ) = ⟨x,y⟩` at every level; the sedenions are the first level with zero divisors; octonions alternative but not associative; sedenions not alternative |
| Sedenion score | `Re(S_t S̄_i)` is exactly the descriptor dot product, so it adds nothing beyond a fixed bilinear kernel |
| Traps | zero divisors are balanced (`‖a‖ = ‖b‖`); descriptor traps need `2⟨m_t,m_i⟩ = ‖m_t⊙m_i‖²`; off-center traps exist; exact classification on the `{−1,0,1}⁴` grid |
| Curvature | the associator is purely imaginary; the sedenions are flexible, so return trajectories `A → B → A` have zero curvature |
| 168 census | 168 of the 256 signed cross-half vectors have a two-term annihilator |
| Zero-divisor theorem (item 1.1, **done**) | `x = (a,b) ≠ 0` is a zero divisor ⇔ `Re a = Re b = 0`, `‖a‖ = ‖b‖`, `a ⊥ b`; unit case = `V₂(ℝ⁷)`; the annihilator is exactly `{(‖b‖²c, (ac)b) : c ⊥ 1,a,b,ab}` |
| Descriptor traps (item 1.2, **characterisation done**) | `descriptor_trap_iff`, `offcenter_trap_family` |
| Stopping rule (item 2.2, **done**) | threshold monotonicity, one-counter implementation, bounded latency |

## 1. Near term (well-scoped Lean work)

### 1.1 Finish the zero-divisor description (Stiefel / G₂ link)
* **Goal.** For `x = (a, b) ∈ 𝕆²` over ℝ with `x ≠ 0`: `x` is a zero divisor ⇔ `Re a = Re b = 0`, `‖a‖ = ‖b‖` and `⟨a, b⟩ = 0`.
* **Done so far.** `‖a‖ = ‖b‖` (`sedenion_zero_divisor_balanced`).
* **Still needed.**
  - The pure-imaginary and orthogonality conditions. From `ac = d̄b` and `da = −bc̄`, use octonion alternativity (`ā(ab) = ‖a‖² b`, provable by the same polynomial-identity method as `nsq_mul_three`) and real-part identities.
  - The converse: build the annihilator explicitly. For orthonormal pure-imaginary `a, b`, the kernel of `L_x` is 4-dimensional; the numerical experiments reproduce this.
* **Payoff.** Normalised zero divisors then form a copy of the Stiefel manifold `V₂(ℝ⁷)`. This is the formal "Stiefel" bridge to the existing `StiefelCubature` modules. It also gives descriptor traps as an explicit real-algebraic set.

### 1.2 Descriptor trap variety
* **Goal.** `S_{t,i}` is a trap ⇔ `m_t 0 = m_i 0 = 0`, `2⟨m_t,m_i⟩ = ‖m_t⊙m_i‖²` and `⟨m_t, m_t − m_i⟩ + ⟨m_i, m_t⊙m_i⟩ = 0`. This follows from 1.1 by specialisation.
* **Then.** Parametrise the variety; the family `m_i = (0, 2/p, 0, 0)` is one chart. Prove its dimension, and decide whether it meets the region that normalised LLM states actually occupy.
* **Controller consequence.** Traps can occur only when both dispersions sit exactly at the population mean (`m_t 0 = m_i 0 = 0`). That is a measure-zero event, so a trap detector needs a *near*-trap version (1.3).

### 1.3 Quantitative near-traps
* **Goal.** A lower bound `‖S Y‖ ≥ κ(S)‖S‖‖Y‖`, where `κ(S)` is the smallest singular value of `L_S` divided by `‖S‖`. The detector then thresholds `κ(S_{t,i})`.
* **Method.**
  - Relate `κ` to the defects `|‖a‖² − ‖b‖²|`, `|Re a|`, `|Re b|`, `|⟨a,b⟩|` (a stability version of 1.1).
  - Certify concrete bounds with the `StateOfThoughtLeftMul` certificate method, extended from "invertible" to "Gram matrix `L_Sᵀ L_S ⪰ κ² I`" (an LDLᵀ certificate over ℚ).

### 1.4 Curvature: what the associator can detect
* Done: `Re[x,y,z] = 0` and `[x,y,x] = 0`.
* Next:
  - `⟨[x,y,z], y⟩ = 0`. This is observed numerically; prove it by a polynomial identity.
  - Trilinearity and scaling, so that the normalised curvature `‖[A,B,C]‖/(‖A‖‖B‖‖C‖)` is scale-invariant.
  - Show that the associator vanishes on any quaternionic subalgebra, so trajectories confined to a quaternion slice are "flat".
  - Characterise the descriptor trajectories with zero curvature.
* **Negative result to record.** Period-2 loops are invisible to the associator (`descriptor_curvature_return`). A loop detector should use longer windows (for example `[S_{t−3}, S_{t−1}, S_t]`) or the trap test.

## 2. Medium term (connect to the controller)

### 2.1 Algebraic selection head versus the MLP
* **Proved.** `Re(S_t S̄_i)` is a fixed bilinear kernel.
* **Next.**
  - Formalise the function class of `φ_sel` (a ReLU MLP `16 → 32 → 1`).
  - Prove it contains every quadratic form in `d_{t,i}` up to ε on compact sets. This is a universal-approximation statement; Mathlib has only partial support, so the needed pieces would be built here.
  - Conversely, show that the parameter-free rule "score = −κ(S_{t,i})" (from 1.3) cannot be expressed by any linear layer on `d_{t,i}`, because it is not a polynomial of degree ≤ 2.
* **Deliverable.** A theorem that states exactly which sedenionic scores are new relative to the 577-parameter head.

### 2.2 Stopping rule
* **Proved.** `σ(w·m+b) > τ` is a linear threshold.
* **Next.**
  - Formalise the Appendix D windowed rule (`H_t` and `v_t` low, `c_t > 0` over `r_stop` steps) as a finite automaton.
  - Prove that it is monotone in the thresholds and that, for bounded feature sequences, it fires within a bounded time once the conditions hold.

### 2.3 Octonion / quaternion projections as a control law
* Define `π_𝕆(S) = (q₀, q₁)` and `π_ℍ(S) = q₀`.
* Prove the associator vanishes on `π_ℍ`-images and is controlled on `π_𝕆`-images: the octonions are alternative, so `[x,x,y] = 0`.
* Specify a control law that switches between sub-algebras when `κ` or the curvature crosses a threshold, and prove it is well-defined and Lipschitz away from the trap variety.

## 3. Longer term / research questions

1. **The 168 count beyond two-term annihilators.** The census counts cross-half vectors with a *two-term* annihilator. By 1.1, `±e_i ± e_{8+j}` is a zero divisor exactly when `i, j ≠ 0` and `i ≠ j`, so the 88 others have no annihilator of any shape. Formalising 1.1 turns the census into a statement about all annihilators. The certificate method can also check the 88 directly now.
2. **Higher Cayley–Dickson levels (32-D and up).** Extend the balance law and the grid classification to level 5 and above. The descriptor could be enlarged (for example with velocity/consistency history blocks) to fill a 32-D pathion.
3. **Empirical validation (outside Lean).** Run the paper's feature extractor on real reasoning traces and measure how often `κ(S_{t,i})` is small and whether small `κ` correlates with loops or contradictions. This is an experiment, not a proof. Any claim coming out of it should be labelled as such.
4. **Paper cross-check.** The formalisation follows the transcription in the request, not the arXiv PDF. Once the authors release code, compare definitions (normalisation statistics, ε placement, entropy base) and update `StateOfThoughtFeatures.lean` if they differ.

## 4. Engineering notes

* **Build cost.** `StateOfThoughtLeftMul.coord16_mul_eq` and `StateOfThoughtCurvature.assoc_four_flexible` are brute-force polynomial identities (about 2–3 minutes each). An inductive proof of bilinearity and flexibility for the whole tower would remove this cost and generalise to all levels.
* **Certificates.** The grid classification uses `native_decide` (trusted compiler) on 662 matrix checks. To remove the compiler from the trusted base, precompute the inverse matrices as literals and check them with `decide` in the kernel, or switch to an LDLᵀ certificate over ℤ.
* **Index.** New modules must be added to `Sovereign/Meta.lean`; `scripts/gen_indices.py` flags any that are missed.
