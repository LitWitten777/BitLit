# Sovereign Mathematical Research Roadmap v2.0
## Triply Even Codes, Admissible Pairs, Coding Theory, and Spectral Geometry

**Status:** Active Execution  
**Governance:** Token-Efficient Computational Research Protocol & Double Verification (Haskell + Lean 4)  
**Reference Analysis:** `docs/RESEARCH_ANALYSIS.md`  
**Computational Engine:** `haskell/sovereign-compute`  

---

## 1. Executive Summary & Epistemic Grounding

This roadmap establishes the mathematical trajectory of the Sovereign research program following the comprehensive audit in `docs/RESEARCH_ANALYSIS.md`.

### Core Epistemic Principles:
1. **Separation of Authentic Theorems from Parameter-Level Analogies**:
   - All physical analogies (Navier-Stokes, Yang-Mills, 3-generation Standard Model) that merely attach grand names to trivial arithmetic evaluations are permanently discarded from the mathematical foundation.
   - The verified mathematical core is strictly preserved: Cayley-Dickson zero divisors, cross-half annihilation graph topology, exact degree censuses, higher moments, twin-class equitable quotients, and spectral characterizations.
2. **Double Verification Standard**:
   - Every candidate theorem must first be computed and verified across dimensions in the exact Haskell computational engine (`sovereign-compute`), logging exhaustive diagnostics.
   - Every claim must subsequently be formally proven in Lean 4 without `sorry` and without non-standard axioms.
3. **Token-Efficient Research Protocol**:
   - Raw combinatorial explosions are forbidden from LLM context windows. All state space enumeration runs in native Haskell code, reducing results to compact minimal context packets (<500 tokens) with sha256 checksums and dual logging (`logs/experiment_log.jsonl`, `logs/conjectures.jsonl`, `logs/research/*.json`, `logs/research/RESULTS.md`).

---

## 2. Comprehensive Workstreams

```
+-------------------------------------------------------------------------------+
|                      SOVEREIGN MATHEMATICAL WORKSTREAMS                       |
+-------------------------------------------------------------------------------+
| W1: Uniform Moment Theorem          | W7: Admissible Pairs & Bijective Theory |
|     - M_k(D) polynomial deg k+2     |     - Explicit fiber bijection 2^(q-k)  |
|     - Vanishing D^(k+1) term        |     - 2-automatic sequence & F₂ series  |
|     - Moment doubling recurrence    +-----------------------------------------+
+-------------------------------------+ W8: Spectral Quadratic Fields & Expander|
| W2: Sector Census Closed Form       |     - Regular quotient spectrum         |
|     - Closed form sectorCount(n,χ,v)|     - Q(sqrt(57)) & field stabilization |
|     - 2^(n-3) isomorphism classes   |     - Alon-Boppana mod 8 non-residue    |
+-------------------------------------+-----------------------------------------+
| W3: Prefix-Depth Classification     | W9: Quantum LDPC & Hypergraph Products  |
|     - Bitwise descent invariants    |     - [[976, 16, >=8]] CSS code from W6 |
|     - Pair multiplicity 2^(q-k)     |     - Exact F₂ commutation H_X H_Zᵀ = 0 |
+-------------------------------------+-----------------------------------------+
| W4: Graph Topology & Counts         | W10: 2-Automatic Automaton Dynamics     |
|     - (D-2)(D-4) vertices           |     - 4-State DFA over prefix bits      |
|     - D³/4 - 28D + 96 edges         |     - Transfer spectrum {0, 1, 1, 2}    |
|     - Degree 2 * towerDegree        |     - Universal mod 24 vanishing        |
+-------------------------------------+-----------------------------------------+
| W5: Equitable Quotient Spectra      | W11: Sedenion Fano Zero Divisors        |
|     - Integer exhaustive for D<=32  |     - 336 pairs, 100% cross-half        |
|     - Splitting over Q(sqrt 57) D=64|     - K_{6,6} \ 3 K_{2,2} Fano blocks   |
+-------------------------------------+-----------------------------------------+
| W6: Triply Even Codes & CSS         | W12: Trigintaduonion (D=32) Variety     |
|     - [24, 4, 8] code, wt mod 8 = 0 |     - 5040 pairs (336+336+3696+672)     |
|     - Transversal T-gates           |     - 100% charge conservation          |
|     - [[24, 16, 8]] CSS stabilizer  |     - 8 x 336 + 7 x 144 stratification  |
+-------------------------------------------------------------------------------+
```

---

## 3. Detailed Specifications

### Workstream W6: Triply Even Binary Codes & Quantum CSS Stabilizers (Immediate Priority)

**Mathematical Foundation:**
- In dimension $D_a = 16$, the cross-half annihilation graph decomposes into 7 non-trivial charge sectors of 24 vertices each. Every vertex has degree $d = 8 \equiv 8 \pmod{16}$.
- The intersection of neighbourhoods (common neighbours between any two vertices) satisfies $|N(u) \cap N(v)| \equiv 0 \pmod 4$.
- These two congruences ($d \equiv 0 \pmod 8$ and $|N(u) \cap N(v)| \equiv 0 \pmod 4$) are the exact algebraic input conditions for generating a **triply-even binary linear code** over $\mathbb{F}_2$:
  $$w(c) \equiv 0 \pmod 8 \quad \forall c \in C$$
- **Transversal T-Gate Realization**:
  Triply-even codes are the fundamental building blocks of fault-tolerant quantum computation: they support transversal application of the $T$-gate ($T = \mathrm{diag}(1, e^{i\pi/4})$) without magic state distillation:
  $$T^{\otimes n} |c\rangle = e^{i \pi w(c) / 4} |c\rangle = |c\rangle \quad \text{since } w(c) \equiv 0 \pmod 8$$
- **Connection to Classical Codes**:
  - The 24-vertex sector in $D=16$ provides a natural embedding into $\mathbb{F}_2^{24}$. The Golay code $\mathcal{G}_{24} = [24, 12, 8]$ is doubly-even; subcodes generated by the sector incidence matrices must be classified against the Fano subcode $[24, 4, 8]$ and the Golay family.
  - For $D=32, 64$, the neighbourhood matrices yield codes of block length $(D-2)(D-4)/4$ and individual sector lengths $2^n - 2$.

**Computational Agenda (Haskell)**:
1. Construct adjacency/neighbourhood binary matrices for $D=16, 32, 64$.
2. Implement Gaussian elimination over $\mathbb{F}_2$ to determine code rank ($k$) and generator matrix $G$.
3. Compute exact weight distribution $A_w = |\{c \in C : \mathrm{wt}(c) = w\}|$ via Gray code or recursive enumeration.
4. Test self-orthogonality ($C \subseteq C^\perp \iff G G^T = 0 \pmod 2$).
5. Construct CSS parity check matrices $H_X, H_Z$ such that $H_X H_Z^T = 0 \pmod 2$ and evaluate the quantum parameters $[[n, k_{CSS}, d]]$.

---

### Workstream W7: Admissible Pairs & Bijective Structure Theory

**Mathematical Foundation:**
- Admissible pairs $(i, j)$ index the basis units $e_i, e_j$ whose cross-half combinations yield zero divisors.
- Multiplicities of degrees in dimension $D = 2^{q+3}$ are given by $\mathrm{censusT}(q, t) = 2^{q - \mathrm{prefixDepth}(t)}$.
- **Bijective Goal**: Construct an explicit, deterministic map:
  $$\Phi: \{(i, j) \in \mathrm{Admissible}(D)\} \longrightarrow \{0, 1, \dots, 2^q - 1\}$$
  such that the fiber over $t$ has cardinality exactly $2^{q - \mathrm{prefixDepth}(t)}$.
- **Automaticity**: Demonstrate that the bivariate degree sequence $d(i, j)$ is generated by a finite state automaton reading the binary digits of $i$ and $j$, proving that $\sum_{i,j} d(i, j) x^i y^j$ is an algebraic power series over $\mathbb{F}_2$.

**Computational Agenda (Haskell)**:
1. Implement bit-level descent tracker for pair evaluation.
2. Build empirical transfer matrices representing transitions between bit-states $(i_b, j_b)$.
3. Verify that transfer matrix eigenvalues reproduce the moment doubling law.

---

### Workstream W8: Spectral Quadratic Fields & Graph Expansion

**Mathematical Foundation:**
- Each sector graph admits a twin-class partition (vertices with identical neighbourhoods). The quotient matrix has size $(D_a - 2)/2$.
- In $D=16$, all eigenvalues are integers $\{ \pm 8, \pm 4^2, 0^{18} \}$.
- In $D=32$, all eigenvalues remain strictly integral across all 15 sectors.
- In $D=64$, regular sectors split with quadratic factor $x^2 + 4x - 224$ over $\mathbb{Q}(\sqrt{57})$.
- **Open Algebraic Question**: In $D=128, 256$, what algebraic number fields $\mathbb{Q}(\sqrt{\Delta})$ appear in the regular and irregular quotient spectra?
- **Alon-Boppana Obstruction**: $d - 1 = D_a - 9 \equiv 7 \pmod 8$ is never a perfect square, so Ramanujan saturation $2\sqrt{d-1}$ is always irrational, preventing integral sectors from being Ramanujan graphs.

**Computational Agenda (Haskell)**:
1. Compute exact characteristic polynomials of equitable quotient matrices for $D=128$ using Faddeev-LeVerrier with arbitrary precision integer arithmetic (`Integer`).
2. Factor characteristic polynomials over $\mathbb{Z}[x]$ using square-free decomposition and integer root deflation.
3. Identify discriminant square-free parts $\Delta$ for non-integral factors.

---

### Workstream W1: The Uniform Moment Theorem

**Mathematical Foundation:**
- The degree moments $M_k(D) = \sum_v v^k \cdot \mathrm{mult}(v)$ are proved in Lean for $k \le 4$.
- All verified moments satisfy:
  $$M_k(D) = \sum_{j=1}^{k+2} c_{k, j} D^j \quad \text{with } c_{k, k+1} = 0$$
- The Moment Doubling Law:
  $$M_k(q+1) = 2 \sum_s \left[(2D - x)^k + x^k\right] \cdot \mathrm{censusT}(q, s) + (2D - 4)^k \cdot 6(D - 1)$$
  where $x = 16s + 12$.

**Computational Agenda (Haskell)**:
1. Compute rational coefficients for $M_5, M_6, M_7, M_8$.
2. Formulate the explicit generating function $F(z, D) = \sum_{k=0}^\infty M_k(D) \frac{z^k}{k!}$.

---

## 4. Execution Sequence & Milestones

| Milestone | Target | Description | Tooling |
|---|---|---|---|
| **M1** | Haskell Engine Extension | Add `Sovereign.Coding.TriplyEven` & `Sovereign.Coding.CSS` | GHC / Cabal |
| **M2** | W6 Computation: $D=16, 32$ | Compute code generator, rank, weight enumerator, triply-evenness | `sov-compute w6` |
| **M3** | W7 Computation: Admissible Pairs | Implement prefix-depth fiber bijection & 2-automatic automaton | `sov-compute w7` |
| **M4** | W8 Computation: $D=128$ Spectra | Factor quotient charpoly for $D=128$, find quadratic fields | `sov-compute w8` |
| **M5** | Lean 4 Theorem Targets | Formulate Lean specs in `Sovereign/Coding/TriplyEven.lean` | Lean 4 |
| **M6** | Formal Verification | Machine-check proofs with zero `sorry` and standard axioms | `lake build` |

---

## 5. Summary of Deliverables

1. **`haskell/src/Sovereign/Coding/TriplyEven.hs`**: Exact binary code builder, GF(2) linear algebra, weight enumerator, CSS stabilizer generator.
2. **`logs/research/w6_triply_even.json`**: Complete parameters $[n, k, d]$, weight distributions $A_w$, and CSS parameters $[[n, k_{CSS}, d]]$.
3. **`logs/conjectures.jsonl`**: Token-efficient theorem packets (<500 tokens) summarizing authenticated mathematical invariants.
