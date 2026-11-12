# The mutual annihilation graph of the 168 sedenion zero divisors

All results below are machine-checked in Lean (no `sorry`, no `native_decide`; the axioms
used are `propext`, `Classical.choice`, `Quot.sound`). Summary theorems:
`Sovereign.ZD.zdGraph_main` and `Sovereign.ZD.assocCentralizer_main` in
`Sovereign/Graph/SedenionAnnihilationMain.lean`.

## Setting

* `Sovereign/Graph/SedenionCoord.lean` — the sedenions `𝕊 = Sed ℝ` as `Fin 16 → ℝ` with
  `eₐ e_b = sgn a b · e_{a⊕b}`.
* `Sovereign/Graph/SedenionCoordCDA.lean` — `ofCDA_mul`: this product *is* the fourfold
  Cayley–Dickson double `(a,b)(c,d) = (ac − d̄b, da + bc̄)` (the tower `CDA R 4`).
* `Sovereign/Graph/MutualAnnihilationGraph.lean` — vertices: the 168 vectors `± eᵢ ± e₈₊ⱼ`,
  `i, j ∈ {1..7}`, `i ≠ j`; `zdGraph`: `a ~ b` iff `a b = 0 ∧ b a = 0`.
  One-sided annihilation is automatically mutual (`toSed_mul_eq_zero_comm`), and
  `a b = 0` iff `i ⊕ j = k ⊕ l` plus two sign conditions (`prodZ_eq_zero_iff`).

## Graph structure (`MutualAnnihilationStructure.lean`)

* 168 vertices, 8-regular, 672 edges.
* `zdIso : sevenCopies ≃g zdGraph` — explicit isomorphism with 7 disjoint copies of
  `C₆[4]` (`hexBlowup` = hexagon with each vertex replaced by 4 independent twins).
* Reachability ⇔ equal XOR charge `i ⊕ j`; exactly 7 components; every component
  (24 vertices) is isomorphic to `C₆[4]`.

## Spectrum (`MutualAnnihilationSpectrum.lean`)

* Eigenvalues of `C₆[4]`, of every component and of the whole graph: exactly
  `{8, 4, 0, −4, −8}` (explicit eigenvectors + the identity
  `(μ²−64)(μ²−16)·S = Σ c_y(μ) E_y` on class sums).
* `8` is simple on `C₆[4]` (eigenvectors = constants, via the Laplacian kernel); on the whole
  graph its eigenvectors are the vectors constant on components (multiplicity 7).
  Hence `λ₂ = 4` for each component.
* Ramanujan: every nontrivial eigenvalue has `|μ| ≤ 4 < 2√7`, and `5.2915 < 2√7 < 5.2916`.

## Associator centralizer (`AssociatorCentralizer.lean`, `AssociatorQuaternion.lean`)

`H(a,b) = {x | (a x) b = a (x b)}`. For every annihilating pair `a b = 0` of the 168 zero
divisors (with `a = ±eᵢ±e₈₊ⱼ`, `b = ±e_k±e₈₊ₗ`, `m = i ⊕ k`):

* `H(a,b) = span{1, e_m, e₈, e₈₊ₘ}` and `dim H(a,b) = 4`;
* `q ↦ q₀ + q₁e_m + q₂e₈ + q₃e₈₊ₘ` is an injective unital algebra map `ℍ → 𝕊` with image
  `H(a,b)`; so `H(a,b)` is a unital, product-closed, associative subalgebra isomorphic to `ℍ`.

Proof method: `[a, x, b]_d = x_{d⊕m}A_{d⊕m} + x_{d⊕(8+m')}B_{d⊕(8+m')}` for explicit integer
coefficients (`assoc_crossVec_apply`); a finite certificate (`KerCert`), checked by the kernel
for every sign-normalised annihilating pair, pins the kernel down to the four indices.

## Scope and caveats

* `H_(a,b)` was not defined in the request; the definition above was chosen. Requiring
  additionally `[a,b,x] = [x,a,b] = 0` gives a 2-dimensional space instead (checked
  numerically only, not in Lean).
* The theorems concern the 168 two-term zero divisors `±eᵢ±e₈₊ⱼ`, not arbitrary sedenion
  zero divisors.
* Nothing about the security of a key-exchange protocol ("NA-ZD-KEX") is claimed or proved;
  only the algebraic facts listed above.
* On the full (disconnected) graph the top eigenvalue 8 has multiplicity 7, so "λ₂ = 4" is
  the statement for each component; for the whole graph the statement is that every
  eigenvalue other than ±8 has absolute value at most 4.
