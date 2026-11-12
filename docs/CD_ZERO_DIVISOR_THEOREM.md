# The universal Cayley–Dickson cross-half zero-divisor theorem

All statements below are proved in Lean with no `sorry` and no `native_decide`. They depend
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound` (checked with
`#print axioms`).

| File | Content |
|---|---|
| `Sovereign/Algebra/CrossHalfCriterion.lean` | sign laws; the zero-divisor criterion for every `D ≥ 16` |
| `Sovereign/Algebra/CrossHalfComponents.lean` | edge law, zero divisors in the algebra, count, charge sectors |
| `Sovereign/Algebra/CrossHalfConnectivity.lean` | every charge sector is connected |
| `Sovereign/Algebra/CrossHalfZeroDivisorTheorem.lean` | headline theorems, `PG(n-2, 𝔽₂)`, the `T₃₂` hyperplane fibration |

## Setting

`Tower n` is the Cayley–Dickson algebra of dimension `D = 2ⁿ`, built over `ℤ` by iterated
doubling (`Sovereign/Algebra/TowerBasis.lean`). Write `H = D/2`. A **cross-half vector** is
`± eᵢ ± e_{H+j}` with `i, j < H` (`crossVec`). Such a vector is labelled `((i, j), (s, t))`,
where the Booleans `s, t` record the two signs. It is a **cross-half zero divisor**
(`IsCrossZD`, `crossZD`) if it left-annihilates some non-zero cross-half vector. The
**annihilation graph** `annihGraph` joins two distinct in-range labels `x, y` when
`x·y = 0` or `y·x = 0`. The **charge** of a label is `i XOR j`.

All products of these vectors have integer coefficients. So the same vanishing statements
hold in the real Cayley–Dickson algebras.

## Universal results (`D = 2ⁿ ≥ 16`)

1. **Criterion** (`crossVec_zeroDivisor_iff`): `± eᵢ ± e_{H+j}` is a cross-half zero divisor
   exactly when `i ≠ 0`, `j ≠ 0` and `i ≠ j`.
   * Before this run, this was known only by evaluation for `D = 16, 32, 64, 128`.
   * The proof reduces the problem to a sign-free index condition `crossOK`.
   * Necessity uses the sign laws `eₚ(eₚ e_q) = −e_q` and `(eₚ e_q)e_q = −eₚ`
     (`epsNeg_xor_laws`, proved by induction on the level).
   * Sufficiency gives an explicit partner index in every case, by induction on the level.
     The sedenion case is the base and is checked by `decide`.
2. **Count** (`crossZD_card`): there are exactly `(D − 2)(D − 4)` of them.
3. **Charge preserved** (`reachable_mem`): annihilation, in either order, preserves the
   charge and never leaves the set of zero divisors.
4. **Components** (`reachable_iff`): two zero divisors are in the same connected component
   exactly when they have the same charge.
   * The proof uses explicit spanning edges.
   * It also uses an explicit triangle whose three sign parities add up to an odd number.
   * This is done uniformly for the three kinds of charge: `c < D/4`, `c = D/4` and
     `c > D/4`.
5. **Headline** (`universal_cd_zero_divisor_theorem`):
   * `(crossZD (n-1)).card = (2ⁿ − 2)(2ⁿ − 4)`;
   * `(components (n-1)).card = Nat.card ℙ(𝔽₂^{n-1}) = |PG(n−2, 𝔽₂)|`;
   * `|PG(n−2, 𝔽₂)| = 2ⁿ⁻¹ − 1` (from Mathlib's `Projectivization.card''`);
   * every component has `2(D − 4)` elements.
6. **Fibration over `PG(n−2, 𝔽₂)`** (`card_preimage`): for any set `S` of non-zero charges,
   exactly `|S| · 2(D − 4)` zero divisors have their charge in `S`.

## `T₃₂` (`D = 32`): `trigintaduonion_zero_divisor_theorem`

* There are 840 cross-half zero divisors.
* They form exactly 15 components of 56 elements each, and `|PG(3, 2)| = 15`.
* **Hyperplane fibration.** A hyperplane is `H_a = {c : ⟨a, c⟩ = 0 over 𝔽₂}` for a non-zero
  functional `a`.
  * Each of the 15 hyperplanes is a Fano plane with 7 points (`hyperplane_card_32`).
  * Distinct `a` give distinct hyperplanes (`hyperplane_injective_32`).
  * Over each hyperplane lie exactly `392 = 7·56` zero divisors, and `448 = 8·56` lie off it.
  * Every zero divisor lies over exactly 7 of the 15 hyperplanes (`point_on_hyperplanes_32`).

## Scope and caveats

* "Zero divisor" means a **cross-half** zero divisor `± eᵢ ± e_{D/2+j}` that annihilates a
  non-zero **cross-half** vector. The count is of these signed vectors. Zero divisors of other
  shapes are not classified here.
* The components are those of the annihilation graph on cross-half vectors. The component of
  a zero divisor contains only zero divisors (`reachable_mem`).
* The general hyperplane count (each hyperplane of `PG(n−2, 𝔽₂)` has `2ⁿ⁻² − 1` points) is
  proved only for `D = 32`, by evaluation. The general fibration `card_preimage` holds for
  every set of points.
