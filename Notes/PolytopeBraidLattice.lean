module

public import Mathlib

@[expose] public section

/-!
# Checks of the concrete claims in `stuff.md` (2026-10-19)

`stuff.md` mixes standard mathematics, testable numerical claims and statements that are not
mathematics. This file checks the testable ones that the corpus did not already cover. Report:
`docs/STUFF_TRIAGE_2026-10-19.md`.

1. **Root systems have even size** (`even_card_of_neg_closed`, `even_card_of_reflection_closed`,
   `reflection_closed_card_ne_21`). Every finite set of non-zero vectors that is closed under
   the reflections in its own members is closed under `v ↦ -v`, so it has an even number of
   elements. The claimed "closed 21-vector orbit" from the letters טסאצ cannot be such a set.
2. **Weyl-group orbits in `ℝ⁸` have even size** (`negChain_eq`, `weyl_closed_even`,
   `weyl_closed_card_ne_21`). Eight reflections in mutually orthogonal roots `e_i ± e_j` of
   `D₈ ⊂ E₈` compose to `v ↦ -v`. Hence every finite set of non-zero vectors closed under the
   reflections of `D₈` (in particular every orbit of the Weyl group of `E₈`) has even size. No
   Weyl orbit of a non-zero vector has 21 elements.
3. **Permutahedron and braids** (`orderOf_swap_mul_swap_adjacent`,
   `orderOf_swap_mul_swap_disjoint`, `permFaces_values`, `perm_euler`,
   `perm_twoFaces_hex_square`). The vertices of the permutahedron `Perm_n` are the permutations
   of `n` letters and its edges are the adjacent transpositions `sᵢ`. A 2-face is a coset of a
   subgroup `⟨sᵢ, sⱼ⟩`, a polygon with `2 · orderOf (sᵢ sⱼ)` sides: a **hexagon** when `j = i+1`
   (order 3, the braid relation `sᵢ sᵢ₊₁ sᵢ = sᵢ₊₁ sᵢ sᵢ₊₁`) and a **square** otherwise
   (order 2, the commutation relation). Faces of `Perm_n` of dimension `k` are ordered set
   partitions of `{1, …, n}` into `n - k` blocks (`permFaces`); the face numbers are checked for
   `n ≤ 5`, and the number of 2-faces equals `(n-2) · n!/6` hexagons plus
   `C(n-2, 2) · n!/4` squares.
4. **The `j`-function coefficient `196884`** (`j_coeffs_from_E4`). From
   `E₄ = 1 + 240 q + 2160 q² + …` (the theta series of `E₈`: 240 roots, 2160 vectors of norm 4)
   and `Δ = q ∏ (1 - qᵐ)²⁴`, the identity `E₄³ = Δ · (q⁻¹ + 744 + 196884 q + …)` holds through
   order `q²`. The number `196884 = 1 + 196883` therefore comes from the `E₈` lattice alone; no
   text corpus enters. The character of the `E₈` lattice vertex algebra itself is
   `E₄/η⁸ = q^{-1/3}(1 + 248 q + 4124 q² + …)` (`e8_vertexAlgebra_character`): its first
   non-trivial coefficient is `248 = dim E₈`, not `196884`.
5. **One-loop cosmohedron numbers** (`oneLoopCosmo_edges_forced`, `oneLoopCosmo_not_simple`).
   For a 3-dimensional polytope with 108 vertices and 62 facets, Euler's relation forces exactly
   168 edges, and `2 · 168 > 3 · 108`, so the polytope is not simple. The edge count 168 carries
   no information beyond the vertex and facet counts.
-/

namespace QBX.Notes.PolytopeBraidLattice

open Matrix Equiv

/-! ## 1. Root systems have even size -/

/-- In an additive group without 2-torsion, a finite set closed under negation that does not
contain `0` has even size. -/
theorem even_card_of_neg_closed {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h2 : ∀ x : G, x + x = 0 → x = 0) :
    ∀ (S : Finset G), (0 : G) ∉ S → (∀ x ∈ S, -x ∈ S) → Even S.card := by
  intro S
  induction h : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    intro h0 hneg
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp at h; simp [← h]
    have hxn : -x ∈ S := hneg x hx
    have hne : x ≠ -x := by
      intro he
      exact h0 (h2 x (by nth_rewrite 2 [he]; simp) ▸ hx)
    set T := (S.erase x).erase (-x) with hT
    have hcard : T.card + 2 = n := by
      rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm, hxn⟩),
        Finset.card_erase_of_mem hx, ← h]
      have : 2 ≤ S.card := by
        have : ({x, -x} : Finset G) ⊆ S := by
          intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
        simpa [Finset.card_pair hne] using Finset.card_le_card this
      omega
    have hTe : Even T.card := by
      refine ih T.card (by omega) T rfl ?_ ?_
      · intro hm; exact h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
      · intro y hy
        simp only [hT, Finset.mem_erase] at hy ⊢
        obtain ⟨h1, h2', h3⟩ := hy
        refine ⟨?_, ?_, hneg y h3⟩
        · intro e; exact h2' (neg_injective e)
        · intro e; apply h1; rw [← e, neg_neg]
    rw [← hcard]; exact hTe.add even_two

section Reflection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orthogonal reflection of `v` in the hyperplane perpendicular to `α`. -/
noncomputable def refl (α v : V) : V := v - (2 * inner ℝ v α / inner ℝ α α) • α

/-- A reflection sends its own root to its negative. -/
theorem refl_self {α : V} (hα : α ≠ 0) : refl α α = -α := by
  have h : inner ℝ α α ≠ (0 : ℝ) := inner_self_ne_zero.2 hα
  simp only [refl]
  rw [mul_div_assoc, div_self h, mul_one, two_smul]
  abel

/-- **Root systems have even size.** A finite set of non-zero vectors that is closed under the
reflections in its own members has an even number of elements. -/
theorem even_card_of_reflection_closed (S : Finset V) (h0 : (0 : V) ∉ S)
    (hS : ∀ α ∈ S, ∀ v ∈ S, refl α v ∈ S) : Even S.card := by
  classical
  refine even_card_of_neg_closed (fun x hx => ?_) S h0 (fun x hx => ?_)
  · have : (2 : ℝ) • x = 0 := by rw [two_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · have hx0 : x ≠ 0 := fun e => h0 (e ▸ hx)
    simpa [refl_self hx0] using hS x hx x hx

/-- In particular, no root system (in the sense above) has 21 elements. -/
theorem reflection_closed_card_ne_21 (S : Finset V) (h0 : (0 : V) ∉ S)
    (hS : ∀ α ∈ S, ∀ v ∈ S, refl α v ∈ S) : S.card ≠ 21 := by
  intro h
  have := even_card_of_reflection_closed S h0 hS
  rw [h] at this
  exact absurd this (by decide)

end Reflection

/-! ## 2. Weyl-group orbits in `ℝ⁸` have even size -/

/-- The reflection `v ↦ v - ⟨v, α⟩ α` in a root `α` with `⟨α, α⟩ = 2`. -/
def sref (α v : Fin 8 → ℝ) : Fin 8 → ℝ := v - (v ⬝ᵥ α) • α

/-- The `D₈` root `e_i + s e_j` (an `E₈` root when `i ≠ j` and `s = ±1`). -/
def d8root (i j : Fin 8) (s : ℝ) : Fin 8 → ℝ :=
  fun k => (if k = i then 1 else 0) + (if k = j then s else 0)

theorem dot_d8root (v : Fin 8 → ℝ) (i j : Fin 8) (s : ℝ) :
    v ⬝ᵥ d8root i j s = v i + s * v j := by
  simp [dotProduct, d8root, mul_add, Finset.sum_add_distrib, mul_comm]

/-- The roots `e_i ± e_j` (`i ≠ j`) have squared length 2. -/
theorem d8root_norm (i j : Fin 8) (hij : i ≠ j) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    d8root i j s ⬝ᵥ d8root i j s = 2 := by
  rw [dot_d8root]
  simp only [d8root, if_true, if_neg hij, if_neg (Ne.symm hij)]
  rcases hs with rfl | rfl <;> norm_num

/-- Reflecting in `e_i - e_j` and then in `e_i + e_j` negates coordinates `i` and `j`. -/
theorem sref_pair (v : Fin 8 → ℝ) (i j : Fin 8) (hij : i ≠ j) :
    sref (d8root i j 1) (sref (d8root i j (-1)) v) =
      fun k => if k = i ∨ k = j then -v k else v k := by
  ext k
  simp only [sref, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [dot_d8root, dot_d8root]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, d8root]
  by_cases hi : k = i <;> by_cases hj : k = j <;> subst_vars <;> simp_all [Ne.symm hij]

/-- Eight reflections in the mutually orthogonal roots `e₀ ± e₁, e₂ ± e₃, e₄ ± e₅, e₆ ± e₇`. -/
def negChain (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  sref (d8root 6 7 1) (sref (d8root 6 7 (-1)) (sref (d8root 4 5 1) (sref (d8root 4 5 (-1))
    (sref (d8root 2 3 1) (sref (d8root 2 3 (-1)) (sref (d8root 0 1 1)
      (sref (d8root 0 1 (-1)) v)))))))

/-- **`-1` lies in the Weyl group of `D₈` (hence of `E₈`):** the eight reflections compose to
`v ↦ -v`. -/
theorem negChain_eq (v : Fin 8 → ℝ) : negChain v = -v := by
  simp only [negChain, sref_pair _ _ _ (by decide : (0 : Fin 8) ≠ 1),
    sref_pair _ _ _ (by decide : (2 : Fin 8) ≠ 3), sref_pair _ _ _ (by decide : (4 : Fin 8) ≠ 5),
    sref_pair _ _ _ (by decide : (6 : Fin 8) ≠ 7)]
  ext k
  fin_cases k <;> simp

/-- **Weyl-invariant sets in `ℝ⁸` have even size.** A finite set of non-zero vectors that is
closed under the reflections in all roots `e_i ± e_j` (for example, any orbit of the Weyl group
of `E₈`, which contains these reflections) is closed under negation and has even size. -/
theorem weyl_closed_even (S : Finset (Fin 8 → ℝ)) (h0 : (0 : Fin 8 → ℝ) ∉ S)
    (hS : ∀ i j : Fin 8, i ≠ j → ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ v ∈ S, sref (d8root i j s) v ∈ S) :
    Even S.card := by
  classical
  refine even_card_of_neg_closed (fun x hx => ?_) S h0 (fun x hx => ?_)
  · have : (2 : ℝ) • x = 0 := by rw [two_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · rw [← negChain_eq]
    have p : ∀ i j : Fin 8, i ≠ j → ∀ v ∈ S,
        sref (d8root i j 1) (sref (d8root i j (-1)) v) ∈ S := fun i j hij v hv =>
      hS i j hij 1 (Or.inl rfl) _ (hS i j hij (-1) (Or.inr rfl) v hv)
    exact p 6 7 (by decide) _ (p 4 5 (by decide) _ (p 2 3 (by decide) _
      (p 0 1 (by decide) _ hx)))

/-- No Weyl-invariant set of non-zero vectors in `ℝ⁸` has 21 elements. -/
theorem weyl_closed_card_ne_21 (S : Finset (Fin 8 → ℝ)) (h0 : (0 : Fin 8 → ℝ) ∉ S)
    (hS : ∀ i j : Fin 8, i ≠ j → ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ v ∈ S, sref (d8root i j s) v ∈ S) :
    S.card ≠ 21 := by
  intro h
  have := weyl_closed_even S h0 hS
  rw [h] at this
  exact absurd this (by decide)

/-! ## 3. Permutahedron and braids -/

/-- Adjacent transpositions `swap a b`, `swap b c` multiply to a 3-cycle: the hexagonal 2-faces
of the permutahedron, i.e. the braid relation. -/
theorem orderOf_swap_mul_swap_adjacent {α : Type*} [Fintype α] [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : orderOf (swap a b * swap b c) = 3 := by
  rw [swap_comm a b]
  exact (Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac).orderOf

/-- Disjoint transpositions multiply to an element of order 2: the square 2-faces of the
permutahedron, i.e. the commutation relation. -/
theorem orderOf_swap_mul_swap_disjoint {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    orderOf (swap a b * swap c d) = 2 := by
  have hcomm : Commute (swap a b) (swap c d) := by
    refine Perm.Disjoint.commute ?_
    intro x
    by_cases h1 : x = a
    · right; subst h1; exact swap_apply_of_ne_of_ne hac had
    by_cases h2 : x = b
    · right; subst h2; exact swap_apply_of_ne_of_ne hbc hbd
    · left; exact swap_apply_of_ne_of_ne h1 h2
  apply orderOf_eq_prime
  · rw [hcomm.mul_pow, sq, sq, Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  · intro h
    have := congrArg (fun f : Perm α => f a) h
    simp [swap_apply_of_ne_of_ne hac had] at this
    exact hab this.symm

/-- Faces of dimension `k` of the permutahedron `Perm_n` are the ordered set partitions of
`n` letters into `n - k` blocks, i.e. the surjections `Fin n → Fin (n - k)`. -/
def permFaces (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin (n - k) => Function.Surjective f)).card

/-- Face numbers `f₀, f₁, …` of `Perm_3` (hexagon), `Perm_4` (truncated octahedron) and
`Perm_5`. -/
theorem permFaces_values :
    (List.range 3).map (permFaces 3) = [6, 6, 1] ∧
    (List.range 4).map (permFaces 4) = [24, 36, 14, 1] ∧
    (List.range 5).map (permFaces 5) = [120, 240, 150, 30, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Euler–Poincaré for `Perm_n`, `n = 3, 4, 5` (the polytope itself counted in top degree). -/
theorem perm_euler :
    ∀ n ∈ [3, 4, 5], ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (permFaces n k : ℤ) = 1 := by
  decide +kernel

/-- The 2-faces of `Perm_n` are `(n-2) · n!/6` hexagons (one per coset of `⟨sᵢ, sᵢ₊₁⟩`) plus
`C(n-2, 2) · n!/4` squares (one per coset of `⟨sᵢ, sⱼ⟩`, `|i - j| ≥ 2`), for `n = 3, 4, 5`. -/
theorem perm_twoFaces_hex_square :
    ∀ n ∈ [3, 4, 5],
      permFaces n 2 = (n - 2) * (n.factorial / 6) + (n - 2).choose 2 * (n.factorial / 4) := by
  decide +kernel

/-- Every vertex of `Perm_n` lies on `n - 1` edges (one per adjacent transposition). -/
theorem perm_edges_eq :
    ∀ n ∈ [3, 4, 5], 2 * permFaces n 1 = (n - 1) * permFaces n 0 := by
  decide +kernel

/-! ## 4. The `j`-function coefficient `196884` -/

/-- Truncated product of power series given by coefficient lists. -/
def pmul (N : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range N).map fun n =>
    ((List.range (n + 1)).map fun i => a.getD i 0 * b.getD (n - i) 0).sum

/-- Coefficients of `E₄ = 1 + 240 ∑ σ₃(n) qⁿ` through `q²`. -/
def e4 : List ℤ := [1, 240 * (ArithmeticFunction.sigma 3 1 : ℤ),
  240 * (ArithmeticFunction.sigma 3 2 : ℤ)]

/-- Coefficients of `∏_{m ≥ 1} (1 - qᵐ)²⁴ = Δ / q` through `q²`. -/
def deltaOverQ : List ℤ :=
  pmul 3 ((List.replicate 24 [1, -1, 0]).foldr (pmul 3) [1])
    ((List.replicate 24 [1, 0, -1]).foldr (pmul 3) [1])

theorem e4_values : e4 = [1, 240, 2160] := by
  simp [e4, ArithmeticFunction.sigma_apply, Nat.divisors]
  decide

theorem deltaOverQ_values : deltaOverQ = [1, -24, 252] := by decide +kernel

/-- **`E₄³ = Δ · (q⁻¹ + 744 + 196884 q + …)` through order `q²`.** Dividing by `q`, this says
`E₄³ ≡ (Δ/q)·(1 + 744 q + 196884 q²)` modulo `q³`; so the coefficients `744` and `196884` of the
`j`-function are determined by the `E₈` theta series `E₄`. -/
theorem j_coeffs_from_E4 :
    pmul 3 e4 (pmul 3 e4 e4) = pmul 3 deltaOverQ [1, 744, 196884] := by
  rw [e4_values]; decide +kernel

/-- Coefficients of `∏_{m ≥ 1} (1 - qᵐ)⁸ = η⁸ / q^{1/3}` through `q²`. -/
def eta8 : List ℤ :=
  pmul 3 ((List.replicate 8 [1, -1, 0]).foldr (pmul 3) [1])
    ((List.replicate 8 [1, 0, -1]).foldr (pmul 3) [1])

/-- **The character of the `E₈` lattice vertex algebra starts `1 + 248 q + 4124 q²`.**
`[1, 8, 44]` is the inverse of `η⁸/q^{1/3}` modulo `q³`, and `E₄ · [1, 8, 44] = [1, 248, 4124]`.
The weight-one coefficient `248 = 240 + 8` is the dimension of the Lie algebra `E₈` (240 roots
plus an 8-dimensional Cartan subalgebra). The number `196884` does not occur here: it is a
coefficient of `E₄³/Δ`, i.e. of the 24-dimensional lattice `E₈³` (`j_coeffs_from_E4`). -/
theorem e8_vertexAlgebra_character :
    eta8 = [1, -8, 20] ∧ pmul 3 eta8 [1, 8, 44] = [1, 0, 0] ∧
      pmul 3 e4 [1, 8, 44] = [1, 248, 4124] := by
  rw [e4_values]; refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 5. One-loop cosmohedron numbers -/

/-- For a 3-polytope with 108 vertices and 62 facets, Euler's relation `V - E + F = 2` holds
exactly when there are 168 edges. -/
theorem oneLoopCosmo_edges_forced (E : ℤ) : 108 - E + 62 = 2 ↔ E = 168 := by
  constructor <;> intro h <;> omega

/-- A simple 3-polytope has `2E = 3V`; here `2 · 168 > 3 · 108`, so the one-loop
cosmohedron at three points is not simple (some vertex lies on at least four edges). -/
theorem oneLoopCosmo_not_simple : 3 * 108 < 2 * 168 := by norm_num

end QBX.Notes.PolytopeBraidLattice
