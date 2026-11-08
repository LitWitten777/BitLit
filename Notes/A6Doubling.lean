module

public import Mathlib

@[expose] public section

/-!
# The 21 vectors and their 42-element "dual": the root system `A₆`

Follow-up to `QBX.Notes.PolytopeBraidLattice`, which showed that no reflection-closed set (and
no Weyl orbit in `ℝ⁸`) has 21 elements. The natural repair is to double: 21 vectors together
with their negatives give 42, and the 21 vectors are then the **positive roots** of a root system
with 42 roots. This file checks that this works, and for which root system.

* `card_roots_seven`, `card_posRoots_seven`, `roots_eq_pos_union_neg`, `card_roots_eq_two_mul`:
  the vectors `e_i - e_j` (`i ≠ j`) in `ℤ⁷` are 42 roots of `A₆`; the 21 with `i < j` are the
  positive roots and the other 21 are exactly their negatives.
* `refl_mem_roots`, `neg_mem_roots`, `ip_self_roots`, `ip_roots_bound`: it is a crystallographic
  root system. The reflection in `e_i - e_j` is the transposition `i ↔ j` of coordinates
  (`refl_aroot`), so the 21 positive-root reflections are the 21 transpositions of `S₇`, the
  Weyl group. All roots have length² 2, so the coroots are the roots: `A₆` is self-dual.
* `neg_not_perm`: unlike `E₈`, negation is not in the Weyl group, so the 21 ↔ 21 pairing is a
  symmetry of the root system that is not a product of its reflections.
* `irreducible_count_42`: among the irreducible root systems (`Aᵣ, Bᵣ, Cᵣ, Dᵣ, E₆₋₈, F₄, G₂`),
  only `A₆` has 42 roots. (The classification itself is not formalized; this checks the count
  formulas.) `A₆` is simply laced, i.e. of type ADE.
* `fano_partition_roots`, `roots_seven_eq_biUnion`, `refl_mem_subRoots`, `card_subRoots_line`:
  the seven Fano lines split the 42 roots into seven `A₂` subsystems of 6 roots each (21 positive
  roots = 7 lines × 3 pairs), because every pair of points lies on exactly one line.
* `a6_sub_e8`: placed on the first seven coordinates of `ℝ⁸`, the 42 roots are `E₈` roots.
-/

namespace QBX.Notes.A6Doubling

open Equiv

variable {n : ℕ}

/-- Integer dot product on `ℤⁿ`. -/
def ip (v w : Fin n → ℤ) : ℤ := ∑ k, v k * w k

/-- The root `e_i - e_j` of type `A`. -/
def aroot (i j : Fin n) : Fin n → ℤ := Pi.single i 1 - Pi.single j 1

/-- The reflection `v ↦ v - ⟨v, α⟩ α`. -/
def refl (a v : Fin n → ℤ) : Fin n → ℤ := v - ip v a • a

theorem ip_aroot (v : Fin n → ℤ) (i j : Fin n) : ip v (aroot i j) = v i - v j := by
  simp [ip, aroot, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem refl_aroot (i j : Fin n) (h : i ≠ j) (v : Fin n → ℤ) :
    refl (aroot i j) v = v ∘ swap i j := by
  funext k
  rw [refl, ip_aroot]
  simp only [aroot, Pi.sub_apply, Pi.smul_apply, Pi.single_apply,
    Function.comp_apply, swap_apply_def, smul_eq_mul]
  by_cases hi : k = i
  · subst hi; simp [h]
  · by_cases hj : k = j
    · subst hj; simp [hi]
    · simp [hi, hj]

theorem aroot_comp_swap (i j k l : Fin n) :
    aroot k l ∘ swap i j = aroot (swap i j k) (swap i j l) := by
  funext m
  simp only [aroot, Function.comp_apply, Pi.sub_apply, Pi.single_apply]
  congr 1 <;> congr 1 <;> apply propext <;> constructor <;> intro h <;>
    first | (rw [← h]; simp) | (rw [h]; simp)

theorem aroot_apply (i j m : Fin n) :
    aroot i j m = (if m = i then 1 else 0) - (if m = j then 1 else 0) := by
  simp [aroot, Pi.single_apply]

theorem aroot_inj {i j k l : Fin n} (hij : i ≠ j) (h : aroot i j = aroot k l) :
    i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [aroot_apply, if_neg hij, if_neg (Ne.symm hij)] at hi hj
  constructor
  · by_contra hne
    rw [if_neg hne] at hi
    split_ifs at hi <;> omega
  · by_contra hne
    rw [if_neg hne] at hj
    split_ifs at hj <;> omega

theorem neg_aroot (i j : Fin n) : -aroot i j = aroot j i := by
  simp [aroot]

/-! ## The root system `A_{n-1}` -/

/-- All roots `e_i - e_j`, `i ≠ j`. -/
def roots (n : ℕ) : Finset (Fin n → ℤ) :=
  (Finset.univ.offDiag).image (fun p : Fin n × Fin n => aroot p.1 p.2)

/-- The positive roots `e_i - e_j`, `i < j`. -/
def posRoots (n : ℕ) : Finset (Fin n → ℤ) :=
  ((Finset.univ.offDiag).filter (fun p : Fin n × Fin n => p.1 < p.2)).image
    (fun p => aroot p.1 p.2)

theorem mem_roots {a : Fin n → ℤ} : a ∈ roots n ↔ ∃ i j, i ≠ j ∧ aroot i j = a := by
  simp [roots]

theorem mem_posRoots {a : Fin n → ℤ} : a ∈ posRoots n ↔ ∃ i j, i < j ∧ aroot i j = a := by
  simp only [posRoots, Finset.mem_image, Finset.mem_filter, Finset.mem_offDiag,
    Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨-, h⟩, rfl⟩; exact ⟨i, j, h, rfl⟩
  · rintro ⟨i, j, h, rfl⟩; exact ⟨i, j, ⟨h.ne, h⟩, rfl⟩

theorem card_roots (n : ℕ) : (roots n).card = n * n - n := by
  rw [roots, Finset.card_image_of_injOn, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  rintro ⟨i, j⟩ hp ⟨k, l⟩ hq h
  simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.coe_univ, Set.mem_univ,
    true_and] at hp hq
  obtain ⟨rfl, rfl⟩ := aroot_inj hp h
  rfl

theorem card_posRoots_eq (n : ℕ) :
    (posRoots n).card = ((Finset.univ.offDiag).filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
  rw [posRoots, Finset.card_image_of_injOn]
  rintro ⟨i, j⟩ hp ⟨k, l⟩ hq h
  simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hp hq
  obtain ⟨rfl, rfl⟩ := aroot_inj hp.1 h
  rfl

/-- **`A₆` has 42 roots.** -/
theorem card_roots_seven : (roots 7).card = 42 := by
  rw [card_roots]

/-- **`A₆` has 21 positive roots.** -/
theorem card_posRoots_seven : (posRoots 7).card = 21 := by
  rw [card_posRoots_eq]; decide

/-- The negatives of the positive roots. -/
def negRoots (n : ℕ) : Finset (Fin n → ℤ) := (posRoots n).image (fun a => -a)

/-- **The 42 = 21 + 21 split.** Every root is positive or the negative of a positive root, and
not both. -/
theorem roots_eq_pos_union_neg (n : ℕ) :
    roots n = posRoots n ∪ negRoots n ∧ Disjoint (posRoots n) (negRoots n) := by
  constructor
  · ext a
    simp only [Finset.mem_union, mem_roots, mem_posRoots, negRoots, Finset.mem_image]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl ⟨i, j, h, rfl⟩
      · exact Or.inr ⟨aroot j i, ⟨j, i, h, rfl⟩, neg_aroot j i⟩
    · rintro (⟨i, j, h, rfl⟩ | ⟨b, ⟨i, j, h, rfl⟩, rfl⟩)
      · exact ⟨i, j, h.ne, rfl⟩
      · exact ⟨j, i, h.ne', (neg_aroot i j).symm⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_posRoots, negRoots, Finset.mem_image] at ha hb
    obtain ⟨i, j, hij, rfl⟩ := ha
    obtain ⟨b, ⟨k, l, hkl, rfl⟩, h⟩ := hb
    rw [neg_aroot] at h
    obtain ⟨rfl, rfl⟩ := aroot_inj hkl.ne' h
    exact absurd (hij.trans hkl) (lt_irrefl _)

theorem card_negRoots (n : ℕ) : (negRoots n).card = (posRoots n).card :=
  Finset.card_image_of_injective _ neg_injective

/-- `|Φ| = 2 |Φ⁺|`: the negatives are the "dual half". -/
theorem card_roots_eq_two_mul (n : ℕ) : (roots n).card = 2 * (posRoots n).card := by
  obtain ⟨h1, h2⟩ := roots_eq_pos_union_neg n
  rw [h1, Finset.card_union_of_disjoint h2, card_negRoots]; ring

/-- Closed under negation. -/
theorem neg_mem_roots {a : Fin n → ℤ} (ha : a ∈ roots n) : -a ∈ roots n := by
  obtain ⟨i, j, hij, rfl⟩ := mem_roots.1 ha
  exact mem_roots.2 ⟨j, i, hij.symm, (neg_aroot i j).symm⟩

/-- **Closed under its own reflections** (a root system). The reflection in `e_i - e_j` is the
transposition of coordinates `i ↔ j`. -/
theorem refl_mem_roots {a b : Fin n → ℤ} (ha : a ∈ roots n) (hb : b ∈ roots n) :
    refl a b ∈ roots n := by
  obtain ⟨i, j, hij, rfl⟩ := mem_roots.1 ha
  obtain ⟨k, l, hkl, rfl⟩ := mem_roots.1 hb
  rw [refl_aroot i j hij, aroot_comp_swap]
  exact mem_roots.2 ⟨_, _, (swap i j).injective.ne hkl, rfl⟩

/-- Every root has squared length 2, so the coroot `2α/⟨α,α⟩` equals `α`: the system is
**self-dual** (`A₆^∨ = A₆`). -/
theorem ip_self_roots {a : Fin n → ℤ} (ha : a ∈ roots n) : ip a a = 2 := by
  obtain ⟨i, j, hij, rfl⟩ := mem_roots.1 ha
  rw [ip_aroot]
  simp [aroot_apply, hij, Ne.symm hij]

/-- **Crystallographic**: all Cartan integers `⟨β, α⟩` lie in `[-2, 2]`. -/
theorem ip_roots_bound {a b : Fin n → ℤ} (ha : a ∈ roots n) (hb : b ∈ roots n) :
    -2 ≤ ip b a ∧ ip b a ≤ 2 := by
  obtain ⟨i, j, -, rfl⟩ := mem_roots.1 ha
  obtain ⟨k, l, hkl, rfl⟩ := mem_roots.1 hb
  rw [ip_aroot]
  simp only [aroot_apply]
  split_ifs <;> simp_all

/-- Negation is **not** in the Weyl group `Sₙ` of `A_{n-1}` (`n ≥ 1`): no coordinate permutation
sends every vector to its negative. (Contrast with `E₈`, where `-1` is a product of eight
reflections, `PolytopeBraidLattice.negChain_eq`.) The 21 ↔ 21 pairing of `A₆` is therefore an
outer symmetry, not a Weyl element. -/
theorem neg_not_perm (hn : 0 < n) : ¬ ∃ σ : Perm (Fin n), ∀ v : Fin n → ℤ, v ∘ σ = -v := by
  rintro ⟨σ, h⟩
  have := congrFun (h fun _ => 1) ⟨0, hn⟩
  simp at this

/-! ## Which irreducible root systems have 42 roots? -/

/-- Root counts of the irreducible root systems: `A_r: r(r+1)`, `B_r, C_r: 2r²`,
`D_r: 2r(r-1)`, `E₆: 72`, `E₇: 126`, `E₈: 240`, `F₄: 48`, `G₂: 12`. -/
theorem irreducible_count_42 :
    (∀ r : ℕ, 1 ≤ r → (r * (r + 1) = 42 ↔ r = 6)) ∧
    (∀ r : ℕ, 2 * r ^ 2 ≠ 42) ∧
    (∀ r : ℕ, 2 * r * (r - 1) ≠ 42) ∧
    (72 ≠ 42 ∧ 126 ≠ 42 ∧ 240 ≠ 42 ∧ 48 ≠ 42 ∧ 12 ≠ 42) := by
  refine ⟨fun r _ => ⟨fun h => ?_, fun h => by subst h; rfl⟩, fun r h => ?_, fun r h => ?_,
    by decide⟩
  · have : r ≤ 6 := by nlinarith
    interval_cases r <;> omega
  · have : r ≤ 5 := by nlinarith
    interval_cases r <;> omega
  · have : r ≤ 6 := by
      rcases r with _ | r
      · simp at h
      · simp at h; nlinarith
    interval_cases r <;> omega

/-! ## The Fano plane decomposes `A₆` into seven `A₂`'s -/

/-- The seven lines of the Fano plane on the points `0, …, 6` (the octonion units `e₁ … e₇`
shifted down by one; the lines `{i, j, i xor j}`). -/
def fanoLine : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

theorem fanoLine_card : ∀ t, (fanoLine t).card = 3 := by decide

/-- Two distinct points lie on exactly one line. -/
theorem fano_unique_line (i j : Fin 7) (hij : i ≠ j) :
    ∃! t, i ∈ fanoLine t ∧ j ∈ fanoLine t := by
  have hex : ∀ i j : Fin 7, i ≠ j → ∃ t, i ∈ fanoLine t ∧ j ∈ fanoLine t := by decide
  have huniq : ∀ i j t t' : Fin 7, i ≠ j → i ∈ fanoLine t → j ∈ fanoLine t →
      i ∈ fanoLine t' → j ∈ fanoLine t' → t' = t := by decide
  obtain ⟨t, ht⟩ := hex i j hij
  exact ⟨t, ht, fun t' ht' => huniq i j t t' hij ht.1 ht.2 ht'.1 ht'.2⟩

/-- The roots supported on a subset `S` of coordinates. -/
def subRoots (S : Finset (Fin n)) : Finset (Fin n → ℤ) :=
  S.offDiag.image (fun p => aroot p.1 p.2)

theorem mem_subRoots {S : Finset (Fin n)} {a : Fin n → ℤ} :
    a ∈ subRoots S ↔ ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j ∧ aroot i j = a := by
  simp [subRoots, and_assoc]

/-- Roots on a subset form a sub-root-system (closed under its own reflections); on a 3-element
set this is `A₂`, with 6 roots. -/
theorem refl_mem_subRoots {S : Finset (Fin n)} {a b : Fin n → ℤ} (ha : a ∈ subRoots S)
    (hb : b ∈ subRoots S) : refl a b ∈ subRoots S := by
  obtain ⟨i, j, hi, hj, hij, rfl⟩ := mem_subRoots.1 ha
  obtain ⟨k, l, hk, hl, hkl, rfl⟩ := mem_subRoots.1 hb
  rw [refl_aroot i j hij, aroot_comp_swap]
  have hS : ∀ m ∈ S, swap i j m ∈ S := by
    intro m hm; rw [swap_apply_def]; split_ifs <;> assumption
  exact mem_subRoots.2 ⟨_, _, hS k hk, hS l hl, (swap i j).injective.ne hkl, rfl⟩

theorem card_subRoots_line (t : Fin 7) : (subRoots (fanoLine t)).card = 6 := by
  rw [subRoots, Finset.card_image_of_injOn, Finset.offDiag_card, fanoLine_card]
  rintro ⟨i, j⟩ hp ⟨k, l⟩ hq h
  simp only [Finset.coe_offDiag, Set.mem_offDiag] at hp hq
  obtain ⟨rfl, rfl⟩ := aroot_inj hp.2.2 h
  rfl

/-- **The 42 roots of `A₆` split into seven `A₂` subsystems, one per Fano line** (`7 · 6 = 42`;
on positive roots, `7 · 3 = 21`). Every root lies in exactly one of them. -/
theorem fano_partition_roots :
    ∀ a ∈ roots 7, ∃! t, a ∈ subRoots (fanoLine t) := by
  intro a ha
  obtain ⟨i, j, hij, rfl⟩ := mem_roots.1 ha
  obtain ⟨t, ⟨hi, hj⟩, huniq⟩ := fano_unique_line i j hij
  refine ⟨t, mem_subRoots.2 ⟨i, j, hi, hj, hij, rfl⟩, ?_⟩
  intro t' hm
  obtain ⟨k, l, hk, hl, hkl, h⟩ := mem_subRoots.1 hm
  obtain ⟨rfl, rfl⟩ := aroot_inj hkl h
  exact huniq t' ⟨hk, hl⟩

theorem roots_seven_eq_biUnion : roots 7 = Finset.univ.biUnion (fun t => subRoots (fanoLine t)) := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro ha
    obtain ⟨t, h, -⟩ := fano_partition_roots a ha
    exact ⟨t, h⟩
  · rintro ⟨t, h⟩
    obtain ⟨i, j, -, -, hij, rfl⟩ := mem_subRoots.1 h
    exact mem_roots.2 ⟨i, j, hij, rfl⟩

/-! ## `A₆ ⊂ E₈` -/

/-- The Gosset lattice `E₈` in doubled coordinates (`y = 2x`), as in
`Sovereign.Steering.GossetE8`: all `yᵢ` even or all odd, and `4 ∣ ∑ yᵢ`. A root is a lattice
vector with `⟨x, x⟩ = 2`, i.e. `y ⬝ y = 8`. -/
def IsE8Root (y : Fin 8 → ℤ) : Prop :=
  ((∀ i, Even (y i)) ∨ (∀ i, Odd (y i))) ∧ (4 : ℤ) ∣ ∑ i, y i ∧ ip y y = 8

/-- The `A₆` roots, placed on the first seven coordinates of `ℝ⁸`, are `E₈` roots. -/
theorem a6_sub_e8 (i j : Fin 7) (hij : i ≠ j) :
    IsE8Root (2 • aroot (Fin.castSucc i) (Fin.castSucc j)) := by
  have h' : Fin.castSucc i ≠ Fin.castSucc j := Fin.castSucc_injective _ |>.ne hij
  unfold IsE8Root
  refine ⟨Or.inl fun k => ⟨aroot (Fin.castSucc i) (Fin.castSucc j) k, by simp [two_mul]⟩, ?_, ?_⟩
  · simp [aroot, Finset.sum_sub_distrib, ← Finset.mul_sum]
  · have : ip (2 • aroot (Fin.castSucc i) (Fin.castSucc j))
        (2 • aroot (Fin.castSucc i) (Fin.castSucc j)) =
        4 * ip (aroot (Fin.castSucc i) (Fin.castSucc j)) (aroot (Fin.castSucc i) (Fin.castSucc j)) := by
      simp only [ip, Pi.smul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [this, ip_self_roots (mem_roots.2 ⟨_, _, h', rfl⟩)]
    norm_num

end QBX.Notes.A6Doubling
