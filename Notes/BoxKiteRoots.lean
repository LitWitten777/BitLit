module

public import QBX.Formal.BoxKites
public import QBX.Notes.A6GramAudit

@[expose] public section

/-!
# Sedenion box kites as `A₆` roots: box kites are Fano *points*, `A₂` blocks are Fano *lines*

A pasted analysis claimed that "the 168 box-kite structures are indexed by `PSL(2,7)`" and that
"each of the seven `A₂` blocks of `A₆` represents a box kite". This file tests the second claim
against the box-kite structure proved in `QBX.Formal.BoxKites`.

* `QBX.Formal.BoxKites` already shows: 168 primitive zero divisors `±e_a ± e_(8+b)`, falling into
  **7** box kites (connected components, `annGraph_reachable_iff`), with 24 vectors each, and
  42 twin classes of 4. So 168 counts vectors, and there are 7 box kites, not 168.
* `rootOf`, `rootOf_eq_iff`, `image_rootOf`: sending the label `(a, b, s, t)` to the root
  `s t (e_a - e_b)` of `A₆` (indices shifted to `0 … 6`) is constant exactly on twin classes, and
  its image is all of the 42 roots. So **the 42 twin classes correspond one-to-one to the 42
  roots of `A₆`.**
* `kite_eq_xor`: the box kite of a label is the xor `(i+1) xor (j+1)` of its root's indices.
* `same_kite_orth`: two roots in the same box kite are orthogonal or opposite. So each box kite
  is a `3 A₁` (three mutually orthogonal pairs `±r`), **not** an `A₂` (`line_has_sixty`: an `A₂`
  block always contains roots at 60°). `ann_orth`: zero products `u w = 0` only join labels whose
  roots are orthogonal.
* `third_on_line`: the box kite of `e_i - e_j` is the third point of the Fano line through
  `i, j`. So box kites correspond to the 7 **points** of the Fano plane, while the `A₂` blocks of
  `A6Doubling.fano_partition_roots` correspond to the 7 **lines**. Both are partitions of the
  same 42 roots into 7 groups of 6, and they are exchanged by point–line duality.
-/

namespace QBX.Notes.BoxKiteRoots

open QBX.Formal.BoxKites QBX.Notes.A6Doubling QBX.Notes.A6GramAudit

/-- Shift a nonzero index `1 … 7` of `Fin 8` down to `0 … 6`. -/
def down (x : Fin 8) : Fin 7 := ⟨x.val - 1, by omega⟩

/-- The ordered pair of the root attached to a label `(a, b, s, t)`: the root is
`s t (e_a - e_b)`, i.e. `e_a - e_b` if `s = t` and `e_b - e_a` otherwise. -/
def rootPair (l : Label) : Fin 7 × Fin 7 :=
  if l.2.2.1 = l.2.2.2 then (down l.1, down l.2.1) else (down l.2.1, down l.1)

/-- The `A₆` root attached to a label. -/
def rootOf (l : Label) : Fin 7 → ℤ := aroot (rootPair l).1 (rootPair l).2

/-- **Zero products join only orthogonal roots.** -/
theorem ann_orth : ∀ l m : Label, Ann l m → gramF (rootPair l) (rootPair m) = 0 := by
  have h : allLabels.all (fun l => allLabels.all fun m =>
      !decide (Ann l m) || decide (gramF (rootPair l) (rootPair m) = 0)) = true := by
    decide +kernel
  intro l m hlm
  have := List.all_eq_true.1 (of_allLabels h l) m (mem_allLabels m)
  simpa [hlm] using this

/-- The root of a primitive label is a genuine root (`i ≠ j`). -/
theorem rootPair_ne : ∀ l : Label, Primitive l → (rootPair l).1 ≠ (rootPair l).2 := by
  decide +kernel

/-- Every ordered pair `i ≠ j` occurs. -/
theorem rootPair_surj : ∀ i j : Fin 7, i ≠ j → ∃ l : Label, Primitive l ∧ rootPair l = (i, j) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- Two primitive labels give the same root pair iff they are twins. -/
theorem rootPair_eq_iff : ∀ l m : Label, Primitive l → Primitive m →
    (rootPair l = rootPair m ↔ m ∈ twinClass l) := by
  have h : allLabels.all (fun l => allLabels.all fun m =>
      !decide (Primitive l ∧ Primitive m) ||
        (decide (rootPair l = rootPair m) == decide (m ∈ twinClass l))) = true := by
    decide +kernel
  intro l m hl hm
  have := List.all_eq_true.1 (of_allLabels h l) m (mem_allLabels m)
  simpa [hl, hm] using this

/-- **Two primitive labels give the same `A₆` root iff they are twins** (same partners). -/
theorem rootOf_eq_iff (l m : Label) (hl : Primitive l) (hm : Primitive m) :
    rootOf l = rootOf m ↔ m ∈ twinClass l := by
  rw [← rootPair_eq_iff l m hl hm, rootOf, rootOf]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := aroot_inj (rootPair_ne l hl) h
    exact Prod.ext h1 h2
  · intro h; rw [h]

/-- **The roots of the 168 primitive labels are exactly the 42 roots of `A₆`.** -/
theorem image_rootOf : (Finset.univ.filter Primitive).image rootOf = roots 7 := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mem_roots]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, _, rootPair_ne l hl, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨l, hl, he⟩ := rootPair_surj i j hij
    exact ⟨l, hl, by rw [rootOf, he]⟩

/-- The box kite of a label is the xor of its root's (1-based) indices. -/
theorem kite_eq_xor : ∀ l : Label, Primitive l →
    kite l = ((rootPair l).1.val + 1) ^^^ ((rootPair l).2.val + 1) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **Roots in one box kite are orthogonal or opposite** (a `3 A₁`, never an `A₂`). -/
theorem same_kite_orth : ∀ l m : Label, Primitive l → Primitive m → kite l = kite m →
    gramF (rootPair l) (rootPair m) = -2 ∨ gramF (rootPair l) (rootPair m) = 0 ∨
      gramF (rootPair l) (rootPair m) = 2 := by
  have h : allLabels.all (fun l => allLabels.all fun m =>
      !decide (Primitive l ∧ Primitive m ∧ kite l = kite m) ||
        decide (gramF (rootPair l) (rootPair m) = -2 ∨ gramF (rootPair l) (rootPair m) = 0 ∨
          gramF (rootPair l) (rootPair m) = 2)) = true := by
    decide +kernel
  intro l m hl hm hk
  have := List.all_eq_true.1 (of_allLabels h l) m (mem_allLabels m)
  simpa [hl, hm, hk] using this

/-- The third point `(i+1) xor (j+1)`, shifted back to `0 … 6`. -/
def third (i j : Fin 7) : Fin 7 := down ⟨((i.val + 1) ^^^ (j.val + 1)) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- **The box kite of `e_i - e_j` is the third point of the Fano line through `i, j`.** -/
theorem third_on_line : ∀ i j : Fin 7, i ≠ j → ∀ t : Fin 7, i ∈ fanoLine t → j ∈ fanoLine t →
    third i j ∈ fanoLine t ∧ third i j ≠ i ∧ third i j ≠ j := by
  decide +kernel

/-- An `A₂` block contains roots at 60° (`⟨e_i - e_j, e_i - e_k⟩ = 1`). -/
theorem line_has_sixty : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → gramF (i, j) (i, k) = 1 := by
  decide +kernel

end QBX.Notes.BoxKiteRoots
