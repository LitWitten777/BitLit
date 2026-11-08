module

public import Mathlib

@[expose] public section

/-!
# Braid "compression" and Chern-number "integrity guards": what can and cannot hold

A pasted note made three engineering claims. This file checks the mathematical content of each.
Report: `docs/CD_ZERO_DIVISOR_BRAID_CHERN_AUDIT_2026-10-20.md`.

## 1. "Any text can be compressed into a braid polynomial"

* `no_lossless_shortening`: an injective (= lossless) encoder of all `n`-bit strings must output
  at least one string of length `≥ n`. This holds for *every* encoding, braid-based or not
  (pigeonhole: there are `2ⁿ` inputs but only `2ⁿ - 1` shorter bit strings).
* Jones and Alexander polynomials are invariants of the *closed* braid, so they take equal
  values on conjugate braids. In Lean: `B3` is Artin's braid group on three strands (presented
  group, one braid relation), `s1_ne_s2` and `s1s2_ne_s2s1` show its generators and the words
  `σ₁σ₂`, `σ₂σ₁` are distinct, and `classFunction_not_injective` shows that **no** function `f`
  with `f (g h) = f (h g)` is injective on `B3`. So such a polynomial cannot be decoded back to
  the braid word, let alone the text.

## 2. "A Chern number jumps to a fraction when memory is corrupted"

We use the standard lattice (Fukui–Hatsugai–Suzuki) Chern number on an `L × L` periodic grid:
the link angles `ax`, `ay` are arbitrary real numbers, the plaquette flux is the curl wrapped into
`(-π, π]`, and the Chern number is the total flux divided by `2π`.

* `latticeChern_isInt`: for **every** choice of link data, including corrupted data, the
  result is an integer. So a check of the form "the Chern number is no longer an integer"
  can never fire.
* `latticeChern_singleLink_lt` and `latticeChern_singleLink_pi`: changing one link angle from
  `t` (with `|t| < π`) to `π` changes the Chern number from `0` to `1`. So the integer is not
  immune to a single local change, and an arbitrarily small change can flip it.
-/

namespace QBX.Notes.BraidChern

open Finset

/-! ### 1a. Pigeonhole: no lossless encoder shortens every input -/

/-- Lists of booleans of length `< n`, as a finset. -/
def shortLists (n : ℕ) : Finset (List Bool) :=
  (range n).biUnion fun k => (univ : Finset (Fin k → Bool)).image List.ofFn

lemma mem_shortLists {n : ℕ} {l : List Bool} (hl : l.length < n) : l ∈ shortLists n := by
  simp only [shortLists, mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  exact ⟨l.length, hl, fun i => l.get i, List.ofFn_get l⟩

lemma sum_two_pow_lt (n : ℕ) : ∑ k ∈ range n, 2 ^ k < 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

lemma card_shortLists_lt (n : ℕ) : (shortLists n).card < 2 ^ n := by
  have h : (shortLists n).card ≤ ∑ k ∈ range n, 2 ^ k := by
    refine (card_biUnion_le).trans (sum_le_sum fun k _ => ?_)
    refine (card_image_le).trans ?_
    simp
  exact h.trans_lt (sum_two_pow_lt n)

/-- **No lossless shortening.** An injective encoder of `n`-bit strings into bit strings has
an input whose code is at least `n` bits long. This applies to any scheme, including encoding
text as braid words or as polynomials written out in bits. -/
theorem no_lossless_shortening (n : ℕ) (f : (Fin n → Bool) → List Bool)
    (hf : Function.Injective f) : ∃ x, n ≤ (f x).length := by
  by_contra h
  push_neg at h
  have hsub : (univ : Finset (Fin n → Bool)).image f ⊆ shortLists n := by
    intro l hl
    obtain ⟨x, -, rfl⟩ := mem_image.1 hl
    exact mem_shortLists (h x)
  have := card_le_card hsub
  rw [card_image_of_injective _ hf, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at this
  exact absurd this (not_le.2 (card_shortLists_lt n))

/-! ### 1b. Conjugation-invariant braid invariants forget the word -/

/-- The single braid relation `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`, written as a relator. -/
def b3Rels : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹}

/-- Artin's braid group on three strands, `⟨σ₁, σ₂ | σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂⟩`. -/
abbrev B3 := PresentedGroup b3Rels

/-- The generator `σ₁`. -/
def s1 : B3 := PresentedGroup.of 0
/-- The generator `σ₂`. -/
def s2 : B3 := PresentedGroup.of 1

theorem braid_relation : s1 * s2 * s1 = s2 * s1 * s2 := by
  have h : (PresentedGroup.mk b3Rels) (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure (Set.mem_singleton _))
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.1 h

/-- The permutation of the strand endpoints: `σ₁ ↦ (0 1)`, `σ₂ ↦ (1 2)`. -/
def toPerm : B3 →* Equiv.Perm (Fin 3) :=
  PresentedGroup.toGroup (f := ![Equiv.swap 0 1, Equiv.swap 1 2]) (by
    intro r hr
    rw [Set.mem_singleton_iff.1 hr]
    decide)

lemma toPerm_s1 : toPerm s1 = Equiv.swap 0 1 := PresentedGroup.toGroup.of _
lemma toPerm_s2 : toPerm s2 = Equiv.swap 1 2 := PresentedGroup.toGroup.of _

/-- `σ₁ ≠ σ₂` in `B₃`. -/
theorem s1_ne_s2 : s1 ≠ s2 := by
  intro h
  have := congrArg toPerm h
  rw [toPerm_s1, toPerm_s2] at this
  exact absurd this (by decide)

/-- The braid words `σ₁ σ₂` and `σ₂ σ₁` are different braids. -/
theorem s1s2_ne_s2s1 : s1 * s2 ≠ s2 * s1 := by
  intro h
  have := congrArg toPerm h
  rw [map_mul, map_mul, toPerm_s1, toPerm_s2] at this
  exact absurd this (by decide)

/-- `σ₂` is a conjugate of `σ₁`: `σ₂ = (σ₁ σ₂) σ₁ (σ₁ σ₂)⁻¹`. -/
theorem s2_conj_s1 : s2 = (s1 * s2) * s1 * (s1 * s2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, braid_relation, mul_assoc]

/-- A **class function** (`f (g h) = f (h g)`, as for the Jones or Alexander polynomial of the
closure, or the trace of any representation) takes the same value on `σ₁` and `σ₂`. -/
theorem classFunction_s1_eq_s2 {X : Type*} (f : B3 → X) (hf : ∀ g h, f (g * h) = f (h * g)) :
    f s1 = f s2 := by
  rw [s2_conj_s1, hf, ← mul_assoc, inv_mul_cancel, one_mul]

/-- A class function cannot tell `σ₁ σ₂` from `σ₂ σ₁`. -/
theorem classFunction_s1s2 {X : Type*} (f : B3 → X) (hf : ∀ g h, f (g * h) = f (h * g)) :
    f (s1 * s2) = f (s2 * s1) := hf _ _

/-- **No class function on `B₃` is injective.** So no conjugation-invariant braid invariant
(Jones polynomial, Alexander polynomial, character of a representation) can be decoded back
into the braid word. -/
theorem classFunction_not_injective {X : Type*} (f : B3 → X)
    (hf : ∀ g h, f (g * h) = f (h * g)) : ¬ Function.Injective f :=
  fun hinj => s1_ne_s2 (hinj (classFunction_s1_eq_s2 f hf))

/-! ### 2. The lattice Chern number is an integer for every input -/

variable {L : ℕ} [NeZero L]

/-- Sites of the `L × L` periodic lattice (a discrete torus). -/
abbrev Site (L : ℕ) := ZMod L × ZMod L

/-- Lattice curl of the link angles around the plaquette with lower-left corner `p`. -/
def curl (ax ay : Site L → ℝ) (p : Site L) : ℝ :=
  ax p + ay (p + (1, 0)) - ax (p + (0, 1)) - ay p

/-- The plaquette flux: the curl wrapped into `(-π, π]`. -/
noncomputable def plaqFlux (ax ay : Site L → ℝ) (p : Site L) : ℝ :=
  toIocMod Real.two_pi_pos (-Real.pi) (curl ax ay p)

/-- The lattice Chern number: total plaquette flux divided by `2π`. -/
noncomputable def latticeChern (ax ay : Site L → ℝ) : ℝ :=
  (∑ p, plaqFlux ax ay p) / (2 * Real.pi)

lemma sum_shift (g : Site L → ℝ) (q : Site L) : ∑ p, g (p + q) = ∑ p, g p :=
  Fintype.sum_equiv (Equiv.addRight q) _ _ (fun _ => rfl)

/-- The curl sums to zero over the torus (every link occurs once with each sign). -/
theorem sum_curl (ax ay : Site L → ℝ) : ∑ p, curl ax ay p = 0 := by
  simp only [curl, sum_sub_distrib, sum_add_distrib, sum_shift]
  ring

/-- **Integrality for every input.** Whatever real numbers the link angles are (correct,
noisy, or corrupted), the lattice Chern number is an integer. -/
theorem latticeChern_isInt (ax ay : Site L → ℝ) : ∃ n : ℤ, latticeChern ax ay = n := by
  refine ⟨-∑ p, toIocDiv Real.two_pi_pos (-Real.pi) (curl ax ay p), ?_⟩
  have hp : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have h : ∑ p, plaqFlux ax ay p =
      ∑ p, curl ax ay p - ∑ p, (toIocDiv Real.two_pi_pos (-Real.pi) (curl ax ay p) : ℝ) *
        (2 * Real.pi) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [plaqFlux, toIocMod, zsmul_eq_mul]
  rw [latticeChern, h, sum_curl, ← sum_mul, div_eq_iff hp]
  push_cast
  ring

/-- The link configuration that is zero except for the `x`-link at the origin, which is `t`. -/
noncomputable def singleLink (t : ℝ) : Site L → ℝ := fun p => if p = 0 then t else 0

omit [NeZero L] in
lemma curl_singleLink (t : ℝ) (p : Site L) :
    curl (singleLink t) 0 p = (if p = 0 then t else 0) - (if p = (0, -1) then t else 0) := by
  have h : p + (0, 1) = 0 ↔ p = (0, -1) := by
    rw [show ((0 : ZMod L), (-1 : ZMod L)) = -((0 : ZMod L), (1 : ZMod L)) by simp,
      eq_neg_iff_add_eq_zero]
  simp only [curl, singleLink, Pi.zero_apply, add_zero, sub_zero, h]

lemma sum_flux_singleLink (hL : 2 ≤ L) (t : ℝ) :
    ∑ p, plaqFlux (singleLink t) (0 : Site L → ℝ) p =
      toIocMod Real.two_pi_pos (-Real.pi) t + toIocMod Real.two_pi_pos (-Real.pi) (-t) := by
  have hne : (0 : Site L) ≠ (0, -1) := by
    intro h
    have h2 : ((-1 : ZMod L)) = 0 := (congrArg Prod.snd h).symm
    rw [neg_eq_zero] at h2
    have : ((1 : ℕ) : ZMod L) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  rw [sum_eq_add (0 : Site L) (0, -1) hne]
  · simp [plaqFlux, curl_singleLink, hne, hne.symm]
  · intro c _ hc
    have h0 : toIocMod Real.two_pi_pos (-Real.pi) 0 = 0 :=
      (toIocMod_eq_self _).2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    simp [plaqFlux, curl_singleLink, hc.1, hc.2, h0]
  · simp
  · simp

/-- Any single-link value `t` with `|t| < π` gives Chern number `0`. -/
theorem latticeChern_singleLink_lt (hL : 2 ≤ L) {t : ℝ} (ht : t ∈ Set.Ioo (-Real.pi) Real.pi) :
    latticeChern (singleLink (L := L) t) 0 = 0 := by
  rw [latticeChern, sum_flux_singleLink hL]
  rw [(toIocMod_eq_self _).2 ⟨ht.1, by linarith [ht.2]⟩,
    (toIocMod_eq_self _).2 ⟨by linarith [ht.2], by linarith [ht.1]⟩]
  simp

/-- Setting the same link to `π` gives Chern number `1`. Together with
`latticeChern_singleLink_lt`, an arbitrarily small change of a single link can change the
Chern number. -/
theorem latticeChern_singleLink_pi (hL : 2 ≤ L) :
    latticeChern (singleLink (L := L) Real.pi) 0 = 1 := by
  have hpi := Real.pi_pos
  rw [latticeChern, sum_flux_singleLink hL]
  have h1 : toIocMod Real.two_pi_pos (-Real.pi) Real.pi = Real.pi :=
    (toIocMod_eq_self _).2 ⟨by linarith, by linarith⟩
  have h2 : toIocMod Real.two_pi_pos (-Real.pi) (-Real.pi) = Real.pi := by
    rw [← toIocMod_add_right, show -Real.pi + 2 * Real.pi = Real.pi by ring, h1]
  rw [h1, h2, div_eq_one_iff_eq Real.two_pi_pos.ne']
  ring

end QBX.Notes.BraidChern
