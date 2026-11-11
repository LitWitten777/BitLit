import Mathlib

/-!
# Laurent denominator clearing for holonomy certificates
-/

open scoped BigOperators

noncomputable section

theorem localization_away_exists_rep {R : Type*} [CommRing R] (ad : R)
    (x : Localization.Away ad) :
    ∃ (num : R) (N : ℕ),
      x * algebraMap R (Localization.Away ad) (ad ^ N) =
        algebraMap R (Localization.Away ad) num := by
  obtain ⟨⟨r, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers ad) x
  exact ⟨r, n, h⟩

theorem localization_away_uniform_clear {R : Type*} [CommRing R] (ad : R) {B : ℕ}
    (psi : Fin B → Localization.Away ad) :
    ∃ (N : ℕ) (nums : Fin B → R),
      ∀ i : Fin B,
        psi i * algebraMap R (Localization.Away ad) (ad ^ N) =
          algebraMap R (Localization.Away ad) (nums i) := by
  induction B with
  | zero => exact ⟨0, Fin.elim0, fun i => i.elim0⟩
  | succ B ih =>
    obtain ⟨N₁, nums₁, h₁⟩ := ih (fun i => psi i.castSucc)
    obtain ⟨num₂, N₂, h₂⟩ := localization_away_exists_rep ad (psi (Fin.last B))
    refine ⟨N₁ + N₂, Fin.snoc (fun i => nums₁ i * ad ^ N₂) (num₂ * ad ^ N₁), fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; (
    -- By multiplying both sides of the equation from h₂ by (algebraMap R (Localization.Away ad)) (ad ^ N₁), we obtain the desired result.
    have := congr_arg (fun x => x * (algebraMap R (Localization.Away ad)) (ad ^ N₁)) h₂; simp_all +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ];
    -- By multiplying both sides of the equation from h₂ by (algebraMap R (Localization.Away ad)) ad ^ N₁, we obtain the desired result.
    rw [← h₂]
    ring)
    | cast i => simp only [Fin.snoc_castSucc]; (
    convert congr_arg ( · * algebraMap R ( Localization.Away ad ) ( ad ^ N₂ ) ) ( h₁ i ) using 1 <;> simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ])

end