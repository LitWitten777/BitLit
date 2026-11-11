module

public import Sovereign.Meta.StateOfThoughtPairedView
public import Sovereign.Meta.CliffordMul

@[expose] public section

/-!
# Paired CD × Clifford view on `ℚ^16`

`pairedCDClifford x` is the paired linear map `y ↦ (y ·_CD x, y ·_Cliff x)`, where `·_CD` is
the sedenion product (through `cdRightMul`) and `·_Cliff` is the specific Clifford product of
`Sovereign.Clifford.cliffordRightMulLin`. The FINDINGS.md classification of the 84 primitive
sedenion zero divisors ("joint stacked rank 16 for 48 keys, 14 for 36 keys") is
`PairedCDCliffordClassification`.

## Structural theorems proved

* `ker_pairedCDClifford` — the paired kernel is `sedenionAnnihilator x ⊓ ker(Cliff_x)`.
* `paired_injective_of_clifford_injective` — if the Clifford view is injective, the pair is.
* `pairedCDClifford_joint_ker_le` — the joint kernel is contained in the CD annihilator, so
  for a nonzero zero divisor it is at most 4-dimensional (from
  `finrank_sedenionAnnihilator_of_zeroDivisor`).
-/

namespace Sovereign.StateOfThought

open CDA Sovereign.Clifford

/-- The paired CD × Clifford view: `y ↦ (y ·_CD x, y ·_Cliff x)`. -/
noncomputable def pairedCDClifford (x : CDA ℚ 4) :
    (Fin 16 → ℚ) →ₗ[ℚ] (Fin 16 → ℚ) × (Fin 16 → ℚ) :=
  stack (cdRightMul x) (cliffordRightMulLin (coord16 x))

/-- The joint kernel is the intersection of the CD-annihilator and the Clifford-kernel. -/
theorem ker_pairedCDClifford (x : CDA ℚ 4) :
    LinearMap.ker (pairedCDClifford x) =
      sedenionAnnihilator x ⊓ LinearMap.ker (cliffordRightMulLin (coord16 x)) := by
  rw [pairedCDClifford, ker_stack, sedenionAnnihilator_eq_ker]

/-- **Structural: Clifford injective ⇒ paired injective.** -/
theorem paired_injective_of_clifford_injective (x : CDA ℚ 4)
    (h : Function.Injective (cliffordRightMulLin (coord16 x))) :
    Function.Injective (pairedCDClifford x) := by
  rw [pairedCDClifford, injective_stack_iff, ← sedenionAnnihilator_eq_ker,
    LinearMap.ker_eq_bot.mpr h, inf_bot_eq]

/-- **Structural: joint kernel ⊆ CD annihilator.** -/
theorem pairedCDClifford_joint_ker_le (x : CDA ℚ 4) :
    LinearMap.ker (pairedCDClifford x) ≤ sedenionAnnihilator x := by
  rw [ker_pairedCDClifford]
  exact inf_le_left

/-! ## The 84 assessors, enumerated -/

/-- The 84 assessor pairs `(i, j)` with `1 ≤ i ≤ 7`, `9 ≤ j ≤ 15`, `j ≠ i + 8` (de Marrais'
condition). -/
def assessorPairs : List (Fin 16 × Fin 16) :=
  (Finset.univ.product Finset.univ).filter (fun p : Fin 16 × Fin 16 =>
    decide (1 ≤ p.1.val ∧ p.1.val ≤ 7 ∧ 9 ≤ p.2.val ∧ p.2.val ≠ p.1.val + 8)).toList

/-- The 84 two-term sedenion zero divisors `e_i ± e_j` for assessor pairs `(i, j)`, as
`CDA ℚ 4` elements. -/
noncomputable def assessors : List (CDA ℚ 4) :=
  assessorPairs.flatMap (fun p =>
    [ofFn16 (fun k => if k = p.1 then 1 else if k = p.2 then 1 else 0),
     ofFn16 (fun k => if k = p.1 then 1 else if k = p.2 then -1 else 0)])

/-- Sanity: 84 assessors. -/
theorem assessors_length : assessors.length = 84 := by
  native_decide

/-! ## The classification target -/

/-- The FINDINGS.md classification: among the 84 assessors, 48 have joint kernel 0 (paired
rank 16) and 36 have joint kernel 2 (paired rank 14).

Verified numerically by `verify_paired.py`. To formalize in Lean: prove this `Prop` by
either (a) evaluating `Module.finrank ℚ (LinearMap.ker (pairedCDClifford x))` via a
computable rational rank function, or (b) providing explicit kernel-basis witnesses for each
of the 84 keys.

The 36 keys where `CliffordRightMul x` is injective are automatically in the "joint kernel 0"
camp by `paired_injective_of_clifford_injective`. -/
def PairedCDCliffordClassification : Prop :=
  (assessors.toFinset.filter
    (fun x => Module.finrank ℚ (LinearMap.ker (pairedCDClifford x)) = 0)).card = 48 ∧
  (assessors.toFinset.filter
    (fun x => Module.finrank ℚ (LinearMap.ker (pairedCDClifford x)) = 2)).card = 36

end Sovereign.StateOfThought
