module

public import Mathlib

@[expose] public section

/-!
# A specific Clifford multiplication on `ℚ^16`

Translated from `psi_cliff` in `hypercube/hashrounds2.py`, this file defines the sign function
`psiCliff : Fin 16 → Fin 16 → ℚ` and the Clifford right-multiplication matrix
`cliffordRightMul k`. The FINDINGS.md compares this with `cdRightMul` (Cayley–Dickson
multiplication by the same sedenion key) and reports Clifford rank 8 or 16 depending on the
key. The paired rank classification lives in `PairedCDClifford.lean`.

## Conventions

Basis is `e_0, e_1, …, e_15` (the standard CD basis). `e_a ·_Cliff e_b = psiCliff a b · e_{a⊕b}`.
The right-multiplication matrix `M` satisfies `(M · y)_c = (y ·_Cliff k)_c`.
-/

namespace Sovereign.Clifford

/-- XOR on `Fin 16`: always stays in `Fin 16`. -/
theorem xorFin_val_lt (a b : Fin 16) : a.val ^^^ b.val < 16 := by native_decide

/-- `Fin 16` with XOR. -/
def xorFin (a b : Fin 16) : Fin 16 := ⟨a.val ^^^ b.val, xorFin_val_lt a b⟩

/-- The `i`-th bit (0-indexed) of a `Fin 16` value. -/
def bitOf (a : Fin 16) (i : Fin 4) : ℕ := (a.val / 2 ^ i.val) % 2

/-- The Clifford sign function `psiCliff(a, b) = (-1)^{s(a,b)}`, where `s(a, b)` counts pairs
`(i, j)` with `i ≥ j`, `a_i = 1`, `b_j = 1` (bit indices `i, j ∈ Fin 4`). This is the
`psi_cliff` sign table from `hypercube/hashrounds2.py`. -/
def psiCliff (a b : Fin 16) : ℚ :=
  let s := (Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
    p.1.val ≥ p.2.val ∧ bitOf a p.1 = 1 ∧ bitOf b p.2 = 1)).card
  if Even s then 1 else -1

/-- The Clifford right-multiplication matrix: `M[c, a] = k_{a⊕c} · psiCliff a (a⊕c)`. -/
def cliffordRightMul (k : Fin 16 → ℚ) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun c a => k (xorFin a c) * psiCliff a (xorFin a c)

/-- The Clifford right-multiplication as a linear map `y ↦ y ·_Cliff k`. -/
def cliffordRightMulLin (k : Fin 16 → ℚ) : (Fin 16 → ℚ) →ₗ[ℚ] (Fin 16 → ℚ) :=
  (Matrix.of (cliffordRightMul k)).mulVecLin

/-! ## Sanity checks -/

/-- `e_1 ·_Cliff e_1 = -e_0`, matching the CD product for a basis element squared. -/
example : psiCliff 1 1 = -1 := by native_decide

/-- `e_1 ·_Cliff e_2 = +e_3`. -/
example : psiCliff 1 2 = 1 := by native_decide

/-- `psiCliff(a, 0) = 1` for every `a` (0 is the multiplicative identity in the twisted
convention), so right-multiplying by `e_0` is the identity map. -/
example : cliffordRightMul (fun i => if i = 0 then (1 : ℚ) else 0) = 1 := by native_decide

/-- `psiCliff` differs from the CD sign on some pairs: `psiCliff 3 3 = -1` (a unit-squared,
consistent with CD) but `psiCliff 3 5 ≠ psiCliff 5 3` in general — the Clifford algebra here is
not the sedenions; it is a *distinct* sign table on the same 16-dim space. -/
example : psiCliff 3 5 ≠ psiCliff 5 3 := by native_decide

end Sovereign.Clifford
