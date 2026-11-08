module

public import Mathlib
public import QBX.Formal.ClosureLinking
public import QBX.Formal.Connections.TorusLinks

@[expose] public section

/-!
# Ternary strands: three Hopf fibres, the full twist, and 3-colourings

**Status: documentation note, not a theorem of the core corpus** (Lake library `QBXNotes`).
The corrections matter (a Hopf fibre is not a ternary strand; the `(3, q)` orbits are different
objects, see the core file `QBX.Formal.Connections.HopfStrands`), but the subject of this note is
Hebrew-letter numerology, so it lives outside `QBX.Formal`.

`QBX.Formal.Connections.HopfStrands` shows that a *single* Hopf fibre is a 1-strand closed braid.
Ternary structure appears in two other places, both checked here on the QBX braid group
`BraidGroup 3`.

**Three Hopf fibres.**  Any `n` distinct Hopf fibres form the torus link `T(n, n)`; for
`n = 3` this is the closure of the 3-strand torus braid `(σ₁σ₂)³ = Δ²`, the full twist.
(The identification of `n` Hopf fibres with `T(n, n)` is the standard picture of the Hopf
fibration — fibres over a circle of latitude in `S²` are `(1, 1)` curves on one torus — and is
cited, not re-proved.)  Proved:

* `threeFibres_pure`, `threeFibres_components`: the closure has three components;
* `crossMatrix_threeFibres`, `linkingSpectrum_threeFibres`: every pair of components links
  exactly once — the braid-side shadow of "any two Hopf fibres have linking number 1";
* `fullTwist_eq`, `fullTwist_central`: `(σ₁σ₂)³ = (σ₁σ₂σ₁)²` and it commutes with every braid.

**Ternary labels (Fox 3-colourings).**  Labelling strands by `ℤ/3` with the rule
"under-strand out = 2·over − under-strand in" gives an action `foxHom` of `B₃` on `(ℤ/3)³`
(`foxGen_rels` checks the braid relation).  The number of 3-colourings of the closure of `g`
is the number of labellings fixed by `g` (`colourings g`); the closure is *tricolourable* when
this exceeds the 3 constant colourings.  Proved:

* `fox_period`: `(σ₁σ₂)⁶` acts trivially;
* `colourings_torus`: `T(3, q)` has 27, 9 or 3 colourings according as `6 ∣ q`, `q` even but
  `6 ∤ q`, or `q` odd; hence `tricolourable_torus_iff`: `T(3, q)` is tricolourable iff `q` is
  even;
* `colourings_tenen`: Tenen's `(3, 10)` knot has 9 colourings, so it **is** tricolourable (the
  Meru JSON's claim checks out); `colourings_threeFibres`: three Hopf fibres (`T(3, 3)`) are
  **not** tricolourable.
-/

namespace QBX.Notes

open QBX.Formal QBX.Formal.Connections

/-! ### Three Hopf fibres = the full twist on three strands -/

/-- The closure of `(σ₁σ₂)³`, i.e. `T(3, 3)`: three Hopf fibres. -/
def threeFibres : BraidGroup 3 := torusBraid 2 3

theorem cycBraid_two_two : cycBraid 2 2 = sigma (n := 3) 0 * sigma 1 := by
  simp [cycBraid]

/-- The full twist is a pure braid: each Hopf fibre closes up on itself. -/
theorem threeFibres_pure : permHom 3 threeFibres = 1 := by
  rw [threeFibres, permHom_torusBraid]
  ext x
  simp only [Equiv.coe_addRight, Equiv.Perm.coe_one, id_eq]
  rw [show ((3 : ℕ) : ZMod (2 + 1)) = 0 from rfl, add_zero]

/-- The closure has three components. -/
theorem threeFibres_components : numCycles (permHom 3 threeFibres) = 3 := by
  rw [threeFibres, torusBraid_components]; rfl

/-- Every pair of distinct strands of the full twist crosses twice (signed). -/
theorem crossMatrix_threeFibres (a b : Fin 3) :
    crossMatrix threeFibres a b = if a = b then 0 else 2 := by
  simp only [threeFibres, torusBraid, cycBraid_two_two, pow_succ, pow_zero, one_mul]
  fin_cases a <;> fin_cases b <;>
    simp [crossMatrix_mul, crossMatrix_sigma, crossE, map_mul, transposition, siteL, siteR,
      Equiv.swap_apply_def]

/-- **Any two of the three fibres link exactly once**: the linking spectrum of the closure is six
copies of `1` (one per ordered pair of distinct components). -/
theorem linkingSpectrum_threeFibres :
    linkingSpectrum threeFibres = Multiset.replicate 6 1 := by
  rw [linkingSpectrum_pure threeFibres_pure]
  have h : ∀ x ∈ (Finset.univ.offDiag : Finset (Fin 3 × Fin 3)).val,
      crossMatrix threeFibres x.1 x.2 / 2 = 1 := by
    rintro ⟨a, b⟩ hx
    have hab : a ≠ b := (Finset.mem_offDiag.1 hx).2.2
    simp [crossMatrix_threeFibres, hab]
  rw [Multiset.map_congr rfl h, Multiset.map_const']
  rfl

/-- `(σ₁σ₂)³ = (σ₁σ₂σ₁)²`: the torus braid of three fibres is the square of Garside's `Δ`. -/
theorem fullTwist_eq :
    threeFibres = (sigma (n := 3) 0 * sigma 1 * sigma 0) ^ 2 := by
  have hb := sigma_braid (n := 3) 0 1 rfl
  simp only [threeFibres, torusBraid, cycBraid_two_two, pow_succ, pow_zero, one_mul]
  calc sigma 0 * sigma 1 * (sigma 0 * sigma 1) * (sigma 0 * sigma 1)
      = (sigma 0 * sigma 1 * sigma 0) * (sigma 1 * sigma 0 * sigma 1) := by group
    _ = (sigma 0 * sigma 1 * sigma 0) * (sigma 0 * sigma 1 * sigma 0) := by rw [← hb]

/-- **The full twist is central** in `B₃`. -/
theorem fullTwist_central (g : BraidGroup 3) : threeFibres * g = g * threeFibres := by
  rw [fullTwist_eq]
  have hb := sigma_braid (n := 3) 0 1 rfl
  have h0 : (sigma (n := 3) 0 * sigma 1 * sigma 0) * sigma 0 =
      sigma 1 * (sigma 0 * sigma 1 * sigma 0) := by
    calc (sigma (n := 3) 0 * sigma 1 * sigma 0) * sigma 0
        = (sigma 1 * sigma 0 * sigma 1) * sigma 0 := by rw [hb]
      _ = sigma 1 * (sigma 0 * sigma 1 * sigma 0) := by group
  have h1 : (sigma (n := 3) 0 * sigma 1 * sigma 0) * sigma 1 =
      sigma 0 * (sigma 0 * sigma 1 * sigma 0) := by
    calc (sigma (n := 3) 0 * sigma 1 * sigma 0) * sigma 1
        = sigma 0 * (sigma 1 * sigma 0 * sigma 1) := by group
      _ = sigma 0 * (sigma 0 * sigma 1 * sigma 0) := by rw [hb]
  generalize sigma (n := 3) 0 * sigma 1 * sigma 0 = D at h0 h1 ⊢
  have hgen : ∀ i : Fin 2, sigma i ∈ Subgroup.centralizer {D ^ 2} := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    fin_cases i
    · show sigma 0 * D ^ 2 = D ^ 2 * sigma 0
      rw [pow_two, mul_assoc D D, h0, ← mul_assoc D (sigma 1) D, h1, mul_assoc]
    · show sigma 1 * D ^ 2 = D ^ 2 * sigma 1
      rw [pow_two, mul_assoc D D, h1, ← mul_assoc D (sigma 0) D, h0, mul_assoc]
  have hall : Subgroup.centralizer {D ^ 2} = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hall ▸ Subgroup.mem_top g)).symm

/-! ### Fox 3-colourings: ternary labels on strands -/

/-- Labellings of three strand ends by `ℤ/3`. -/
abbrev Col3 := Fin 3 → ZMod 3

/-- The labelling after the crossing `σᵢ`: the over-strand label moves left, the under-strand
label `a` becomes `2b − a` where `b` is the over-strand label. -/
def foxFwd (i : Fin 2) (x : Col3) : Col3 := fun k =>
  if k = i.castSucc then x i.succ else if k = i.succ then 2 * x i.succ - x i.castSucc else x k

/-- The inverse crossing. -/
def foxBwd (i : Fin 2) (x : Col3) : Col3 := fun k =>
  if k = i.castSucc then 2 * x i.castSucc - x i.succ else if k = i.succ then x i.castSucc else x k

/-- The crossing `σᵢ` as a permutation of labellings. -/
def foxGen (i : Fin 2) : Equiv.Perm Col3 where
  toFun := foxFwd i
  invFun := foxBwd i
  left_inv := by revert i; decide
  right_inv := by revert i; decide

/-- The colouring moves satisfy the braid relation. -/
theorem foxGen_rels : ∀ r ∈ braidRels 3, FreeGroup.lift foxGen r = 1 := by
  rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
    fin_cases i <;> fin_cases j <;> simp at hij
    decide
  · fin_cases i <;> fin_cases j <;> simp at hij

/-- The action of `B₃` on ternary labellings. -/
def foxHom : BraidGroup 3 →* Equiv.Perm Col3 := PresentedGroup.toGroup foxGen_rels

theorem foxHom_sigma (i : Fin 2) : foxHom (sigma i) = foxGen i :=
  PresentedGroup.toGroup.of foxGen_rels

/-- Number of Fox 3-colourings of the closure of `g`: labellings fixed by `g`. -/
def colourings (g : BraidGroup 3) : ℕ := Fintype.card {x : Col3 // foxHom g x = x}

/-- The closure of `g` is tricolourable: it has a non-constant 3-colouring. -/
def Tricolourable (g : BraidGroup 3) : Prop := 3 < colourings g

theorem foxHom_cyc : foxHom (cycBraid 2 2) = foxGen 0 * foxGen 1 := by
  simp [cycBraid, foxHom_sigma]

/-- `(σ₁σ₂)⁶` acts trivially on ternary labellings. -/
theorem fox_period : (foxGen 0 * foxGen 1) ^ 6 = 1 := by decide

theorem foxHom_torus (q : ℕ) :
    foxHom (torusBraid 2 q) = (foxGen 0 * foxGen 1) ^ (q % 6) := by
  rw [torusBraid, map_pow, foxHom_cyc]
  conv_lhs => rw [← Nat.div_add_mod q 6, pow_add, pow_mul, fox_period, one_pow, one_mul]

/-- **Colourings of `T(3, q)`**: 27 if `6 ∣ q`, 9 if `q` is even and `6 ∤ q`, 3 if `q` is odd. -/
theorem colourings_torus (q : ℕ) :
    colourings (torusBraid 2 q) = if q % 6 = 0 then 27 else if q % 2 = 0 then 9 else 3 := by
  have h2 : q % 2 = (q % 6) % 2 := by omega
  rw [colourings, foxHom_torus, h2]
  have : q % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize q % 6 = r at this ⊢
  interval_cases r <;> decide

/-- **`T(3, q)` is tricolourable iff `q` is even.** -/
theorem tricolourable_torus_iff (q : ℕ) : Tricolourable (torusBraid 2 q) ↔ 2 ∣ q := by
  rw [Tricolourable, colourings_torus]
  split_ifs <;> omega

/-- Tenen's `(3, 10)` torus knot has 9 Fox 3-colourings: it is tricolourable. -/
theorem colourings_tenen : colourings (torusBraid 2 10) = 9 := by
  rw [colourings_torus]; rfl

/-- Three Hopf fibres (`T(3, 3)`) have only the 3 constant colourings: not tricolourable. -/
theorem colourings_threeFibres : colourings threeFibres = 3 := by
  rw [threeFibres, colourings_torus]; rfl

end QBX.Notes
