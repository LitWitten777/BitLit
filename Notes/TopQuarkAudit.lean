module

public import Mathlib

@[expose] public section

/-!
# Can the top-quark coupling `0.993` be derived from the gauge constraints?

Audit of `sovereign/Sovereign/Physics/TopQuarkFixedPoint.lean`
(report: `docs/VOXEL_TOPQUARK_ZD32_2026-10-20.md`).

That module states the Pendleton–Ross ratio `R* = y_t² / g₃² = 2/9`, then separately sets
`y_t* = 0.993` by hand and checks `0.993 · 246.22 / √2 ∈ (171, 175)`. Everything below uses the
standard one-loop Standard-Model renormalisation-group equations (`t = log μ`, common factor
`1/(16π²)` dropped; `g'` is the hypercharge coupling in Standard-Model normalisation):

* `d(y_t²)/dt ∝ y_t² (9/2 y_t² − 8 g₃² − 9/4 g₂² − 17/12 g'²)`,
* `d(g₃²)/dt ∝ −7 g₃⁴`.

## Findings

1. **The gauge constraint, solved exactly.** The ratio `R = y_t²/g₃²` is stationary iff
   `y_t² = (2/9)(g₃² + 9/4 g₂² + 17/12 g'²)` (`ratio_stationary_iff`). Without the electroweak
   couplings this is the module's `R* = 2/9` (`ratio_stationary_iff_qcd`); the "`(9/2) R* = 8 − 7`"
   of its docstring is the same equation.
2. **It cannot give 173 GeV.** For any couplings in the physical range `g₃ ≤ 1.23`, `g₂ ≤ 0.66`,
   `g' ≤ 0.37`, the gauge-constrained coupling gives `m_t = y_t v/√2 < 140 GeV`
   (`mt_gauge_constrained_lt`), so **`0.993` is not derivable from this fixed point**, even with
   the electroweak corrections included.
3. **What ratio 173 GeV needs.** `m_t ≥ 171 GeV` with `g₃ ≤ 1.23` forces `R ≥ 0.63`
   (`ratio_needed_ge`), about `2.9 ×` the Pendleton–Ross value. The "`R_phys ≈ 1.05`" of the
   docstring together with `y_t = 0.993` would need `g₃ < 0.97` (`ratio_105_needs_small_g3`),
   far below the measured `g₃(m_Z) ≈ 1.22`.
4. **The flow of the ratio, solved exactly (QCD only).** With `α = g₃²` and `u = 1/R`, the
   one-loop system is solved by `α(t) = α₀/(1 + 7cα₀t)`,
   `u(t) = 9/2 + (u₀ − 9/2)(1 + 7cα₀t)^{1/7}` (`alphaFlow_hasDerivAt`, `uFlow_hasDerivAt`). So the
   deviation from the fixed point shrinks only like `(α₀/α)^{1/7}` (`uFlow_deviation`); while `α`
   grows by at most a factor 3 (roughly the whole range from the unification scale to `m_Z`) at
   least `85 %` of the initial deviation remains (`deviation_factor_ge`). The fixed point
   `R* = 2/9` is never reached at physical scales.
5. **The quasi-infrared fixed point overshoots.** Starting from an arbitrarily large Yukawa at the
   high scale (`u₀ = 0`) gives `R = 2 / (9 (1 − (α₀/α)^{1/7}))`, which is `≥ 1.48` whenever
   `α ≤ 3 α₀` (`qirfp_ratio_ge`). The observed top sits strictly between the two one-loop
   attractors: above `2/9`, below the QCD quasi-fixed point.

**Verdict.** At one loop the value `0.993` is an empirical input (essentially `√2 · m_t / v`),
not a consequence of the gauge constraints. To reconcile the module with `173 GeV` its structure
has to change: either state `y_t` as a measured input, or replace the fixed-point claim by the
condition `R(m_t) ≥ 0.63` (numerically `R ≈ 0.64 – 0.76` for `m_t ∈ [171, 175]`,
`g₃ ∈ [1.16, 1.23]`; see the report), or run the full two-loop flow with threshold
corrections from a stated high-scale boundary condition — which this repository does not
formalise.
-/

namespace QBX.Notes.TopQuarkAudit

open Real

/-! ## 1. The gauge constraint -/

/-- One-loop `d(y_t²)/dt` (up to the positive factor `2/(16π²)`), in terms of squared couplings
`y = y_t²`, `a3 = g₃²`, `a2 = g₂²`, `a1 = g'²`. -/
noncomputable def betaYt2 (y a3 a2 a1 : ℝ) : ℝ :=
  y * (9 / 2 * y - 8 * a3 - 9 / 4 * a2 - 17 / 12 * a1)

/-- One-loop `d(g₃²)/dt` (same factor), `b₃ = −7`. -/
noncomputable def betaG32 (a3 : ℝ) : ℝ := -7 * a3 ^ 2

/-- Numerator of `d(y/a3)/dt` (quotient rule). -/
noncomputable def ratioDeriv (y a3 a2 a1 : ℝ) : ℝ := betaYt2 y a3 a2 a1 * a3 - y * betaG32 a3

/-- **The ratio `y_t²/g₃²` is stationary iff `y_t² = (2/9)(g₃² + 9/4 g₂² + 17/12 g'²)`.** -/
theorem ratio_stationary_iff (y a3 a2 a1 : ℝ) (hy : 0 < y) (ha : 0 < a3) :
    ratioDeriv y a3 a2 a1 = 0 ↔ y = 2 / 9 * (a3 + 9 / 4 * a2 + 17 / 12 * a1) := by
  have h : ratioDeriv y a3 a2 a1 = y * a3 * (9 / 2 * y - a3 - 9 / 4 * a2 - 17 / 12 * a1) := by
    unfold ratioDeriv betaYt2 betaG32; ring
  rw [h]
  constructor
  · intro h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (mul_pos hy ha).ne'
    · linarith
  · intro h1; rw [h1]; ring

/-- Without electroweak couplings this is the Pendleton–Ross value `R* = 2/9`. -/
theorem ratio_stationary_iff_qcd (y a3 : ℝ) (hy : 0 < y) (ha : 0 < a3) :
    ratioDeriv y a3 0 0 = 0 ↔ y / a3 = 2 / 9 := by
  rw [ratio_stationary_iff y a3 0 0 hy ha, div_eq_iff ha.ne']
  constructor <;> intro h <;> linarith

/-! ## 2. The gauge-constrained coupling gives less than 140 GeV -/

/-- Higgs vacuum expectation value (GeV), as in the audited module. -/
def vHiggs : ℝ := 246.22

/-- Tree-level top mass from the coupling: `m_t = y_t v / √2`. -/
noncomputable def mtOf (yt : ℝ) : ℝ := yt * vHiggs / Real.sqrt 2

theorem mtOf_sq (yt : ℝ) : mtOf yt ^ 2 = yt ^ 2 * vHiggs ^ 2 / 2 := by
  rw [mtOf, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **For physical gauge couplings the gauge-constrained top mass is below 140 GeV.** -/
theorem mt_gauge_constrained_lt (yt g3 g2 g1 : ℝ) (h3 : 0 ≤ g3) (h3' : g3 ≤ 1.23)
    (h2 : 0 ≤ g2) (h2' : g2 ≤ 0.66) (h1 : 0 ≤ g1) (h1' : g1 ≤ 0.37)
    (hfix : yt ^ 2 = 2 / 9 * (g3 ^ 2 + 9 / 4 * g2 ^ 2 + 17 / 12 * g1 ^ 2)) :
    mtOf yt < 140 := by
  have hy : yt ^ 2 < 0.6 := by
    rw [hfix]
    nlinarith [mul_le_mul h3' h3' h3 (by norm_num), mul_le_mul h2' h2' h2 (by norm_num),
      mul_le_mul h1' h1' h1 (by norm_num)]
  have hsq : mtOf yt ^ 2 < 140 ^ 2 := by
    rw [mtOf_sq, vHiggs]; nlinarith
  by_contra hc
  push_neg at hc
  nlinarith

/-! ## 3. What 173 GeV requires -/

/-- **`m_t ≥ 171 GeV` with `g₃ ≤ 1.23` forces `R = y_t²/g₃² ≥ 0.63`.** -/
theorem ratio_needed_ge (yt g3 : ℝ) (h3 : 0 < g3) (h3' : g3 ≤ 1.23) (hm : 171 ≤ mtOf yt) :
    0.63 ≤ yt ^ 2 / g3 ^ 2 := by
  have hm2 : 171 ^ 2 ≤ mtOf yt ^ 2 := by nlinarith
  rw [mtOf_sq, vHiggs] at hm2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul h3' h3' h3.le (by norm_num)]

/-- **`y_t = 0.993` with `R = 1.05` (the docstring's `R_phys`) needs `g₃ < 0.97`.** -/
theorem ratio_105_needs_small_g3 (g3 : ℝ) (h3 : 0 < g3) (h : (0.993 : ℝ) ^ 2 / g3 ^ 2 = 1.05) :
    g3 < 0.97 := by
  rw [div_eq_iff (by positivity)] at h
  nlinarith

/-! ## 4. The exact one-loop flow of the ratio (QCD only) -/

/-- `α(t) = g₃²(t) = α₀/(1 + 7 c α₀ t)`. -/
noncomputable def alphaFlow (c a0 t : ℝ) : ℝ := a0 / (1 + 7 * c * a0 * t)

/-- `u(t) = 1/R(t) = 9/2 + (u₀ − 9/2)(1 + 7 c α₀ t)^{1/7}`. -/
noncomputable def uFlow (c a0 u0 t : ℝ) : ℝ :=
  9 / 2 + (u0 - 9 / 2) * (1 + 7 * c * a0 * t) ^ (1 / 7 : ℝ)

/-- `dα/dt = −7 c α²` (one-loop running of `g₃²`, `b₃ = −7`). -/
theorem alphaFlow_hasDerivAt (c a0 t : ℝ) (ht : 0 < 1 + 7 * c * a0 * t) :
    HasDerivAt (alphaFlow c a0) (-7 * c * alphaFlow c a0 t ^ 2) t := by
  have hd : HasDerivAt (fun s => 1 + 7 * c * a0 * s) (7 * c * a0) t := by
    simpa using ((hasDerivAt_id t).const_mul (7 * c * a0)).const_add 1
  have := (hd.inv ht.ne').const_mul a0
  convert this using 1
  simp only [alphaFlow]; field_simp

/-- **`du/dt = −c α (9/2 − u)`**, i.e. `R = 1/u` obeys the one-loop equation
`dR/dt = c α R (9/2 R − 1)` with `α = g₃²`. -/
theorem uFlow_hasDerivAt (c a0 u0 t : ℝ) (ht : 0 < 1 + 7 * c * a0 * t) :
    HasDerivAt (uFlow c a0 u0) (-c * alphaFlow c a0 t * (9 / 2 - uFlow c a0 u0 t)) t := by
  have hd : HasDerivAt (fun s => 1 + 7 * c * a0 * s) (7 * c * a0) t := by
    simpa using ((hasDerivAt_id t).const_mul (7 * c * a0)).const_add 1
  have hp := (hd.rpow_const (p := (1 / 7 : ℝ)) (Or.inl ht.ne')).const_mul (u0 - 9 / 2)
  have := hp.const_add (9 / 2)
  convert this using 1
  simp only [uFlow, alphaFlow]
  have hx : (1 + 7 * c * a0 * t) ^ ((1 / 7 : ℝ) - 1) =
      (1 + 7 * c * a0 * t) ^ (1 / 7 : ℝ) / (1 + 7 * c * a0 * t) := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  rw [hx]
  field_simp
  ring

/-- **The deviation from the fixed point scales like `(α₀/α)^{1/7}`.** -/
theorem uFlow_deviation (c a0 u0 t : ℝ) (ha0 : 0 < a0) :
    uFlow c a0 u0 t - 9 / 2 = (u0 - 9 / 2) * (a0 / alphaFlow c a0 t) ^ (1 / 7 : ℝ) := by
  have : a0 / alphaFlow c a0 t = 1 + 7 * c * a0 * t := by
    rw [alphaFlow]; field_simp
  rw [this, uFlow]; ring

/-- **While `α` grows by at most a factor 3, at least 85 % of the deviation survives**:
`(α₀/α)^{1/7} ≥ 0.85` for `α₀/α ≥ 1/3`. -/
theorem deviation_factor_ge (ρ : ℝ) (hρ : 1 / 3 ≤ ρ) : 0.85 ≤ ρ ^ (1 / 7 : ℝ) := by
  have h1 : (0.85 : ℝ) = ((0.85 : ℝ) ^ (7 : ℝ)) ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num)]; norm_num
  rw [h1]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  have : (0.85 : ℝ) ^ (7 : ℝ) = 0.85 ^ (7 : ℕ) := by exact_mod_cast Real.rpow_natCast 0.85 7
  rw [this]; norm_num at hρ ⊢; linarith

/-! ## 5. The QCD quasi-infrared fixed point overshoots -/

/-- The quasi-infrared fixed point ratio: `u₀ = 0` (infinite Yukawa at the high scale), so
`R = 1 / ((9/2)(1 − ρ^{1/7}))` with `ρ = α₀/α`. -/
noncomputable def qirfpRatio (ρ : ℝ) : ℝ := 1 / (9 / 2 * (1 - ρ ^ (1 / 7 : ℝ)))

/-- **For `1/3 ≤ ρ < 1` the quasi-fixed-point ratio is at least `1.48`**, well above the
`≈ 0.64 – 0.76` needed for the observed top mass. -/
theorem qirfp_ratio_ge (ρ : ℝ) (hρ : 1 / 3 ≤ ρ) (hρ1 : ρ < 1) : 1.48 ≤ qirfpRatio ρ := by
  have h1 := deviation_factor_ge ρ hρ
  have h2 : ρ ^ (1 / 7 : ℝ) < 1 := Real.rpow_lt_one (by linarith) hρ1 (by norm_num)
  rw [qirfpRatio, le_div_iff₀ (by nlinarith)]
  nlinarith

end QBX.Notes.TopQuarkAudit
