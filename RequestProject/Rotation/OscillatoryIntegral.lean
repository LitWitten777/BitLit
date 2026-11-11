import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology

/-!
# Stage 3B, Part D: the oscillatory integral contradiction

This module isolates the *analytic* half of the measurable winding obstruction:
the oscillatory-integral estimate that forces the period integrals of the phase
multipliers `Ψₙ = exp(2πi Φₙ)` to vanish in the limit when the winding degree
`d ≠ 0`.

The dossier obtains this via integration by parts:
```
  |∫₀¹ exp(2πi Φₙ)| ≤ ‖Φₙ''‖₁ / (2π (inf_x |Φₙ'|)²),
```
together with the Denjoy–Koksma control `inf_x |Φₙ'| ≥ |d| qₙ − C` and the
second-derivative bound `‖Φₙ''‖₁ ≤ C' qₙ`.

We provide two reusable, fully proved pieces:

* `oscillatory_ibp_quotient_tendsto_zero` — the elementary real-analysis fact
  that the integration-by-parts bound `C' qₙ / (2π (|d| qₙ − C)²)` tends to `0`
  as `qₙ → ∞` (numerator `∼ qₙ`, denominator `∼ qₙ²`).
* `integral_tendsto_zero_of_norm_le` — the squeeze: if the period integrals are
  eventually dominated by a sequence tending to `0`, then they tend to `0`.

Composing the two yields the "Part D" conclusion `∫ Ψₙ → 0` from the explicit
integration-by-parts bound, which is exactly the analytic hypothesis carried by
the phase-lift winding theorem.
-/

namespace CriticalMixedHRT

/-
**The integration-by-parts bound tends to zero.**

If `r n → ∞` and `dabs > 0`, then the integration-by-parts quotient
`Csec * r n / (2π (dabs * r n − Cvar)²)` tends to `0`: the numerator grows like
`r n` while the denominator grows like `(r n)²`.
-/
theorem oscillatory_ibp_quotient_tendsto_zero
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (Cvar Csec dabs : ℝ) (hdabs : 0 < dabs) :
    Tendsto
      (fun n => Csec * r n / (2 * π * (dabs * r n - Cvar) ^ 2))
      atTop (𝓝 0) := by
  -- Divide numerator and denominator by $r^2$.
  suffices h_div : Filter.Tendsto (fun n => Csec * (1 / r n) / (2 * Real.pi * (dabs - Cvar / r n) ^ 2)) Filter.atTop (nhds 0) by
    grind +locals;
  convert Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop hr ) ) ( tendsto_const_nhds.mul ( Filter.Tendsto.pow ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop hr ) ) 2 ) ) _ using 2 <;> norm_num [ hdabs.ne.symm, Real.pi_ne_zero ]

/-
**Squeeze to zero for the period integrals.**

If the period integrals `∫₀¹ Ψₙ` are eventually dominated in norm by a real
sequence `bound n` that tends to `0`, then they tend to `0`.  This is the
abstract form of the oscillatory contradiction: the integration-by-parts
estimate supplies `hbd`, and `oscillatory_ibp_quotient_tendsto_zero` supplies
`hbound`.
-/
theorem integral_tendsto_zero_of_norm_le
    (Ψ : ℕ → ℝ → ℂ) (bound : ℕ → ℝ)
    (hbound : Tendsto bound atTop (𝓝 0))
    (hbd : ∀ᶠ n in atTop,
        ‖∫ x in Set.Ioc (0 : ℝ) 1, Ψ n x‖ ≤ bound n) :
    Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1, Ψ n x) atTop (𝓝 0) := by
  exact squeeze_zero_norm' hbd hbound

/-- **Part D: the oscillatory contradiction (from the explicit IBP bound).**

If the period integrals satisfy the integration-by-parts estimate
`‖∫₀¹ Ψₙ‖ ≤ Csec * qₙ / (2π (dabs qₙ − Cvar)²)` eventually, with `dabs > 0` and
`qₙ → ∞`, then `∫₀¹ Ψₙ → 0`. -/
theorem integral_tendsto_zero_of_ibp_bound
    {θ : ℝ} (D : DenjoyKoksmaReturnData θ)
    (Ψ : ℕ → ℝ → ℂ) (Cvar Csec dabs : ℝ) (hdabs : 0 < dabs)
    (hq : Tendsto (fun n => (D.q n : ℝ)) atTop atTop)
    (hbd : ∀ᶠ n in atTop,
        ‖∫ x in Set.Ioc (0 : ℝ) 1, Ψ n x‖
          ≤ Csec * (D.q n : ℝ) / (2 * π * (dabs * (D.q n : ℝ) - Cvar) ^ 2)) :
    Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1, Ψ n x) atTop (𝓝 0) :=
  integral_tendsto_zero_of_norm_le Ψ _
    (oscillatory_ibp_quotient_tendsto_zero (fun n => (D.q n : ℝ)) hq Cvar Csec dabs hdabs)
    hbd

end CriticalMixedHRT