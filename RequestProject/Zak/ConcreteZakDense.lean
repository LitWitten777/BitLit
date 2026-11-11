import Mathlib

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the concrete classical Zak transform on a dense test class

This module defines the **classical Zak transform**

`concreteZakDense f x s := ∑' k : ℤ, f (x + k) * exp (-2π i k s)`

together with the concrete time-frequency shift `shiftFun a b` acting on
functions `ℝ → ℂ`, and proves — *unconditionally*, by reindexing of `tsum`s and
termwise congruence — the four covariance identities required by the abstract
`L2ZakModel` interface (`RequestProject/Zak/L2Zak.lean`):

* `concreteZakDense_periodic_s`       — `1`-periodicity in the frequency `s`;
* `concreteZakDense_quasiperiodic_x`  — Zak quasiperiodicity in the time `x`;
* `concreteZakDense_lattice_covariance_int` — integer lattice covariance;
* `concreteZakDense_rogue_covariance_real`  — real (rogue) covariance.

None of these need any summability hypothesis: periodicity in `s` is termwise
(`tsum_congr`), the rogue covariance pulls out a constant (`tsum_mul_left`) and
is then termwise, and the `x`-quasiperiodicity / lattice covariance reindex the
summation lattice by an integer (`Equiv.tsum_eq`).

These provide the concrete route to the `Zak`, `shift`, `Zak_periodic_s`,
`lattice_cov` and `rogue_cov` fields of `L2ZakModel`.  Linearity, the Plancherel
identity and the L²-extension live in the companion modules
`ConcreteZakPlancherel.lean`, `ConcreteL2ZakModel.lean` and
`ZakFubiniRegularity.lean`.
-/

namespace CriticalMixedHRT

/-- The classical Zak transform on the dense test class of functions `ℝ → ℂ`:
`Zf(x,s) = ∑' k : ℤ, f (x + k) · e^{-2π i k s}`. -/
noncomputable def concreteZakDense (f : ℝ → ℂ) (x s : ℝ) : ℂ :=
  ∑' k : ℤ, f (x + (k : ℝ)) * Complex.exp (-2 * ↑Real.pi * Complex.I * (k : ℂ) * (s : ℂ))

/-- The concrete time-frequency shift on functions:
`(shiftFun a b f)(t) = e^{-2π i b t} · f (t - a)`.  With this convention the Zak
transform satisfies the rogue covariance of `L2ZakModel`. -/
noncomputable def shiftFun (a b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (t : ℂ)) * f (t - a)

/-
**`1`-periodicity in the frequency variable** (termwise):
`Zf(x, s+1) = Zf(x, s)`.
-/
theorem concreteZakDense_periodic_s (f : ℝ → ℂ) (x s : ℝ) :
    concreteZakDense f x (s + 1) = concreteZakDense f x s := by
  convert tsum_congr fun k : ℤ => ?_ using 1;
  exact congrArg _ ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ -k, by push_cast; ring ⟩ )

/-
**Zak quasiperiodicity in the time variable**:
`Zf(x+1, s) = e^{2π i s} · Zf(x, s)`.
-/
theorem concreteZakDense_quasiperiodic_x (f : ℝ → ℂ) (x s : ℝ) :
    concreteZakDense f (x + 1) s =
      Complex.exp (2 * ↑Real.pi * Complex.I * (s : ℂ)) * concreteZakDense f x s := by
  unfold concreteZakDense; norm_num [ Complex.exp_add, mul_add, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  rw [ ← tsum_mul_left ] ; symm; rw [ ← Equiv.tsum_eq ( Equiv.addRight ( 1 : ℤ ) ) ] ; norm_num ; congr ; ext ; ring;
  rw [ mul_right_comm, ← Complex.exp_add ] ; ring

/-
**Integer lattice covariance**:
`Z(shiftFun m n f)(x,s) = e^{-2π i (n x + m s)} · Zf(x,s)` for `m n : ℤ`.
-/
theorem concreteZakDense_lattice_covariance_int (f : ℝ → ℂ) (m n : ℤ) (x s : ℝ) :
    concreteZakDense (shiftFun (m : ℝ) (n : ℝ) f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑n * ↑x + ↑m * ↑s) : ℂ)) *
        concreteZakDense f x s := by
  unfold concreteZakDense shiftFun;
  rw [ ← tsum_mul_left ] ; symm; rw [ ← Equiv.tsum_eq ( Equiv.addRight ( -m : ℤ ) ) ] ; norm_num ; ring;
  refine' tsum_congr fun k => _ ; ring;
  norm_num [ mul_assoc, mul_left_comm, ← Complex.exp_add ] ; ring;
  exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ n * k, by push_cast; ring ⟩ )

/-
**Real (rogue) covariance**:
`Z(shiftFun a b f)(x,s) = e^{-2π i b x} · Zf(x-a, s+b)` for `a b : ℝ`.
-/
theorem concreteZakDense_rogue_covariance_real (f : ℝ → ℂ) (a b : ℝ) (x s : ℝ) :
    concreteZakDense (shiftFun a b f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * (↑b : ℂ) * (↑x : ℂ)) *
        concreteZakDense f (x - a) (s + b) := by
  -- Unfold `concreteZakDense` and `shiftFun`.
  unfold concreteZakDense shiftFun;
  rw [ ← tsum_mul_left ] ; congr ; ext k ; push_cast ; ring;
  simpa only [ sub_eq_add_neg, Complex.exp_add ] using by ring;

end CriticalMixedHRT