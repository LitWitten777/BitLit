import Mathlib
import RequestProject.Zak.L2Zak

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (Parts B & C) — Zak covariance theorems

These are the time-frequency covariance identities of the Zak transform,
extracted from the `L2ZakModel` interface.  They are the named theorems

* `zak_lattice_covariance_int` — integer lattice covariance;
* `zak_translation_integer` — integer translation `T_m`;
* `zak_modulation_integer` — integer modulation `M_n`;
* `zak_rogue_covariance_real` — real rogue covariance.
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (Z : L2ZakModel V)

/-- **Part B — integer lattice covariance.**
`Zak (M_n T_m f)(x,s) = e^{-2πi(n x + m s)} Zak f(x,s)`. -/
theorem zak_lattice_covariance_int (f : V) (m n : ℤ) (x s : ℝ) :
    Z.Zak (Z.shift (m : ℝ) (n : ℝ) f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑n * ↑x + ↑m * ↑s) : ℂ)) * Z.Zak f x s :=
  Z.lattice_cov f m n x s

/-- **Part B — integer translation covariance.**
`Zak (T_m f)(x,s) = e^{-2πi m s} Zak f(x,s)`. -/
theorem zak_translation_integer (f : V) (m : ℤ) (x s : ℝ) :
    Z.Zak (Z.shift (m : ℝ) (0 : ℝ) f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑m * ↑s) : ℂ)) * Z.Zak f x s := by
  have h := Z.lattice_cov f m 0 x s
  simpa using h

/-- **Part B — integer modulation covariance.**
`Zak (M_n f)(x,s) = e^{-2πi n x} Zak f(x,s)`. -/
theorem zak_modulation_integer (f : V) (n : ℤ) (x s : ℝ) :
    Z.Zak (Z.shift (0 : ℝ) (n : ℝ) f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * ((↑n * ↑x) : ℂ)) * Z.Zak f x s := by
  have h := Z.lattice_cov f 0 n x s
  simpa using h

/-- **Part C — real rogue covariance.**
`Zak (M_b T_a f)(x,s) = e^{-2πi b x} Zak f(x-a, s+b)`. -/
theorem zak_rogue_covariance_real (f : V) (a b : ℝ) (x s : ℝ) :
    Z.Zak (Z.shift a b f) x s =
      Complex.exp (-2 * ↑Real.pi * Complex.I * (↑b : ℂ) * (↑x : ℂ)) * Z.Zak f (x - a) (s + b) :=
  Z.rogue_cov f a b x s

end CriticalMixedHRT
