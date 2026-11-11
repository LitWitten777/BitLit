import Mathlib
import RequestProject.Rotation.WindingAdapter

open scoped Classical BigOperators Real
open Filter Topology Complex

/-!
# Phase lift of a nonvanishing periodic loop from a continuous logarithm
(Run C, Task 2, target 1)

For a continuous, `1`-periodic, nonvanishing loop `b : ℝ → ℂ` that admits a
continuous logarithm `L` (`Complex.exp (L x) = b x`), we construct the **phase
lift**
```
  b(x) / ‖b(x)‖ = exp(2πi (d x + g x)),
```
where `d : ℤ` is the **winding number** (the integer with `L(x+1) - L(x) = 2πi d`)
and `g : ℝ → ℝ` is `1`-periodic.

This is the geometric input behind the phase-cocycle hypotheses of the
measurable winding obstruction: the integer `d` extracted here is exactly the
phase-lift degree appearing in `measurable_cocycle_winding_eq_zero_public`, and
`windingNumberIntegral_eq_of_phase_lift` confirms it equals the contour winding
number when `b` is `C¹`.

The continuous logarithm is taken as input (it exists for any continuous
nonvanishing loop on the simply connected line, by the standard lifting
theorem); the construction of `d` and the periodic remainder `g` is carried out
here.
-/

namespace CriticalMixedHRT

/-- `b` has a **phase lift** with degree `d` and periodic remainder `g` if its
normalization is `exp(2πi(d x + g x))` and `g` is `1`-periodic. -/
def HasPhaseLift (b : ℝ → ℂ) (d : ℤ) (g : ℝ → ℝ) : Prop :=
  Function.Periodic g 1 ∧
  ∀ x, b x / (‖b x‖ : ℂ) = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ)))

/-
**Phase lift from a continuous logarithm.**

If `b` is continuous, `1`-periodic, nonvanishing, and `L` is a continuous
logarithm of `b` (`exp (L x) = b x`), then `b` has a phase lift: there are an
integer winding degree `d` and a `1`-periodic real remainder `g` with
`b(x)/‖b(x)‖ = exp(2πi(d x + g x))`.
-/
theorem hasPhaseLift_of_continuous_log
    (b : ℝ → ℂ) (hb_cont : Continuous b) (hb_per : Function.Periodic b 1)
    (hb_ne : ∀ x, b x ≠ 0)
    (L : ℝ → ℂ) (hL_cont : Continuous L) (hL_exp : ∀ x, Complex.exp (L x) = b x) :
    ∃ (d : ℤ) (g : ℝ → ℝ), HasPhaseLift b d g := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, ∀ x, L (x + 1) - L x = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    -- By definition of $L$, we know that $L(x+1) - L(x) = 2\pi i d$ for some integer $d$.
    have h_diff : ∀ x, ∃ d : ℤ, L (x + 1) - L x = 2 * Real.pi * Complex.I * d := by
      intro x; have := Complex.exp_eq_exp_iff_exists_int.mp ( show Complex.exp ( L ( x + 1 ) ) = Complex.exp ( L x ) from by aesop ) ; obtain ⟨ d, hd ⟩ := this; exact ⟨ d, by linear_combination hd ⟩ ;
    choose d hd using h_diff;
    have h_const : Continuous d := by
      have h_const : Continuous (fun x => (L (x + 1) - L x) / (2 * Real.pi * Complex.I)) := by
        exact Continuous.div_const ( Continuous.sub ( hL_cont.comp ( continuous_add_right _ ) ) hL_cont ) _;
      simp_all +decide [ mul_div_cancel_left₀, Real.pi_ne_zero, Complex.I_ne_zero ];
      rw [ Metric.continuous_iff ] at *;
      intro b ε hε; specialize h_const b ε hε; rcases h_const with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro a ha; specialize H a ha; rw [ dist_eq_norm ] at *; norm_cast at *;
      erw [ Real.norm_eq_abs ] ; aesop;
    have h_const : IsConnected (Set.range d) := by
      exact isConnected_range h_const;
    have := h_const.isPreconnected.subsingleton;
    exact ⟨ d 0, fun x => by rw [ hd, this ( Set.mem_range_self x ) ( Set.mem_range_self 0 ) ] ; ring ⟩;
  refine' ⟨ d, fun x => Complex.im ( L x - ( d : ℂ ) * ( 2 * Real.pi * Complex.I ) * x ) / ( 2 * Real.pi ), ⟨ _, _ ⟩ ⟩;
  · intro x; simp +decide [ hd, mul_add ] ;
    have := hd x; norm_num [ Complex.ext_iff ] at this; linarith;
  · intro x; rw [ ← hL_exp x ] ; simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, div_eq_mul_inv ] ; ring;
    norm_num [ Complex.norm_exp, sq, mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ] ; ring_nf ;
    norm_num [ sq, mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ]

end CriticalMixedHRT