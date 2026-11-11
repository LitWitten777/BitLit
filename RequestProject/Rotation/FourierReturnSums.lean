import Mathlib
import RequestProject.Rotation.ReturnData

open scoped Classical BigOperators Real
open Filter Topology Complex

/-!
# Finite Fourier-mode return sums (Stage 2A)

Working over an irrational rotation by `θ` equipped with return data
`R : RotationReturnData θ` (positive denominators `qₙ` and integers `pₙ` with
`qₙ θ - pₙ → 0`), we prove the two return-sum facts that feed the later
Denjoy–Koksma / measurable-winding steps.

* **One nonzero Fourier mode.**  For `k ≠ 0`,
  `∑_{j<qₙ} e^{2πi k (x - jθ)} → 0` uniformly in `x`, via the geometric-series
  identity
  `∑_{j<q} e^{2πi k (x-jθ)} = e^{2πi kx} (1 - e^{-2πi k qθ})/(1 - e^{-2πi kθ})`,
  whose numerator tends to `0` (because `qₙ θ - pₙ → 0`) while the denominator
  is a fixed nonzero number (because `θ` is irrational and `k ≠ 0`).

* **Finite mean-zero trigonometric polynomials.**  For a finite trigonometric
  polynomial `P(x) = ∑_{k ∈ s} a_k e^{2πi kx}` with `0 ∉ s` (mean zero),
  `‖∑_{j<qₙ} P(· - jθ)‖∞ → 0`, by linearity over the finitely many modes.

We encode finite trigonometric polynomials by a coefficient function
`a : ℤ → ℂ` together with a frequency support `s : Finset ℤ`.
-/

namespace CriticalMixedHRT

/-- The return sum of the single Fourier mode `x ↦ e^{2πi k x}` over the first
`N` steps of the rotation by `θ`:
`∑_{j<N} e^{2πi k (x - jθ)}`. -/
noncomputable def fourierModeReturnSum (θ : ℝ) (k : ℤ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N,
    Complex.exp (2 * π * Complex.I * (k : ℂ) * ((x : ℂ) - (j : ℂ) * (θ : ℂ)))

/-- A finite trigonometric polynomial `P(x) = ∑_{k ∈ s} a_k e^{2πi k x}`. -/
noncomputable def trigPoly (a : ℤ → ℂ) (s : Finset ℤ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, a k * Complex.exp (2 * π * Complex.I * (k : ℂ) * (x : ℂ))

/-
**Geometric-series form of a single-mode return sum.**
For `k ≠ 0` and irrational `θ`, writing `z = e^{-2πi k θ} ≠ 1`,
`∑_{j<N} e^{2πi k (x-jθ)} = e^{2πi kx} (z^N - 1)/(z - 1)`, hence its norm is
`‖z^N - 1‖ / ‖z - 1‖`, independent of `x`.
-/
theorem fourierModeReturnSum_norm_eq
    (θ : ℝ) (hθ : Irrational θ) (k : ℤ) (hk : k ≠ 0) (N : ℕ) (x : ℝ) :
    ‖fourierModeReturnSum θ k N x‖
      = ‖Complex.exp (-(2 * π * Complex.I * (k : ℂ) * (θ : ℂ))) ^ N - 1‖
          / ‖Complex.exp (-(2 * π * Complex.I * (k : ℂ) * (θ : ℂ))) - 1‖ := by
  -- Simplify the expression using the exponential property.
  have h_exp : fourierModeReturnSum θ k N x = Complex.exp (2 * Real.pi * Complex.I * k * x) * (∑ j ∈ Finset.range N, (Complex.exp (-(2 * Real.pi * Complex.I * k * θ))) ^ j) := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.exp_nat_mul ] ; rw [ ← Complex.exp_add ] ; ring;
  rw [ h_exp, geom_sum_eq ];
  · norm_num [ Complex.norm_exp ];
  · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
    rw [ Real.cos_eq_one_iff ] ; rintro ⟨ m, hm ⟩ ; exact False.elim <| hθ.ne_rat ( m / k ) <| by push_cast; rw [ eq_div_iff <| by positivity ] ; nlinarith [ Real.pi_pos ] ;

/-
**One nonzero Fourier mode return sum tends to zero, uniformly in `x`.**
For `k ≠ 0`, there is a null sequence `C n → 0` bounding the single-mode
return sum uniformly:
`‖∑_{j<qₙ} e^{2πi k (x-jθ)}‖ ≤ C n` for all `n, x`.
-/
theorem fourierModeReturnSum_uniform_bound
    {θ : ℝ} (R : RotationReturnData θ) (hθ : Irrational θ) (k : ℤ) (hk : k ≠ 0) :
    ∃ C : ℕ → ℝ, Tendsto C atTop (𝓝 0) ∧
      ∀ n x, ‖fourierModeReturnSum θ k (R.q n) x‖ ≤ C n := by
  refine' ⟨ _, _, fun n x => le_of_eq ( fourierModeReturnSum_norm_eq θ hθ k hk ( R.q n ) x ) ⟩;
  -- Since $z = e^{-2πi k θ}$ and $k ≠ 0$, $z$ is not equal to 1. Therefore, $z^{R.q n} → 1$ as $R.q n → ∞$.
  have h_z_pow : Filter.Tendsto (fun n => (Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (θ : ℂ)))) ^ (R.q n)) Filter.atTop (nhds 1) := by
    -- By definition of $R$, we know that $(R.q n : ℝ) * θ - (R.p n : ℝ) → 0$.
    have h_diff_zero : Filter.Tendsto (fun n => -(2 * Real.pi * Complex.I * (k : ℂ) * ((R.q n : ℝ) * θ - (R.p n : ℝ)))) Filter.atTop (nhds 0) := by
      convert Tendsto.const_mul ( - ( 2 * Real.pi * Complex.I * k ) ) ( Complex.continuous_ofReal.continuousAt.tendsto.comp R.tendsto_return ) using 2 ; norm_num;
      norm_num;
    convert Complex.continuous_exp.continuousAt.tendsto.comp h_diff_zero using 2 ; norm_num [ ← Complex.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm ];
    · convert Complex.exp_periodic.int_mul ( -k * R.p ‹_› ) _ using 2 ; push_cast ; ring;
    · norm_num;
  simpa using Filter.Tendsto.div_const ( Filter.Tendsto.norm ( h_z_pow.sub_const 1 ) ) _

/-
**One nonzero Fourier mode: uniform convergence to `0`.**
-/
theorem fourierModeReturnSum_tendstoUniformly
    {θ : ℝ} (R : RotationReturnData θ) (hθ : Irrational θ) (k : ℤ) (hk : k ≠ 0) :
    TendstoUniformly
      (fun n (x : ℝ) => fourierModeReturnSum θ k (R.q n) x) (fun _ => (0 : ℂ))
      atTop := by
  have := fourierModeReturnSum_uniform_bound R hθ k hk;
  rw [ Metric.tendstoUniformly_iff ];
  exact fun ε hε => by rcases this with ⟨ C, hC₁, hC₂ ⟩ ; filter_upwards [ hC₁.eventually ( gt_mem_nhds hε ) ] with n hn x using by simpa [ abs_of_nonneg ( show 0 ≤ C n from le_trans ( norm_nonneg _ ) ( hC₂ n x ) ) ] using lt_of_le_of_lt ( hC₂ n x ) hn;

/-
**Finite mean-zero trigonometric polynomial return sums tend to zero,
uniformly.**  If `0 ∉ s` (mean zero), then the return sums of
`P(x) = ∑_{k ∈ s} a_k e^{2πi kx}` satisfy
`‖∑_{j<qₙ} P(· - jθ)‖∞ → 0`.
-/
theorem trigPoly_return_uniform_bound
    {θ : ℝ} (R : RotationReturnData θ) (hθ : Irrational θ)
    (a : ℤ → ℂ) (s : Finset ℤ) (hs : (0 : ℤ) ∉ s) :
    ∃ C : ℕ → ℝ, Tendsto C atTop (𝓝 0) ∧
      ∀ n x, ‖∑ j ∈ Finset.range (R.q n), trigPoly a s ((x : ℝ) - j * θ)‖ ≤ C n := by
  obtain ⟨C, hC⟩ : ∃ C : ℤ → ℕ → ℝ, (∀ k ∈ s, Tendsto (C k) atTop (𝓝 0)) ∧ ∀ n x k, k ∈ s → ‖fourierModeReturnSum θ k (R.q n) x‖ ≤ C k n := by
    choose! C hC using fun k hk => fourierModeReturnSum_uniform_bound R hθ k ( show k ≠ 0 from fun h => hs <| h ▸ hk );
    exact ⟨ C, fun k hk => hC k hk |>.1, fun n x k hk => hC k hk |>.2 n x ⟩;
  refine' ⟨ fun n => ∑ k ∈ s, ‖a k‖ * C k n, _, _ ⟩;
  · simpa using tendsto_finset_sum _ fun k hk => Filter.Tendsto.const_mul _ ( hC.1 k hk );
  · intro n x; simp +decide [ trigPoly ] ;
    rw [ Finset.sum_comm ];
    refine' le_trans ( norm_sum_le _ _ ) _;
    exact Finset.sum_le_sum fun i hi => by simpa [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, fourierModeReturnSum ] using mul_le_mul_of_nonneg_left ( hC.2 n x i hi ) ( norm_nonneg ( a i ) ) ;

/-
**Finite mean-zero trigonometric polynomial: uniform convergence to `0`.**
-/
theorem trigPoly_return_tendstoUniformly
    {θ : ℝ} (R : RotationReturnData θ) (hθ : Irrational θ)
    (a : ℤ → ℂ) (s : Finset ℤ) (hs : (0 : ℤ) ∉ s) :
    TendstoUniformly
      (fun n (x : ℝ) => ∑ j ∈ Finset.range (R.q n), trigPoly a s ((x : ℝ) - j * θ))
      (fun _ => (0 : ℂ)) atTop := by
  obtain ⟨ C, hC₁, hC₂ ⟩ := trigPoly_return_uniform_bound R hθ a s hs;
  rw [ Metric.tendstoUniformly_iff ];
  exact fun ε ε_pos => by filter_upwards [ hC₁.eventually ( gt_mem_nhds ε_pos ) ] with n hn x using by simpa [ dist_eq_norm ] using lt_of_le_of_lt ( hC₂ n x ) hn;

end CriticalMixedHRT