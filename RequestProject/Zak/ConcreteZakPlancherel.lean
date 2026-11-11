import Mathlib
import RequestProject.Zak.ConcreteZakDense

open scoped Classical BigOperators Real
open Complex MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Stage 6B — orthogonality and the finite-support Plancherel identity

The unitarity of the Zak transform rests on the orthonormality of the integer
Fourier characters `t ↦ e^{-2π i k t}` on the unit interval `[0,1]`.  This module
proves that orthogonality in the self-contained form

* `intervalIntegral_exp_two_pi_int` — `∫₀¹ e^{2π i m t} dt = if m = 0 then 1 else 0`;

and deduces the **finite-support (per-fibre) Plancherel identity**

* `finiteSupportZak_plancherel` —
  `∫₀¹ ‖∑ k ∈ s, c k · e^{-2π i k t}‖² dt = ∑ k ∈ s, ‖c k‖²`

for any finite coefficient family `c : ℤ → ℂ` supported on `s : Finset ℤ`.  This
is exactly the per-fibre Parseval identity for the concrete Zak transform
`concreteZakDense` applied to a window whose integer translates have finite
support; it is the orthogonality core of the full L²(ℝ) Plancherel identity
(`∫₀¹∫₀¹ ‖Zf‖² = ∫_ℝ ‖f‖²`), whose remaining content is the Tonelli swap plus the
decomposition of `∫_ℝ` into integer unit intervals.
-/

namespace CriticalMixedHRT

/-
**Orthogonality of integer Fourier characters on `[0,1]`.**
`∫₀¹ e^{2π i m t} dt = 1` if `m = 0` and `0` otherwise.
-/
theorem intervalIntegral_exp_two_pi_int (m : ℤ) :
    (∫ t in (0:ℝ)..1, Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (t : ℂ)))
      = if m = 0 then 1 else 0 := by
  split_ifs with hm;
  · norm_num [ hm ];
  · have := @integral_exp_mul_complex;
    rw [ this ( by norm_num [ Complex.ext_iff, Real.pi_ne_zero, hm ] ) ];
    norm_num [ mul_comm ( 2 * Real.pi * Complex.I ) ]

/-
**Finite-support (per-fibre) Plancherel identity.**
For a finite coefficient family `c` supported on `s`,
`∫₀¹ ‖∑ k ∈ s, c k · e^{-2π i k t}‖² dt = ∑ k ∈ s, ‖c k‖²`.
-/
theorem finiteSupportZak_plancherel (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t in (0:ℝ)..1,
        ‖∑ k ∈ s, c k * Complex.exp (-2 * ↑Real.pi * Complex.I * (k : ℂ) * (t : ℂ))‖ ^ 2)
      = ∑ k ∈ s, ‖c k‖ ^ 2 := by
  -- Expand the square of the absolute value and interchange the order of summation and integration.
  have h_expand : ∫ t in (0:ℝ)..1, ‖∑ k ∈ s, c k * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))‖ ^ 2 = ∑ j ∈ s, ∑ k ∈ s, c j * starRingEnd ℂ (c k) * ∫ t in (0:ℝ)..1, Complex.exp (-2 * Real.pi * Complex.I * (j - k) * (t : ℂ)) := by
    have h_expand : ∀ t : ℝ, ‖∑ k ∈ s, c k * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))‖ ^ 2 = ∑ j ∈ s, ∑ k ∈ s, c j * starRingEnd ℂ (c k) * Complex.exp (-2 * Real.pi * Complex.I * (j - k) * (t : ℂ)) := by
      intro t
      have h_expand : ‖∑ k ∈ s, c k * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))‖ ^ 2 = (∑ k ∈ s, c k * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))) * (∑ k ∈ s, starRingEnd ℂ (c k) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))) := by
        have h_expand : ∀ (z : ℂ), ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        convert h_expand _ using 2 ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      rw [ h_expand, Finset.sum_mul ];
      simp +decide only [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _] ; congr ; ext ; ring;
      exact Finset.sum_congr rfl fun _ _ => by rw [ Complex.exp_add ] ; ring;
    convert intervalIntegral.integral_congr fun t ht => h_expand t using 1;
    convert intervalIntegral.integral_ofReal.symm using 1;
    congr! 1;
    · norm_num [ Complex.ext_iff, sq ];
    · rw [ intervalIntegral.integral_finset_sum ];
      · rw [ Finset.sum_congr rfl ] ; intros ; rw [ intervalIntegral.integral_finset_sum ] ; aesop;
        exact fun _ _ => Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact fun _ _ => Continuous.intervalIntegrable ( by continuity ) _ _;
  -- Evaluate the integral $\int_0^1 e^{-2\pi i (j-k) t} dt$.
  have h_integral : ∀ j k : ℤ, ∫ t in (0:ℝ)..1, Complex.exp (-2 * Real.pi * Complex.I * (j - k) * (t : ℂ)) = if j = k then 1 else 0 := by
    intro j k; split_ifs <;> simp_all +decide [ Complex.exp_ne_zero ];
    have := @integral_exp_mul_complex 0 1;
    convert @this ( - ( 2 * Real.pi * Complex.I * ( j - k ) ) ) ( neg_ne_zero.mpr <| mul_ne_zero ( mul_ne_zero ( mul_ne_zero two_ne_zero <| Complex.ofReal_ne_zero.mpr Real.pi_ne_zero ) <| Complex.I_ne_zero ) <| sub_ne_zero.mpr <| Int.cast_injective.ne ‹_› ) using 1 ; norm_num;
    exact Eq.symm ( div_eq_zero_iff.mpr <| Or.inl <| sub_eq_zero.mpr <| Complex.exp_eq_exp_iff_exists_int.mpr ⟨ - ( j - k ), by push_cast; ring ⟩ );
  rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;

/-
For a window `f` supported in `[0, N)` and a base point `x ∈ [0,1)`, the
concrete Zak transform reduces to the finite sum over the `N` integer translates
that fall in the support window.
-/
theorem concreteZakDense_eq_finsum_of_supp (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) 1) (s : ℝ) :
    concreteZakDense f x s =
      ∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ),
        f (x + (k : ℝ)) * Complex.exp (-2 * ↑Real.pi * Complex.I * (k : ℂ) * (s : ℂ)) := by
  refine tsum_eq_sum ?_;
  simp +zetaDelta at *;
  exact fun k hk => hsupp _ fun _ => by linarith [ show ( k : ℝ ) ≥ N by exact_mod_cast hk ( by exact_mod_cast Int.le_of_lt_add_one ( by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ) ] ;

/-
**Per-fibre Plancherel for finite-support windows.**
For `f` supported in `[0,N)` and `x ∈ [0,1)`,
`∫₀¹ ‖Zf(x,s)‖² ds = ∑_{k=0}^{N-1} ‖f(x+k)‖²`.
-/
theorem concreteZakDense_norm_sq_integral (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (x : ℝ) (hx : x ∈ Set.Ico (0:ℝ) 1) :
    (∫ s in (0:ℝ)..1, ‖concreteZakDense f x s‖ ^ 2)
      = ∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), ‖f (x + (k : ℝ))‖ ^ 2 := by
  convert finiteSupportZak_plancherel ( Finset.Ico 0 ( N : ℤ ) ) ( fun k => f ( x + k ) ) using 1;
  refine' intervalIntegral.integral_congr fun s _ => _;
  rw [ concreteZakDense_eq_finsum_of_supp N f hsupp x hx s ]

/-
**Total `x`-mass identity.**
For `f` supported in `[0,N)`, measurable, with integrable square,
`∫ x in 0..1, (∑_{k=0}^{N-1} ‖f(x+k)‖²) dx = ∫_ℝ ‖f t‖² dt`.
-/
theorem finsum_integral_translate_eq_real (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hint : MeasureTheory.Integrable (fun t => ‖f t‖ ^ 2) MeasureTheory.volume) :
    (∫ x in (0:ℝ)..1, ∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), ‖f (x + (k : ℝ))‖ ^ 2)
      = ∫ t, ‖f t‖ ^ 2 := by
  convert intervalIntegral.integral_finset_sum _ using 1;
  · -- By translation invariance, we can rewrite the integral over each interval [i, i+1] as the integral over [0,1].
    have h_translation : ∀ i : ℕ, ∫ x in (i : ℝ)..((i + 1) : ℝ), ‖f x‖ ^ 2 = ∫ x in (0 : ℝ)..1, ‖f (x + i)‖ ^ 2 := by
      intro i; rw [ intervalIntegral.integral_comp_add_right fun x => ‖f x‖ ^ 2 ] ; ring;
    have h_sum_translation : ∫ x in Set.Ico (0 : ℝ) (N : ℝ), ‖f x‖ ^ 2 = ∑ i ∈ Finset.range N, ∫ x in (i : ℝ)..((i + 1) : ℝ), ‖f x‖ ^ 2 := by
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ];
      · symm;
        convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
        exact fun k hk => by simpa using ‹Integrable ( fun t => ‖f t‖ ^ 2 ) volume›.intervalIntegrable;
      · positivity;
    convert h_sum_translation using 1;
    · rw [ MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ] ; aesop;
    · refine' Finset.sum_bij ( fun i hi => Int.natAbs i ) _ _ _ _ <;> norm_num;
      · exact fun a ha₁ ha₂ => by linarith [ abs_of_nonneg ha₁ ] ;
      · intros; omega;
      · exact fun b hb => ⟨ b, ⟨ Nat.cast_nonneg _, Nat.cast_lt.mpr hb ⟩, rfl ⟩;
      · intro a ha₁ ha₂; rw [ abs_of_nonneg ( by positivity ) ] ; specialize h_translation ( Int.natAbs a ) ; cases a <;> aesop;
  · exact fun _ _ => ( by exact ( by simpa using ( MeasureTheory.Integrable.comp_add_right ( by assumption ) _ ) |> MeasureTheory.Integrable.intervalIntegrable ) )

/-
**Concrete dense-class Plancherel identity.**
For a bounded, measurable window `f` supported in `[0,N)`,
`∫₀¹ ∫₀¹ ‖Zf(x,s)‖² dx ds = ∫_ℝ ‖f t‖² dt`.

The class of bounded measurable functions supported in a bounded interval is
dense in `L²(ℝ)` (it contains step functions and continuous compactly supported
functions); the boundedness makes all the finite-sum/integral interchanges and
integrability side-conditions in the Plancherel computation immediate.
-/
theorem concreteZakDense_plancherel (N : ℕ) (f : ℝ → ℂ)
    (hsupp : ∀ t, t ∉ Set.Ico (0:ℝ) (N:ℝ) → f t = 0)
    (hmeas : Measurable f)
    (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (∫ s in (0:ℝ)..1, ∫ x in (0:ℝ)..1, ‖concreteZakDense f x s‖ ^ 2)
      = ∫ t, ‖f t‖ ^ 2 := by
  obtain ⟨ C, hC ⟩ := hbdd;
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫ s in (0:ℝ)..1, ∫ x in (0:ℝ)..1, ‖(∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), f (x + (k : ℝ)) * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)))‖ ^ 2 = ∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..1, ‖(∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), f (x + (k : ℝ)) * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)))‖ ^ 2 := by
    have h_fubini : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ‖∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), f (p.1 + (k : ℝ)) * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (p.2 : ℂ))‖ ^ 2) (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun p => ( ∑ k ∈ Finset.Ico 0 ( N : ℤ ), C ) ^ 2;
      · norm_num +zetaDelta at *;
        exact Continuous.integrableOn_Icc ( by continuity );
      · fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Icc.prod measurableSet_Icc ) ] with p hp;
        simp +zetaDelta at *;
        exact pow_le_pow_left₀ ( norm_nonneg _ ) ( le_trans ( norm_sum_le _ _ ) <| le_trans ( Finset.sum_le_sum fun _ _ => by simpa [ Complex.norm_exp ] using hC _ ) <| by norm_num ) _;
    have h_fubini : ∫ s in Set.Icc (0:ℝ) 1, ∫ x in Set.Icc (0:ℝ) 1, ‖∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), f (x + (k : ℝ)) * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ))‖ ^ 2 = ∫ x in Set.Icc (0:ℝ) 1, ∫ s in Set.Icc (0:ℝ) 1, ‖∑ k ∈ Finset.Ico (0:ℤ) (N:ℤ), f (x + (k : ℝ)) * Complex.exp (-2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ))‖ ^ 2 := by
      rw [ MeasureTheory.integral_integral_swap ];
      rw [ MeasureTheory.Measure.prod_restrict ];
      exact h_fubini.swap;
    simpa only [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one ] using h_fubini;
  convert h_fubini using 1;
  · refine' intervalIntegral.integral_congr fun s hs => _;
    rw [ intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one ];
    rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => _;
    rw [ concreteZakDense_eq_finsum_of_supp N f hsupp x ⟨ hx.1.le, hx.2 ⟩ s ];
  · convert ( finsum_integral_translate_eq_real N f hsupp _ ) |> Eq.symm using 1;
    · refine' intervalIntegral.integral_congr fun x hx => _;
      convert finiteSupportZak_plancherel ( Finset.Ico 0 ( N : ℤ ) ) ( fun k => f ( x + k ) ) using 1;
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Ico (0:ℝ) (N:ℝ)) := by
        refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun _ => C ^ 2, Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ico_subset_Icc_self, by exact ( hmeas.norm.pow_const 2 |> Measurable.aestronglyMeasurable ), Filter.Eventually.of_forall fun x => by simpa using pow_le_pow_left₀ ( norm_nonneg _ ) ( hC x ) 2 ];
      rwa [ MeasureTheory.integrableOn_iff_integrable_of_support_subset ] at h_integrable;
      exact fun x hx => Classical.not_not.1 fun hx' => hx <| by simp +decide [ hsupp x hx' ] ;

end CriticalMixedHRT