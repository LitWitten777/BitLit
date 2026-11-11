import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.FourierReturnSums
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.Rotation.C1UniformReturnSums
import RequestProject.AnalyticRigidity

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex

/-!
# Stage 3A: measurable holonomy quantization (conditional form)

This module formalizes **Stage 3A** of the certification plan: the measurable
holonomy-quantization step, under the standing assumption that a periodic
logarithm of the multiplicative cocycle is already available.

The geometric situation (cf. Lemma 6.5 of the dossier) is the following.  Let
`θ` be irrational and let `D : DenjoyKoksmaReturnData θ` provide the
continued-fraction return times `qₙ`.  Let `h : ℝ → ℂ` be a nonzero
`L²`-function (over one period) and let `b : ℝ → ℂ` be a non-vanishing cocycle
satisfying the functional equation
```
  h (x - θ) = b x * h x.
```
Given a periodic logarithm `ell` of `b` (`exp (ell x) = b x`), set
```
  c   = ∫₀¹ ell,      φ = ell - c,      H = exp c.
```
The holonomy-quantization theorem asserts that
```
  H ^ qₙ → 1,
```
i.e. the holonomy `H` lies in the resonance group `G_θ`.

## Proof architecture

1. `cocycle_iterate` — iterating the one-step cocycle through the return time
   `N` gives the exact `N`-step identity
   `h (x - N θ) = H^N · exp (∑_{j<N} φ (x - jθ)) · h x`.
2. `tendstoUniformly_exp_returnSum` — the Stage 2B uniform return-sum theorem,
   composed with `exp`, gives `exp (∑_{j<qₙ} φ(· - jθ)) → 1` uniformly.
3. `eLpNorm_mul_sub_one_tendsto_zero` — multiplying a fixed `L²` function by a
   sequence converging to `1` uniformly converges to it in `L²`.
4. `holonomy_limit_one_of_uniform` — the abstract `L²` combination: if
   `h ∘ Tₙ =ᵐ Hₙ · gₙ · h` with `|Hₙ| = 1`, `gₙ → 1` uniformly and
   `h ∘ Tₙ → h` in `L²`, then `Hₙ → 1`.
5. `measurable_cocycle_holonomy_quantized_of_periodic_log` — the assembly.
6. `measurable_cocycle_holonomy_resonant` — the corollary placing `H` in the
   resonance group `resonanceGroupC D.q`.

`L²` translation continuity (`htrans`) is carried as an explicit hypothesis, as
permitted by the certification plan (Mathlib does not yet provide it in the form
needed here); it is **not** introduced as an axiom.
-/

namespace CriticalMixedHRT

/-
**`N`-step cocycle iteration.**

If `h (x - θ) = b x * h x` for every `x` and `exp (ell x) = b x`, then iterating
the one-step relation `N` times yields the exact identity
`h (x - N θ) = (exp c)^N · exp (∑_{j<N} (ell (x - jθ) - c)) · h x`,
for any chosen constant `c`.
-/
theorem cocycle_iterate
    {θ : ℝ} (h b ell : ℝ → ℂ) (c : ℂ)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x) :
    ∀ (N : ℕ) (x : ℝ),
      h (x - (N : ℝ) * θ)
        = Complex.exp c ^ N
          * Complex.exp (∑ j ∈ Finset.range N, (ell (x - (j : ℝ) * θ) - c))
          * h x := by
  intro N x;
  induction' N with N ih <;> simp_all +decide [ Finset.sum_range_succ ];
  convert congr_arg ( fun y => b ( x - N * θ ) * y ) ih using 1 <;> ring;
  · convert hcocycle ( x - N * θ ) using 1 ; ring;
  · rw [ ← hlog ] ; norm_num [ Complex.exp_add, Complex.exp_sub ] ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Complex.exp_ne_zero ]

/-
**Uniform convergence of the exponentiated return sums.**

From the Stage 2B uniform return-sum theorem (`c1_zeroMean_returnSum_tendstoUniformly`)
and the continuity of `exp`, the exponentiated continued-fraction return sums of
`φ` converge to `1` uniformly.
-/
theorem tendstoUniformly_exp_returnSum
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (φ : ℝ → ℂ) (happrox : TrigApproxInVariation D φ) :
    TendstoUniformly
      (fun n (x : ℝ) =>
        Complex.exp (∑ j ∈ Finset.range (D.q n), φ ((x : ℝ) - (j : ℝ) * θ)))
      (fun _ => (1 : ℂ)) atTop := by
  have := @c1_zeroMean_returnSum_tendstoUniformly;
  have := @this θ D hθ φ happrox;
  rw [ Metric.tendstoUniformly_iff ] at *;
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → ‖Complex.exp z - 1‖ < ε := by
    have := Metric.continuous_iff.mp ( show Continuous fun z : ℂ => Complex.exp z - 1 from by continuity ) 0 ε hε; aesop;
  filter_upwards [ this δ hδ_pos ] with n hn x using by simpa [ dist_eq_norm' ] using hδ _ ( by simpa [ dist_eq_norm' ] using hn x ) ;

/-
**`L²` multiplier convergence.**

If `gₙ → 1` uniformly and `h ∈ L²`, then `gₙ · h → h` in `L²`, i.e. the
`eLpNorm` of `gₙ · h - h` tends to `0`.
-/
theorem eLpNorm_mul_sub_one_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℂ) (hmem : MemLp h 2 μ)
    (gn : ℕ → α → ℂ) (hgmeas : ∀ n, AEStronglyMeasurable (gn n) μ)
    (hg : TendstoUniformly gn (fun _ => (1 : ℂ)) atTop) :
    Tendsto (fun n => eLpNorm (fun x => gn n x * h x - h x) 2 μ) atTop (𝓝 0) := by
  rw [ ENNReal.tendsto_nhds_zero ];
  intro ε hε;
  obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r * eLpNorm h 2 μ ≤ ε := by
    by_cases hM : eLpNorm h 2 μ = 0 ∨ eLpNorm h 2 μ = ⊤;
    · cases hM <;> simp_all +decide [ eLpNorm_eq_zero_iff ];
      · exact ⟨ 1, zero_lt_one ⟩;
      · exact absurd ‹_› ( ne_of_lt ( hmem.eLpNorm_lt_top ) );
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε / eLpNorm h 2 μ := by
        rcases ENNReal.lt_iff_exists_real_btwn.mp ( show 0 < ε / eLpNorm h 2 μ from ENNReal.div_pos_iff.mpr ⟨ hε.ne', by aesop ⟩ ) with ⟨ r, hr ⟩;
        exact ⟨ r, lt_of_le_of_ne hr.1 ( Ne.symm <| by aesop ), le_of_lt hr.2.2 ⟩;
      exact ⟨ r, hr.1, by rw [ ENNReal.le_div_iff_mul_le ( by aesop ) ( by aesop ) ] at hr; exact hr.2 ⟩;
  have h_pointwise : ∀ᶠ n in atTop, ∀ x, ‖gn n x - 1‖ ≤ r := by
    rw [ Metric.tendstoUniformly_iff ] at hg;
    simpa only [ dist_eq_norm', norm_sub_rev ] using hg r hr.1 |> fun h => h.mono fun n hn x => le_of_lt ( hn x );
  filter_upwards [ h_pointwise ] with n hn;
  refine' le_trans _ hr.2;
  convert eLpNorm_mono_ae _ using 1;
  convert MeasureTheory.eLpNorm_const_smul ( r : ℝ ) h 2 μ using 1;
  rw [ MeasureTheory.eLpNorm_const_smul ];
  rw [ Real.enorm_eq_ofReal hr.1.le ];
  convert MeasureTheory.eLpNorm_const_smul ( r : ℝ ) h 2 μ using 1;
  simp +decide [ - sub_mul ];
  filter_upwards [ ] with x using by rw [ show gn n x * h x - h x = ( gn n x - 1 ) * h x by ring ] ; exact by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( hn x ) ( le_abs_self _ ) ) ( norm_nonneg _ ) ;

/-
**Abstract holonomy-limit lemma.**

Let `μ` be a measure, `h ∈ L²(μ)` with positive `eLpNorm`, `Hₙ` scalars of
modulus one, `gₙ → 1` uniformly, and `Tₙ` a family of maps with
`h ∘ Tₙ =ᵐ Hₙ · gₙ · h`.  If additionally `h ∘ Tₙ → h` in `L²`, then
`Hₙ → 1`.
-/
theorem holonomy_limit_one_of_uniform
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℂ) (hmem : MemLp h 2 μ) (hpos : eLpNorm h 2 μ ≠ 0)
    (Hn : ℕ → ℂ) (hHn : ∀ n, ‖Hn n‖ = 1)
    (gn : ℕ → α → ℂ) (hgmeas : ∀ n, AEStronglyMeasurable (gn n) μ)
    (hg : TendstoUniformly gn (fun _ => (1 : ℂ)) atTop)
    (T : ℕ → α → α)
    (hrel : ∀ n, (fun x => h (T n x)) =ᵐ[μ] fun x => Hn n * gn n x * h x)
    (htrans : Tendsto (fun n => eLpNorm (fun x => h (T n x) - h x) 2 μ)
      atTop (𝓝 0)) :
    Tendsto Hn atTop (𝓝 1) := by
  -- From `hrel n`, the functions `fun x => h (T n x) - h x` and `fun x => (Hn n * gn n x * h x) - h x` are a.e. equal, so their eLpNorms are equal.
  have h_trans : Tendsto (fun n => eLpNorm (fun x => Hn n * gn n x * h x - h x) 2 μ) atTop (𝓝 0) := by
    refine' htrans.congr' _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ eLpNorm_congr_ae ( by filter_upwards [ hrel n ] with x hx; rw [ hx ] ) ] ;
  -- From `eLpNorm_mul_sub_one_tendsto_zero`, we get that `eLpNorm (fun x => Hn n * gn n x * h x - Hn n * h x) 2 μ` tends to 0.
  have h_mul_trans : Tendsto (fun n => eLpNorm (fun x => Hn n * gn n x * h x - Hn n * h x) 2 μ) atTop (𝓝 0) := by
    have h_mul_trans : Tendsto (fun n => eLpNorm (fun x => gn n x * h x - h x) 2 μ) atTop (𝓝 0) := by
      convert eLpNorm_mul_sub_one_tendsto_zero h hmem gn hgmeas hg using 1;
    convert h_mul_trans using 2;
    convert eLpNorm_const_smul ( Hn ‹_› ) ( fun x => gn ‹_› x * h x - h x ) 2 μ using 1 ; ring;
    · exact congr_arg ( fun f => eLpNorm f 2 μ ) ( funext fun x => by simp +decide [ mul_sub, mul_assoc ] );
    · simp +decide [ ENorm.enorm ];
      simp +decide [ ← ENNReal.ofReal_coe_nnreal, hHn ];
  -- From `h_trans` and `h_mul_trans`, we get that `eLpNorm (fun x => (Hn n - 1) * h x) 2 μ` tends to 0.
  have h_diff_trans : Tendsto (fun n => eLpNorm (fun x => (Hn n - 1) * h x) 2 μ) atTop (𝓝 0) := by
    have h_diff_trans : ∀ n, eLpNorm (fun x => (Hn n - 1) * h x) 2 μ ≤ eLpNorm (fun x => Hn n * gn n x * h x - h x) 2 μ + eLpNorm (fun x => Hn n * gn n x * h x - Hn n * h x) 2 μ := by
      intro n
      have h_triangle : eLpNorm (fun x => (Hn n * gn n x * h x - h x) - (Hn n * gn n x * h x - Hn n * h x)) 2 μ ≤ eLpNorm (fun x => Hn n * gn n x * h x - h x) 2 μ + eLpNorm (fun x => Hn n * gn n x * h x - Hn n * h x) 2 μ := by
        convert MeasureTheory.eLpNorm_sub_le _ _ _ using 1;
        · exact MeasureTheory.AEStronglyMeasurable.sub ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) ( hgmeas n ) ) hmem.aestronglyMeasurable ) hmem.aestronglyMeasurable;
        · exact MeasureTheory.AEStronglyMeasurable.sub ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) ( hgmeas n ) ) hmem.aestronglyMeasurable ) ( MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.aestronglyMeasurable_const ) hmem.aestronglyMeasurable );
        · norm_num;
      convert h_triangle using 3 ; ring;
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ( by simpa using h_trans.add h_mul_trans ) ( fun n => zero_le _ ) h_diff_trans;
  -- From `h_diff_trans`, we get that `‖Hn n - 1‖ₑ * eLpNorm h 2 μ` tends to 0.
  have h_norm_diff_trans : Tendsto (fun n => ‖Hn n - 1‖ₑ * eLpNorm h 2 μ) atTop (𝓝 0) := by
    convert h_diff_trans using 2;
    convert eLpNorm_const_smul ( Hn ‹_› - 1 ) h 2 μ |> Eq.symm using 1;
  -- Since `eLpNorm h 2 μ ≠ 0`, we can divide both sides of the equation by `eLpNorm h 2 μ`.
  have h_div : Tendsto (fun n => ‖Hn n - 1‖ₑ) atTop (𝓝 0) := by
    convert ENNReal.Tendsto.div_const h_norm_diff_trans _ using 1;
    any_goals exact eLpNorm h 2 μ;
    · ext n; rw [ ENNReal.mul_div_cancel_right ] ; aesop;
      exact hmem.eLpNorm_lt_top.ne;
    · rw [ ENNReal.div_eq_inv_mul ] ; aesop;
    · exact Or.inr hpos;
  convert ENNReal.tendsto_toReal ( show ( 0 : ENNReal ) ≠ ⊤ by simp +decide ) |> Filter.Tendsto.comp <| h_div using 1;
  rw [ tendsto_iff_norm_sub_tendsto_zero ] ; aesop;

/-
**Stage 3A: measurable holonomy quantization (conditional form).**

Let `θ` be irrational with Denjoy–Koksma return data `D`.  Let `h : ℝ → ℂ` be
a nonzero `L²`-function over one period `Ioc 0 1`, and `b` a non-vanishing
cocycle with `h (x - θ) = b x * h x`.  Given a periodic logarithm `ell` of `b`
with `∫₀¹ Re(ell) = 0` (`|H| = 1`), and the Stage 2B variation-approximation
hypothesis for `φ = ell - ∫₀¹ ell`, and `L²` translation continuity along the
return times, the holonomy `H = exp (∫₀¹ ell)` satisfies `H ^ qₙ → 1`.
-/
theorem measurable_cocycle_holonomy_quantized_of_periodic_log
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (h b ell : ℝ → ℂ)
    (hell_meas : Measurable ell)
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (hRe : (∫ y in Set.Ioc (0 : ℝ) 1, ell y).re = 0)
    (happrox : TrigApproxInVariation D
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y))
    (htrans : Tendsto
        (fun n => eLpNorm (fun x => h (x - (D.q n : ℝ) * θ) - h x) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0)) :
    Tendsto (fun n => Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y) ^ (D.q n))
        atTop (𝓝 1) := by
  convert holonomy_limit_one_of_uniform h hmem hpos _ _ _ _ _ _ _ htrans;
  rotate_left;
  use fun n x => Complex.exp ( ∑ j ∈ Finset.range ( D.q n ), ( ell ( x - j * θ ) - ∫ y in Set.Ioc 0 1, ell y ) );
  · exact fun n => Measurable.aestronglyMeasurable ( by measurability );
  · convert tendstoUniformly_exp_returnSum hθ D ( fun x => ell x - ∫ y in Set.Ioc 0 1, ell y ) happrox using 1;
  · intro n; filter_upwards [ ] with x; convert cocycle_iterate h b ell ( ∫ y in Set.Ioc 0 1, ell y ) hcocycle hlog ( D.q n ) x using 1;
  · norm_num [ Complex.norm_exp, hRe ]

/-
**Corollary: the holonomy lies in the resonance group.**

Under the hypotheses of `measurable_cocycle_holonomy_quantized_of_periodic_log`,
the holonomy `H = exp (∫₀¹ ell)` belongs to the resonance group
`resonanceGroupC D.q = {ζ : ‖ζ‖ = 1 ∧ ζ^{qₙ} → 1}`.
-/
theorem measurable_cocycle_holonomy_resonant
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (h b ell : ℝ → ℂ)
    (hell_meas : Measurable ell)
    (hmem : MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hpos : eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0)
    (hcocycle : ∀ x, h (x - θ) = b x * h x)
    (hlog : ∀ x, Complex.exp (ell x) = b x)
    (hRe : (∫ y in Set.Ioc (0 : ℝ) 1, ell y).re = 0)
    (happrox : TrigApproxInVariation D
        (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y))
    (htrans : Tendsto
        (fun n => eLpNorm (fun x => h (x - (D.q n : ℝ) * θ) - h x) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0)) :
    Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y) ∈ resonanceGroupC D.q := by
  refine' ⟨ _, _ ⟩;
  · norm_num [ Complex.norm_exp, hRe ];
  · convert measurable_cocycle_holonomy_quantized_of_periodic_log hθ D h b ell hell_meas hmem hpos hcocycle hlog hRe happrox htrans using 1

end CriticalMixedHRT