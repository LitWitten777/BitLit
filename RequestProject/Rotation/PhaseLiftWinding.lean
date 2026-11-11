import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.Rotation.OscillatoryIntegral

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

/-!
# Stage 3B: the measurable winding obstruction (phase-lift conditional form)

This module formalizes the **measurable winding obstruction** of the dossier
(Lemma 6.4 / the `wind = 0` step), in the phase-lift conditional form permitted
by the certification plan.

The geometric situation: `θ` is irrational, `D : DenjoyKoksmaReturnData θ`
provides the continued-fraction return times `qₙ`, and `u : ℝ → ℂ` is a
measurable `1`-periodic unit-modulus function (the normalized window
`u = h / ‖h‖`) satisfying the *phase cocycle*
```
  u (x - θ) = exp(2πi (d x + g x)) · u x,
```
where `d : ℤ` is the winding degree and `g : ℝ → ℝ` the periodic remainder.

The obstruction asserts `d = 0`.  The proof has the structure of the dossier:

* **Part B** (`phase_cocycle_iterate`): iterating the one-step phase cocycle
  through the return time `N` gives `u (x − Nθ) = exp(2πi Φₙ(x)) · u x`, where
  `Φₙ` is the explicit return phase `windingPhase`.
* **Part C** (`eLpNorm_phase_multiplier_tendsto_one`,
  `integral_tendsto_of_eLpNorm_sub_tendsto_zero`): from `|u| = 1` and `L²`
  translation continuity along return times, the phase multipliers
  `Ψₙ = exp(2πi Φₙ)` converge to `1` in `L²`, hence `∫₀¹ Ψₙ → 1`.
* **Part D** (imported from `OscillatoryIntegral`): if `d ≠ 0`, the
  oscillatory integration-by-parts estimate forces `∫₀¹ Ψₙ → 0`.

Two limits `1` and `0` of the same sequence are impossible, so `d = 0`.

As permitted by the fallback policy, the Part D oscillatory estimate enters as
an explicit hypothesis (`hosc`); it is **not** introduced as an axiom, and is
discharged from the explicit integration-by-parts bound by
`integral_tendsto_zero_of_ibp_bound`.
-/

namespace CriticalMixedHRT

/-- The explicit **return phase** `Φₙ` accumulated by iterating the one-step
phase cocycle `u(x−θ) = exp(2πi(d x + g x)) u(x)` through `N` steps:
```
  Φₙ(x) = d N x − d θ · N(N−1)/2 + ∑_{j<N} g(x − jθ).
```
-/
noncomputable def windingPhase (d : ℤ) (g : ℝ → ℝ) (θ : ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  (d : ℂ) * (N : ℂ) * (x : ℂ)
    - (d : ℂ) * (θ : ℂ) * ((N : ℂ) * ((N : ℂ) - 1) / 2)
    + ∑ j ∈ Finset.range N, ((g (x - (j : ℝ) * θ) : ℝ) : ℂ)

/-
**Part B — exact iteration of the phase cocycle.**

If `u(x−θ) = exp(2πi(d x + g x)) · u(x)` for all `x`, then iterating `N` times
gives `u(x − Nθ) = exp(2πi · Φₙ(x)) · u(x)` with `Φₙ = windingPhase d g θ N`.
-/
theorem phase_cocycle_iterate
    {θ : ℝ} (u : ℝ → ℂ) (d : ℤ) (g : ℝ → ℝ)
    (hstep : ∀ x, u (x - θ)
        = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))) * u x) :
    ∀ (N : ℕ) (x : ℝ),
      u (x - (N : ℝ) * θ)
        = Complex.exp (2 * π * Complex.I * windingPhase d g θ N x) * u x := by
  intro N x; induction' N with N ih generalizing x <;> simp_all +decide [ Finset.sum_range_succ, sub_mul ] ; ring;
  · unfold windingPhase; norm_num;
  · convert hstep ( x - N * θ ) using 1 <;> push_cast [ ih ] <;> ring;
    unfold windingPhase; norm_num [ add_comm, add_left_comm, add_assoc, Finset.sum_range_succ ] ; ring;
    simpa only [ mul_assoc, ← Complex.exp_add ] using by ring;

/-
**Part C (abstract) — `L²` convergence of the phase multipliers.**

Let `u` be unit-modulus a.e. and let `Ψₙ`, `Tₙ` satisfy the cocycle relation
`u ∘ Tₙ =ᵐ Ψₙ · u`.  If `u ∘ Tₙ → u` in `L²`, then `Ψₙ → 1` in `L²`.

The key point is that on `|u| = 1`, `Ψₙ − 1 = (u∘Tₙ − u) · conj u` has the same
modulus as `u∘Tₙ − u`.
-/
theorem eLpNorm_phase_multiplier_tendsto_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : α → ℂ) (hu1 : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    (Ψ : ℕ → α → ℂ) (T : ℕ → α → α)
    (hΨ : ∀ n, (fun x => u (T n x)) =ᵐ[μ] fun x => Ψ n x * u x)
    (htrans : Tendsto (fun n => eLpNorm (fun x => u (T n x) - u x) 2 μ)
        atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Ψ n x - 1) 2 μ) atTop (𝓝 0) := by
  refine' htrans.congr _;
  intro n
  have h_eq : ∀ᵐ x ∂μ, ‖u (T n x) - u x‖ = ‖Ψ n x - 1‖ := by
    filter_upwards [ hu1, hΨ n ] with x hx₁ hx₂;
    rw [ hx₂, show Ψ n x * u x - u x = ( Ψ n x - 1 ) * u x by ring, norm_mul, hx₁, mul_one ];
  rw [ eLpNorm_congr_norm_ae h_eq ]

/-
**Part C (integral form) — convergence of integrals from `L²` convergence.**

On a finite measure, if `Fₙ → L` in `L²` (i.e. `‖Fₙ − L‖₂ → 0`) and all
functions are integrable, then `∫ Fₙ → ∫ L`.
-/
theorem integral_tendsto_of_eLpNorm_sub_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (F : ℕ → α → ℂ) (L : α → ℂ)
    (hFint : ∀ n, Integrable (F n) μ) (hLint : Integrable L μ)
    (h : Tendsto (fun n => eLpNorm (fun x => F n x - L x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, L x ∂μ)) := by
  have hL2_to_L1 : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - L x) 1 μ) Filter.atTop (nhds 0) := by
    have hL2_to_L1 : ∀ n, eLpNorm (fun x => F n x - L x) 1 μ ≤ eLpNorm (fun x => F n x - L x) 2 μ * ENNReal.ofReal (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by
      intro n;
      convert MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ ( f := fun x => F n x - L x ) ( p := 1 ) ( q := 2 ) ?_ using 1 <;> norm_num;
      exact ⟨ fun h => fun _ => h, fun h => h ( hFint n |> Integrable.aestronglyMeasurable |> fun h => h.sub hLint.aestronglyMeasurable ) ⟩;
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _ _ _;
    use fun n => eLpNorm ( fun x => F n x - L x ) 2 μ * ENNReal.ofReal ( μ Set.univ |> ENNReal.toReal ) ^ ( 1 / 2 : ℝ );
    · convert ENNReal.Tendsto.mul_const h _ using 1 <;> norm_num;
    · exact Filter.Eventually.of_forall fun n => zero_le _;
    · exact Filter.Eventually.of_forall hL2_to_L1;
  convert tendsto_iff_norm_sub_tendsto_zero.mpr _;
  refine' squeeze_zero ( fun _ => norm_nonneg _ ) ( fun n => _ ) ( ENNReal.tendsto_toReal ( by simp +decide ) |> Filter.Tendsto.comp <| hL2_to_L1 );
  rw [ ← MeasureTheory.integral_sub ( hFint n ) ( hLint ) ];
  convert MeasureTheory.norm_integral_le_lintegral_norm ( fun x => F n x - L x ) using 1;
  simp +decide [ eLpNorm_one_eq_lintegral_enorm ]

/-
**Stage 3B target — the measurable winding obstruction (phase-lift form).**

Let `θ` be irrational with Denjoy–Koksma return data `D`, and let `u : ℝ → ℂ`
be a measurable `1`-periodic unit-modulus function satisfying the phase cocycle
`u(x−θ) = exp(2πi(d x + g x)) u(x)`.  Assume:

* `htrans` — `L²` translation continuity along the return times `qₙ` (Part C);
* `hosc` — if `d ≠ 0`, the oscillatory integration-by-parts estimate forces the
  period integrals of `Ψₙ = exp(2πi Φₙ)` to tend to `0` (Part D).

Then the winding degree vanishes: `d = 0`.
-/
theorem measurable_cocycle_winding_eq_zero_of_phase_lift
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (u : ℝ → ℂ) (hu_meas : Measurable u) (hu1 : ∀ x, ‖u x‖ = 1)
    (d : ℤ) (g : ℝ → ℝ)
    (hstep : ∀ x, u (x - θ)
        = Complex.exp (2 * π * Complex.I * ((d : ℂ) * (x : ℂ) + (g x : ℂ))) * u x)
    (htrans : Tendsto
        (fun n => eLpNorm (fun x => u (x - (D.q n : ℝ) * θ) - u x) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0))
    (hosc : d ≠ 0 →
        Tendsto (fun n => ∫ x in Set.Ioc (0 : ℝ) 1,
            Complex.exp (2 * π * Complex.I * windingPhase d g θ (D.q n) x))
          atTop (𝓝 0)) :
    d = 0 := by
  contrapose! hosc; have := htrans; simp_all +decide [ MeasureTheory.eLpNorm ] ;
  -- Apply the integral_tendsto_of_eLpNorm_sub_tendsto_zero theorem.
  have h_integral : Filter.Tendsto (fun n => ∫ x in Set.Ioc 0 1, u (x - (D.q n : ℝ) * θ) * (starRingEnd ℂ) (u x)) Filter.atTop (nhds (∫ x in Set.Ioc 0 1, u x * (starRingEnd ℂ) (u x))) := by
    apply integral_tendsto_of_eLpNorm_sub_tendsto_zero;
    · intro n; refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => 1;
      · norm_num;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( hu_meas.comp ( measurable_id.sub measurable_const ) ) ( Complex.continuous_conj.measurable.comp hu_meas ) );
      · simp [hu1];
    · simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    · convert htrans using 1;
      ext; simp +decide [ ← sub_mul, eLpNorm, eLpNorm' ] ;
      simp +decide [ hu1, ENorm.enorm ];
      simp +decide [ ← ENNReal.ofReal_coe_nnreal, hu1 ];
  -- By definition of $Ψ$, we know that $Ψ n x = u (x - (D.q n : ℝ) * θ) * (starRingEnd ℂ) (u x)$.
  have hΨ : ∀ n x, Complex.exp (2 * Real.pi * Complex.I * windingPhase d g θ (D.q n) x) = u (x - (D.q n : ℝ) * θ) * (starRingEnd ℂ) (u x) := by
    intro n x; have := phase_cocycle_iterate u d g hstep ( D.q n ) x; simp_all +decide [ Complex.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm ] ;
    simp +decide [ mul_left_comm ( u x ), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1 ];
  simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
  exact fun h => absurd ( tendsto_nhds_unique h h_integral ) ( by norm_num )

end CriticalMixedHRT