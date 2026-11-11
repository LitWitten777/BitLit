import Mathlib
import RequestProject.Zak.ConcreteZakDense
import RequestProject.Zak.ConcreteZakPlancherel
import RequestProject.Zak.ConcreteZakDenseSubspace
import RequestProject.Zak.ConcreteZakAEModel

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the Lp-valued dense Zak map (TASKs B/C/D)

This module builds the concrete densely-defined Zak transform as a genuine
**linear isometry** from the dense test subspace `concreteZakDenseSubspace` of
`L²(ℝ) = Lp ℂ 2 volume` into the concrete target `ZakTarget = L²([0,1]²)`.

The analytic core is the Plancherel identity `concreteZakDense_plancherel`
(proved in `ConcreteZakPlancherel.lean`), upgraded here to:

* `concreteZakDense_memLp` — the per-element Zak square-function lies in
  `L²([0,1]²)` (`MemLp ... 2 zakSquareMeasure`);
* `concreteZakDense_to_Lp` — its `Lp`-class;
* `concreteZakDense_to_Lp_add` / `_smul` / `concreteZakDense_to_Lp_linearMap`
  — linearity into `Lp`;
* `concreteZakDense_to_Lp_norm` / `concreteZakDense_to_Lp_isometry`
  / `concreteZakDense_to_Lp_linearIsometry` — the isometry (Plancherel).
-/

namespace CriticalMixedHRT

noncomputable section

/-- The Zak transform of `g` as a function on the plane (restricted to the
square by the target measure `zakSquareMeasure`). -/
def zakSquareFun (g : ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => concreteZakDense g p.1 p.2

/-
For a compactly supported window, each integer-translate Zak series is a
finite (hence summable) sum.
-/
theorem concreteZakDense_summable (g : ℝ → ℂ) (hgs : HasCompactSupport g) (x s : ℝ) :
    Summable (fun k : ℤ => g (x + (k : ℝ)) *
      Complex.exp (-2 * ↑Real.pi * Complex.I * (k : ℂ) * (s : ℂ))) := by
  -- Since $g$ has compact support, there exists $R > 0$ such that $g(t) = 0$ for all $|t| > R$.
  obtain ⟨R, hR⟩ : ∃ R > 0, ∀ t, |t| > R → g t = 0 := by
    obtain ⟨ R, hR ⟩ := hgs.exists_pos_le_norm;
    exact ⟨ R, hR.1, fun t ht => hR.2 t ht.le ⟩;
  refine' summable_of_ne_finset_zero _;
  exacts [ Finset.Icc ( ⌈-R - x⌉ ) ( ⌊R - x⌋ ), fun n hn => by rw [ hR.2 _ ( by cases abs_cases ( x + n ) <;> exact not_le.1 fun h => hn <| Finset.mem_Icc.2 ⟨ Int.ceil_le.2 <| by linarith, Int.le_floor.2 <| by linarith ⟩ ) ] ; ring ]

/-
Additivity of the dense Zak transform on compactly supported windows.
-/
theorem concreteZakDense_add (g₁ g₂ : ℝ → ℂ)
    (h₁ : HasCompactSupport g₁) (h₂ : HasCompactSupport g₂) (x s : ℝ) :
    concreteZakDense (g₁ + g₂) x s = concreteZakDense g₁ x s + concreteZakDense g₂ x s := by
  convert Summable.tsum_add ( concreteZakDense_summable g₁ h₁ x s ) ( concreteZakDense_summable g₂ h₂ x s ) using 1
  generalize_proofs at *; (
  exact tsum_congr fun k => by rw [ Pi.add_apply ] ; ring;)

/-
`ℂ`-homogeneity of the dense Zak transform.
-/
theorem concreteZakDense_smul (c : ℂ) (g : ℝ → ℂ) (x s : ℝ) :
    concreteZakDense (c • g) x s = c * concreteZakDense g x s := by
  unfold concreteZakDense;
  simp +decide [ mul_assoc, mul_left_comm, ← tsum_mul_left ]

/-
On the unit square the Zak series reduces to a fixed finite sum over
`Finset.Icc (-N) N`.
-/
theorem concreteZakDense_eq_finsum_square (g : ℝ → ℂ) (hgs : HasCompactSupport g) :
    ∃ N : ℕ, ∀ x : ℝ, x ∈ Set.Ioc (0:ℝ) 1 → ∀ s : ℝ,
      concreteZakDense g x s
        = ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
            g (x + (k:ℝ)) * Complex.exp (-2 * ↑Real.pi * Complex.I * (k:ℂ) * (s:ℂ)) := by
  obtain ⟨ R, hR_pos, hR ⟩ := hgs.exists_pos_le_norm;
  refine' ⟨ ⌈R⌉₊ + 1, fun x hx s => _ ⟩;
  refine' tsum_eq_sum _;
  intro k hk; specialize hR ( x + k ) ; simp_all +decide;
  contrapose! hk;
  constructor <;> push_cast [ ← @Int.cast_le ℝ ] <;> cases abs_cases ( x + k ) <;> linarith [ Nat.le_ceil R, show ( k : ℝ ) ≥ -⌈R⌉₊ - 1 by exact_mod_cast Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast ; cases abs_cases ( x + k ) <;> linarith [ Nat.le_ceil R, show ( |x + k| : ℝ ) < R from lt_of_not_ge fun h => hk <| hR h ] }, show ( k : ℝ ) ≤ ⌈R⌉₊ + 1 by exact_mod_cast Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast ; cases abs_cases ( x + k ) <;> linarith [ Nat.le_ceil R, show ( |x + k| : ℝ ) < R from lt_of_not_ge fun h => hk <| hR h ] } ]

/-- The finite-sum proxy for the Zak square-function: a globally continuous and
bounded function agreeing with `zakSquareFun g` on the unit square. -/
def zakFinSum (g : ℝ → ℂ) (N : ℕ) : ℝ × ℝ → ℂ :=
  fun p => ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    g (p.1 + (k:ℝ)) * Complex.exp (-2 * ↑Real.pi * Complex.I * (k:ℂ) * (p.2:ℂ))

theorem zakFinSum_continuous (g : ℝ → ℂ) (hgc : Continuous g) (N : ℕ) :
    Continuous (zakFinSum g N) := by
  -- Show that the sum of continuous functions is continuous.
  have h_sum_cont : Continuous (fun p : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N : ℤ) N, g (p.1 + k) * Complex.exp (-2 * Real.pi * Complex.I * k * p.2)) := by
    fun_prop;
  convert h_sum_cont using 1

theorem zakFinSum_bounded (g : ℝ → ℂ) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (N : ℕ) : ∃ C : ℝ, ∀ p : ℝ × ℝ, ‖zakFinSum g N p‖ ≤ C := by
  -- Since g is continuous with compact support, there exists M such that ‖g(t)‖ ≤ M for all t.
  obtain ⟨M, hM⟩ : ∃ M, ∀ t : ℝ, ‖g t‖ ≤ M := hgs.exists_bound_of_continuous hgc
  use (Finset.Icc (-(N:ℤ)) (N:ℤ)).card * M; intro p; (
  exact le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum fun _ _ => by simpa [ Complex.norm_exp ] using hM _ ) ( by norm_num ) ));

/-
`zakSquareFun g` equals the finite-sum proxy almost everywhere with respect
to the square measure.
-/
theorem zakSquareFun_ae_eq_finsum (g : ℝ → ℂ) (hgs : HasCompactSupport g) :
    ∃ N : ℕ, zakSquareFun g =ᵐ[zakSquareMeasure] zakFinSum g N := by
  obtain ⟨ N, hN ⟩ := CriticalMixedHRT.concreteZakDense_eq_finsum_square g hgs;
  refine' ⟨ N, _ ⟩;
  filter_upwards [ MeasureTheory.ae_restrict_mem ( measurableSet_Ioc.prod measurableSet_Ioc ) ] with p hp using hN p.1 hp.1 p.2

/-
**The Zak square-function is `L²` on the unit square.**
-/
theorem concreteZakDense_memLp (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    MemLp (zakSquareFun g) 2 zakSquareMeasure := by
  obtain ⟨ N, hN ⟩ := zakSquareFun_ae_eq_finsum g hgs;
  have h_finite_measure : IsFiniteMeasure zakSquareMeasure := by
    constructor ; norm_num [ zakSquareMeasure ];
    erw [ MeasureTheory.Measure.prod_prod ] ; norm_num;
  rw [ MeasureTheory.memLp_congr_ae hN ];
  obtain ⟨ C, hC ⟩ := zakFinSum_bounded g hgc hgs N;
  refine' MemLp.mono' _ _ _;
  exacts [ fun _ => C, MeasureTheory.memLp_const _, Continuous.aestronglyMeasurable ( zakFinSum_continuous g hgc N ), Filter.Eventually.of_forall hC ]

/-- **Measurability of the Zak square-function.** -/
theorem concreteZakDense_measurable (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    AEStronglyMeasurable (zakSquareFun g) zakSquareMeasure :=
  (concreteZakDense_memLp g hgc hgs).aestronglyMeasurable

/-
**Plancherel for compactly supported windows (iterated-interval form).**
The existing `concreteZakDense_plancherel` requires support in `[0,N)`; here we
remove that restriction for arbitrary compactly supported continuous windows by
an integer time-shift (which multiplies the Zak transform by a unit-modulus
phase, preserving the pointwise norm, and preserves the `L²(ℝ)` mass).
-/
theorem concreteZakDense_plancherel_cc (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    (∫ s in (0:ℝ)..1, ∫ x in (0:ℝ)..1, ‖concreteZakDense g x s‖ ^ 2)
      = ∫ t, ‖g t‖ ^ 2 := by
  -- By assumption, $g$ has compact support, so we can choose an integer $m$ such that $g(t) = 0$ for $|t| \geq m$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ t : ℝ, |t| ≥ m → g t = 0 := by
    obtain ⟨ m, hm ⟩ := hgs.exists_pos_le_norm;
    exact ⟨ ⌈m⌉₊, fun t ht => hm.2 t <| le_trans ( Nat.le_ceil _ ) <| mod_cast ht ⟩;
  have h_plancherel : ∫ s in (0:ℝ)..1, ∫ x in (0:ℝ)..1, ‖concreteZakDense (fun t => g (t - m)) x s‖ ^ 2 = ∫ t, ‖g (t - m)‖ ^ 2 := by
    convert concreteZakDense_plancherel ( 2 * m + 1 ) ( fun t => g ( t - m ) ) _ _ _ using 1;
    · intro t ht; convert hm ( t - m ) _ using 1; contrapose! ht; constructor <;> push_cast at * <;> cases abs_cases ( t - m ) <;> linarith;
    · exact hgc.measurable.comp ( measurable_id.sub measurable_const );
    · -- Since $g$ is continuous and has compact support, it is bounded.
      have h_bounded : ∃ C, ∀ t, ‖g t‖ ≤ C := by
        have := hgs.exists_bound_of_continuous hgc;
        exact this;
      exact ⟨ h_bounded.choose, fun t => h_bounded.choose_spec _ ⟩;
  have h_plancherel : ∀ x s : ℝ, concreteZakDense (fun t => g (t - m)) x s = Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (s : ℂ)) * concreteZakDense g x s := by
    intro x s; convert concreteZakDense_lattice_covariance_int g m 0 x s using 1 <;> norm_num [ shiftFun ] ; ring;
    · unfold shiftFun; norm_num;
    · exact Or.inl <| by ring;
  simp_all +decide [ Complex.norm_exp ];
  rw [ eq_comm, ← MeasureTheory.integral_sub_right_eq_self ]

/-
**Plancherel for compactly supported windows (square-integral form).**
The `L²([0,1]²)` mass of the Zak transform equals the `L²(ℝ)` mass of the
window.
-/
theorem concreteZakDense_square_integral_norm_sq (g : ℝ → ℂ)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    (∫ p, ‖zakSquareFun g p‖ ^ 2 ∂zakSquareMeasure) = ∫ t, ‖g t‖ ^ 2 := by
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · rw [ ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ ← concreteZakDense_plancherel_cc g hgc hgs ];
      erw [ MeasureTheory.setIntegral_prod ];
      · convert MeasureTheory.integral_integral_swap _ using 3;
        · norm_num [ intervalIntegral.integral_of_le zero_le_one, zakSquareFun ];
        · infer_instance;
        · infer_instance;
        · have h_integrable : MemLp (zakSquareFun g) 2 (MeasureTheory.Measure.prod (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc 0 1)) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc 0 1))) := by
            convert concreteZakDense_memLp g hgc hgs using 1;
            exact MeasureTheory.Measure.prod_restrict _ _;
          exact MeasureTheory.MemLp.integrable_sq ( h_integrable.norm );
      · have := concreteZakDense_memLp g hgc hgs;
        simpa using this.integrable_norm_rpow ( by norm_num );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · convert ( concreteZakDense_memLp g hgc hgs |> fun h => h.aestronglyMeasurable.norm.aemeasurable.pow_const 2 ) |> fun h => h.aestronglyMeasurable using 1;
  · exact Filter.Eventually.of_forall fun p => sq_nonneg _;
  · convert ( concreteZakDense_memLp g hgc hgs |> fun h => h.aestronglyMeasurable.norm.aemeasurable.pow_const 2 ) |> fun h => h.aestronglyMeasurable using 1

/-- A continuous, compactly supported representative of an element of the dense
test subspace. -/
def ccRep (f : concreteZakDenseSubspace) : ℝ → ℂ :=
  ((mem_concreteZakDenseSubspace_iff _).mp f.2).choose

theorem ccRep_continuous (f : concreteZakDenseSubspace) : Continuous (ccRep f) :=
  ((mem_concreteZakDenseSubspace_iff _).mp f.2).choose_spec.1

theorem ccRep_hasCompactSupport (f : concreteZakDenseSubspace) :
    HasCompactSupport (ccRep f) :=
  ((mem_concreteZakDenseSubspace_iff _).mp f.2).choose_spec.2.1

theorem ccRep_ae (f : concreteZakDenseSubspace) :
    ((f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] ccRep f :=
  ((mem_concreteZakDenseSubspace_iff _).mp f.2).choose_spec.2.2

/-
The chosen continuous representative is additive over the subspace addition
(everywhere, since continuous functions a.e. equal are equal).
-/
theorem ccRep_add (f₁ f₂ : concreteZakDenseSubspace) :
    ccRep (f₁ + f₂) = ccRep f₁ + ccRep f₂ := by
  refine' Continuous.ae_eq_iff_eq volume _ _ |>.1 _;
  · exact ccRep_continuous _;
  · exact Continuous.add ( ccRep_continuous f₁ ) ( ccRep_continuous f₂ );
  · filter_upwards [ ccRep_ae ( f₁ + f₂ ), ccRep_ae f₁, ccRep_ae f₂, MeasureTheory.Lp.coeFn_add ( f₁ : Lp ℂ 2 ( volume : Measure ℝ ) ) f₂ ] with t ht₁ ht₂ ht₃ ht₄ using by aesop;

/-
The chosen continuous representative is homogeneous over scalar action.
-/
theorem ccRep_smul (c : ℂ) (f : concreteZakDenseSubspace) :
    ccRep (c • f) = c • ccRep f := by
  refine' Continuous.ae_eq_iff_eq volume _ _ |>.1 _;
  · exact ccRep_continuous _;
  · exact continuous_const.mul ( ccRep_continuous f );
  · have := ccRep_ae ( c • f );
    have := ccRep_ae f;
    filter_upwards [ this, ‹ ( c • f : Lp ℂ 2 ( volume : Measure ℝ ) ) =ᶠ[ae volume] ccRep ( c • f ) ›, MeasureTheory.Lp.coeFn_smul c ( f : Lp ℂ 2 ( volume : Measure ℝ ) ) ] with x hx₁ hx₂ hx₃ using by aesop;

/-- **The Lp-valued dense Zak transform.** -/
def concreteZakDense_to_Lp (f : concreteZakDenseSubspace) : ZakTarget :=
  (concreteZakDense_memLp (ccRep f) (ccRep_continuous f) (ccRep_hasCompactSupport f)).toLp _

theorem concreteZakDense_to_Lp_apply_ae (f : concreteZakDenseSubspace) :
    (concreteZakDense_to_Lp f : ℝ × ℝ → ℂ) =ᵐ[zakSquareMeasure] zakSquareFun (ccRep f) :=
  MeasureTheory.MemLp.coeFn_toLp _

/-
**Additivity into `Lp`.**
-/
theorem concreteZakDense_to_Lp_add (f₁ f₂ : concreteZakDenseSubspace) :
    concreteZakDense_to_Lp (f₁ + f₂) = concreteZakDense_to_Lp f₁ + concreteZakDense_to_Lp f₂ := by
  convert MeasureTheory.MemLp.toLp_add _ _ using 1;
  refine' MeasureTheory.MemLp.toLp_congr _ _ _;
  rw [ ccRep_add ];
  filter_upwards [ ] with p using concreteZakDense_add ( ccRep f₁ ) ( ccRep f₂ ) ( ccRep_hasCompactSupport f₁ ) ( ccRep_hasCompactSupport f₂ ) p.1 p.2

/-
**Homogeneity into `Lp`.**
-/
theorem concreteZakDense_to_Lp_smul (c : ℂ) (f : concreteZakDenseSubspace) :
    concreteZakDense_to_Lp (c • f) = c • concreteZakDense_to_Lp f := by
  refine' MeasureTheory.MemLp.toLp_congr _ _ _;
  · convert MeasureTheory.MemLp.const_smul ( concreteZakDense_memLp ( ccRep f ) ( ccRep_continuous f ) ( ccRep_hasCompactSupport f ) ) c using 1;
  · rw [ ccRep_smul ];
    filter_upwards [ ] with p using by simp +decide [ zakSquareFun, concreteZakDense_smul ] ;

/-- **The Lp-valued dense Zak transform as a linear map.** -/
def concreteZakDense_to_Lp_linearMap : concreteZakDenseSubspace →ₗ[ℂ] ZakTarget where
  toFun := concreteZakDense_to_Lp
  map_add' := concreteZakDense_to_Lp_add
  map_smul' := by intro c f; simpa using concreteZakDense_to_Lp_smul c f

/-- Alias: linearity of the Lp-valued dense Zak transform. -/
theorem concreteZakDense_to_Lp_linear :
    ∀ (c : ℂ) (f₁ f₂ : concreteZakDenseSubspace),
      concreteZakDense_to_Lp (c • f₁ + f₂)
        = c • concreteZakDense_to_Lp f₁ + concreteZakDense_to_Lp f₂ := by
  intro c f₁ f₂
  rw [concreteZakDense_to_Lp_add, concreteZakDense_to_Lp_smul]

/-
Generic: the squared `L²` norm of `MemLp.toLp F` is the integral of `‖F‖²`.
-/
theorem memLp_two_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : α → ℂ) (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ a, ‖F a‖ ^ 2 ∂μ := by
  convert congr_arg ( · ^ 2 ) ( MeasureTheory.Lp.norm_toLp F hF ) using 1
  generalize_proofs at *; (
  convert ( MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _ ) using 1;
  · rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal ] <;> norm_num;
    rw [ ← ENNReal.toReal_rpow ];
    rw [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ( ENNReal.toReal_nonneg ) ];
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · simpa only [ sq ] using hF.1.norm.mul hF.1.norm)

/-
Generic: the squared `L²` norm of an `Lp` class is the integral of `‖·‖²` of a
representative.
-/
theorem Lp_two_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ a, ‖(f : α → ℂ) a‖ ^ 2 ∂μ := by
  convert memLp_two_norm_toLp_sq ( f : α → ℂ ) ( Lp.memLp f ) using 1;
  simp +decide [ MeasureTheory.Lp.norm_def ]

/-
**Norm-square identity (isometry core).**
-/
theorem concreteZakDense_to_Lp_norm_sq (f : concreteZakDenseSubspace) :
    ‖concreteZakDense_to_Lp f‖ ^ 2 = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := by
  convert memLp_two_norm_toLp_sq ( zakSquareFun ( ccRep f ) ) ( concreteZakDense_memLp ( ccRep f ) ( ccRep_continuous f ) ( ccRep_hasCompactSupport f ) ) using 2;
  convert Lp_two_norm_sq ( f : Lp ℂ 2 ( volume : Measure ℝ ) ) using 1;
  convert concreteZakDense_square_integral_norm_sq ( ccRep f ) ( ccRep_continuous f ) ( ccRep_hasCompactSupport f ) using 1;
  exact MeasureTheory.integral_congr_ae ( by filter_upwards [ ccRep_ae f ] with x hx; aesop )

/-- **Isometry of the Lp-valued dense Zak transform.** -/
theorem concreteZakDense_to_Lp_norm (f : concreteZakDenseSubspace) :
    ‖concreteZakDense_to_Lp f‖ = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ := by
  have h := concreteZakDense_to_Lp_norm_sq f
  have h1 : (0:ℝ) ≤ ‖concreteZakDense_to_Lp f‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ := norm_nonneg _
  nlinarith [h, h1, h2, sq_nonneg (‖concreteZakDense_to_Lp f‖ - ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖)]

/-- **The Lp-valued dense Zak transform as a linear isometry.** -/
def concreteZakDense_to_Lp_linearIsometry : concreteZakDenseSubspace →ₗᵢ[ℂ] ZakTarget where
  toLinearMap := concreteZakDense_to_Lp_linearMap
  norm_map' := by
    intro f
    -- norm of the subspace element equals the ambient Lp norm
    simpa [concreteZakDense_to_Lp_linearMap] using concreteZakDense_to_Lp_norm f

/-- Alias matching the task name: the isometry property. -/
theorem concreteZakDense_to_Lp_isometry :
    ∀ f : concreteZakDenseSubspace,
      ‖concreteZakDense_to_Lp_linearMap f‖ = ‖(f : Lp ℂ 2 (volume : Measure ℝ))‖ := by
  intro f
  simpa [concreteZakDense_to_Lp_linearMap] using concreteZakDense_to_Lp_norm f

end

end CriticalMixedHRT