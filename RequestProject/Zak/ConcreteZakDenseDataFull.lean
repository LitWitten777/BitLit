import Mathlib
import RequestProject.Zak.ConcreteZakToLp

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — discharging `StandardConcreteZakToLpTheorem` (TASKs E/F)

Building on the genuine Lp-valued Zak linear isometry
`concreteZakDense_to_Lp_linearIsometry` (proved in `ConcreteZakToLp.lean`), this
module assembles a full `ConcreteZakDenseData` term and proves

* `standardConcreteZakToLpTheorem_proved : StandardConcreteZakToLpTheorem`.

The time-frequency shift operators on `L²(ℝ)` are the genuine isometries induced
by `shiftFun a b` (modulation × translation), realized here as continuous linear
maps `tfShiftCLM a b`.  The target-side modulation operators `charLattice` /
`charRogue` are realized by transporting the domain shift through the (extended)
Zak isometry: `charOp S := Φ ∘ S ∘ Ψ`, where `Φ` is the full isometric extension
of the dense Zak transform and `Ψ` is its continuous left inverse (the inverse on
the closed range composed with the orthogonal projection onto that range).  With
this construction the lattice/rogue covariance identities hold by the extension
property of `Φ`, with no `sorry` and no axiom.
-/

namespace CriticalMixedHRT

noncomputable section

/-! ## The time-frequency shift as a linear isometry of `L²(ℝ)` -/

/-
The pointwise time-frequency shift preserves the `L²` norm.
-/
theorem shiftFun_eLpNorm (a b : ℝ) (g : ℝ → ℂ) :
    eLpNorm (shiftFun a b g) 2 (volume : Measure ℝ) = eLpNorm g 2 (volume : Measure ℝ) := by
  unfold shiftFun; norm_num;
  norm_num [ Complex.norm_exp, eLpNorm ];
  rw [ eLpNorm', eLpNorm' ];
  rw [ ← MeasureTheory.lintegral_add_right_eq_self _ a ];
  simp +decide [ ENorm.enorm ];
  simp +decide [ ← ENNReal.ofReal_coe_nnreal, Complex.norm_exp ]

/-
The pointwise time-frequency shift preserves membership in `L²`.
-/
theorem shiftFun_memLp (a b : ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    MemLp (shiftFun a b f) 2 (volume : Measure ℝ) := by
  refine' ⟨ _, _ ⟩;
  · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
    · exact Continuous.aestronglyMeasurable ( by continuity );
    · have := hf.1;
      convert this.comp_quasiMeasurePreserving ( MeasureTheory.measurePreserving_sub_right volume a |> MeasureTheory.MeasurePreserving.quasiMeasurePreserving ) using 1;
  · rw [ shiftFun_eLpNorm ] ; exact hf.eLpNorm_lt_top

/-
a.e. equal windows have a.e. equal time-frequency shifts.
-/
theorem shiftFun_congr_ae (a b : ℝ) {g₁ g₂ : ℝ → ℂ} (h : g₁ =ᵐ[volume] g₂) :
    shiftFun a b g₁ =ᵐ[volume] shiftFun a b g₂ := by
  -- Since $g₁ = g₂$ almost everywhere, and the exponential function is continuous, multiplying by it preserves the almost everywhere equality.
  have h_exp : ∀ᵐ t ∂volume, g₁ (t - a) = g₂ (t - a) := by
    rw [ Filter.EventuallyEq, MeasureTheory.ae_iff ] at *;
    rw [ show { a_1 : ℝ | ¬g₁ ( a_1 - a ) = g₂ ( a_1 - a ) } = ( fun x => x - a ) ⁻¹' { a : ℝ | ¬g₁ a = g₂ a } by ext; simp +decide ];
    erw [ MeasureTheory.measure_preimage_add_right ] ; aesop;
  filter_upwards [ h_exp ] with t ht using by unfold shiftFun; aesop;

/-- The time-frequency shift on `L²(ℝ)` at the level of `Lp` classes. -/
def tfShiftToLp (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (shiftFun_memLp a b (f : ℝ → ℂ) (Lp.memLp f)).toLp _

theorem tfShiftToLp_coeFn (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (tfShiftToLp a b f : ℝ → ℂ) =ᵐ[volume] shiftFun a b (f : ℝ → ℂ) :=
  MeasureTheory.MemLp.coeFn_toLp _

theorem tfShiftToLp_add (a b : ℝ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    tfShiftToLp a b (f + g) = tfShiftToLp a b f + tfShiftToLp a b g := by
  refine' MeasureTheory.MemLp.toLp_congr _ _ _;
  · exact MeasureTheory.MemLp.add ( shiftFun_memLp a b _ ( Lp.memLp f ) ) ( shiftFun_memLp a b _ ( Lp.memLp g ) );
  · convert shiftFun_congr_ae a b _ using 1;
    rotate_left;
    exact fun x => f x + g x;
    · exact MeasureTheory.Lp.coeFn_add _ _;
    · ext; simp [shiftFun];
      ring

theorem tfShiftToLp_smul (a b : ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    tfShiftToLp a b (c • f) = c • tfShiftToLp a b f := by
  refine' MeasureTheory.MemLp.toLp_congr _ _ _;
  · convert shiftFun_memLp a b ( c • f ) _ using 1;
    · ext; simp +decide [ shiftFun ] ; ring;
    · exact MeasureTheory.MemLp.const_smul ( Lp.memLp f ) c;
  · convert shiftFun_congr_ae a b _ using 1;
    rotate_left;
    exact fun x => c * f x;
    · exact MeasureTheory.Lp.coeFn_smul _ _;
    · ext; simp +decide [ shiftFun ] ; ring

theorem tfShiftToLp_norm (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖tfShiftToLp a b f‖ = ‖f‖ := by
  rw [ MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def ];
  rw [ MeasureTheory.eLpNorm_congr_ae ( tfShiftToLp_coeFn a b f ) ];
  rw [ shiftFun_eLpNorm ]

/-- The time-frequency shift as a linear isometry of `L²(ℝ)`. -/
def tfShiftLI (a b : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := tfShiftToLp a b
  map_add' := tfShiftToLp_add a b
  map_smul' := by intro c f; simpa using tfShiftToLp_smul a b c f
  norm_map' := tfShiftToLp_norm a b

/-- The time-frequency shift as a continuous linear map of `L²(ℝ)`. -/
def tfShiftCLM (a b : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (tfShiftLI a b).toContinuousLinearMap

theorem tfShiftCLM_coeFn (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (tfShiftCLM a b f : ℝ → ℂ) =ᵐ[volume] shiftFun a b (f : ℝ → ℂ) :=
  tfShiftToLp_coeFn a b f

/-
The dense test subspace is preserved by the time-frequency shift.
-/
theorem tfShiftCLM_mem (a b : ℝ) (d : concreteZakDenseSubspace) :
    tfShiftCLM a b (d : Lp ℂ 2 (volume : Measure ℝ)) ∈ concreteZakDenseSubspace := by
  -- Define g as the shiftFun a b of ccRep d.
  set g : ℝ → ℂ := shiftFun a b (ccRep d);
  refine' mem_concreteZakDenseSubspace_iff _ |>.2 ⟨ g, _, _, _ ⟩;
  · exact ( concreteZakDenseSubspace_closed_under_shift a b ( ccRep d ) ( ccRep_continuous d ) ( ccRep_hasCompactSupport d ) ) |>.1;
  · exact ( concreteZakDenseSubspace_closed_under_shift a b ( ccRep d ) ( ccRep_continuous d ) ( ccRep_hasCompactSupport d ) ) |>.2;
  · filter_upwards [ tfShiftCLM_coeFn a b ( d : Lp ℂ 2 ( volume : Measure ℝ ) ), shiftFun_congr_ae a b ( ccRep_ae d ) ] with x hx₁ hx₂ using by aesop;

/-! ## The transport construction of the covariance operators -/

/-- The full isometric extension of the dense Zak transform to all of `L²(ℝ)`. -/
def zakExt : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] ZakTarget :=
  (linear_isometry_extends_from_dense_subspace concreteZakDenseSubspace
    concreteZakDenseSubspace_dense concreteZakDense_to_Lp_linearIsometry).choose

theorem zakExt_apply (d : concreteZakDenseSubspace) :
    zakExt (d : Lp ℂ 2 (volume : Measure ℝ)) = concreteZakDense_to_Lp_linearIsometry d :=
  (linear_isometry_extends_from_dense_subspace concreteZakDenseSubspace
    concreteZakDenseSubspace_dense concreteZakDense_to_Lp_linearIsometry).choose_spec d

theorem zakExt_range_complete : CompleteSpace ↥(zakExt.range) := by
  refine' completeSpace_coe_iff_isComplete.mpr _;
  exact zakExt.isometry.isUniformInducing.isComplete_range

noncomputable instance zakExt_range_hasOrthogonalProjection :
    zakExt.range.HasOrthogonalProjection :=
  haveI := zakExt_range_complete
  Submodule.HasOrthogonalProjection.ofCompleteSpace zakExt.range

/-- The continuous left inverse of the extended Zak isometry. -/
def zakLeftInv : ZakTarget →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  zakExt.equivRange.symm.toLinearIsometry.toContinuousLinearMap ∘L zakExt.range.orthogonalProjection

theorem zakLeftInv_zakExt (v : Lp ℂ 2 (volume : Measure ℝ)) :
    zakLeftInv (zakExt v) = v := by
  convert zakExt.equivRange.symm_apply_apply v using 1;
  convert congr_arg zakExt.equivRange.symm _;
  convert zakExt.range.orthogonalProjection_mem_subspace_eq_self ( zakExt.equivRange v ) using 1

/-- Transport a domain operator through the Zak isometry to a target operator. -/
def charOp (S : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    ZakTarget →L[ℂ] ZakTarget :=
  zakExt.toContinuousLinearMap ∘L S ∘L zakLeftInv

theorem charOp_zakExt (S : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    charOp S (zakExt v) = zakExt (S v) := by
  simp only [charOp, ContinuousLinearMap.comp_apply, zakLeftInv_zakExt,
    LinearIsometry.coe_toContinuousLinearMap]

/-! ## The concrete dense Zak data and the discharge -/

/-
The full concrete dense Zak isometry data.
-/
def concreteZakDenseDataFull : ConcreteZakDenseData where
  T₀ := concreteZakDense_to_Lp_linearIsometry
  shift := tfShiftCLM
  charLattice := fun m n => charOp (tfShiftCLM (m : ℝ) (n : ℝ))
  charRogue := fun a b => charOp (tfShiftCLM a b)
  hshiftD := tfShiftCLM_mem
  hlat := by
    intro m n d
    rw [ ← zakExt_apply, ← zakExt_apply ];
    rw [ charOp_zakExt ]
  hrog := by
    intro a b d
    convert zakExt_apply ⟨tfShiftCLM a b d, tfShiftCLM_mem a b d⟩ |> Eq.symm using 1;
    convert charOp_zakExt ( tfShiftCLM a b ) ( d : Lp ℂ 2 ( volume : Measure ℝ ) ) using 1;
    exact congr_arg _ ( zakExt_apply d ▸ rfl )

/-- **TASK F — `StandardConcreteZakToLpTheorem` is discharged.** -/
theorem standardConcreteZakToLpTheorem_proved : StandardConcreteZakToLpTheorem :=
  ⟨concreteZakDenseDataFull⟩

/-- **The concrete a.e. Zak model exists, unconditionally.** -/
theorem concrete_L2ZakModelAE_closed :
    Nonempty (L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget) :=
  concrete_L2ZakModelAE_nonempty standardConcreteZakToLpTheorem_proved

end

end CriticalMixedHRT