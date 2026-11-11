import Mathlib
import RequestProject.Zak.ConcreteZakDenseDataFull

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the **canonical** a.e.-level `L²` Zak model with explicit operators

This module replaces the opaque `Classical.choice` Zak model by a *canonical*
a.e.-level Zak model whose target covariance operators are **explicitly defined**
by the expected fibre formulas:

* `explicitCharLattice m n` — multiplication by the lattice character
  `exp(-2π i (n x + m s))` on `ZakTarget = L²([0,1]²)`;
* `explicitCharRogue a b` — the rogue covariance operator, acting on a target
  class `G` by
  `(x,s) ↦ exp(-2π i b x) · (canonicalQuasiRep G)(x - a, s + b)`,
  where `canonicalQuasiRep` is the canonical quasiperiodic extension (identical
  formula to `zakQuasiPeriodicRep`).

Both are realized as genuine bounded operators on `Lp` classes (via
`UnimodWeightedComp`), and the canonical model `canonicalAEZakModel` uses the
genuine extended Zak isometry `zakExt`, the time-frequency shift `tfShiftCLM`,
and these explicit operators, with the lattice / rogue covariance laws proved
from the dense covariance identities `concreteZakDense_lattice_covariance_int` /
`concreteZakDense_rogue_covariance_real`.
-/

namespace CriticalMixedHRT

noncomputable section

/-! ## The canonical quasiperiodic extension -/

/-- The canonical quasiperiodic extension of a target `L²([0,1]²)` class
(identical formula to `zakQuasiPeriodicRep`):
`canonicalQuasiRep G x s = exp(2π i ⌊x⌋ · fract s) · (G : ℝ×ℝ→ℂ)(fract x, fract s)`. -/
def canonicalQuasiRep (G : ZakTarget) : ℝ → ℝ → ℂ :=
  fun x s =>
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(⌊x⌋ : ℤ) : ℂ) * (↑(Int.fract s) : ℂ))
      * (G : ℝ × ℝ → ℂ) (Int.fract x, Int.fract s)

/-! ## Unimodular weighted-composition operators on `ZakTarget` -/

/-- A unimodular weighted composition datum: multiplication by a unimodular
weight `χ` composed with precomposition by a measure-preserving map `T` of the
fundamental square.  Such a datum induces a linear isometry of `ZakTarget`. -/
structure UnimodWeightedComp where
  /-- The unimodular weight. -/
  χ : ℝ × ℝ → ℂ
  /-- The measure-preserving precomposition map of the fundamental square. -/
  T : ℝ × ℝ → ℝ × ℝ
  /-- The weight is (a.e.) strongly measurable. -/
  hχ_meas : AEStronglyMeasurable χ zakSquareMeasure
  /-- The weight is unimodular a.e. -/
  hχ_unit : ∀ᵐ p ∂zakSquareMeasure, ‖χ p‖ = 1
  /-- `T` is measure-preserving on the fundamental square. -/
  hT : MeasureTheory.MeasurePreserving T zakSquareMeasure zakSquareMeasure

namespace UnimodWeightedComp

variable (D : UnimodWeightedComp)

/-- The pointwise action of the datum on a representative. -/
def fn (G : ZakTarget) : ℝ × ℝ → ℂ := fun p => D.χ p * (G : ℝ × ℝ → ℂ) (D.T p)

/-
The pointwise action is `L²` on the fundamental square.
-/
theorem memLp (G : ZakTarget) : MemLp (D.fn G) 2 zakSquareMeasure := by
  refine' MemLp.mono' _ _ _;
  exact fun p => ‖( G : ℝ × ℝ → ℂ ) ( D.T p )‖;
  · have h_integrable : MemLp (fun p => (G : ℝ × ℝ → ℂ) (D.T p)) 2 zakSquareMeasure := by
      exact MemLp.comp_measurePreserving ( Lp.memLp _ ) D.hT;
    exact h_integrable.norm;
  · exact D.hχ_meas.mul ( G.1.aestronglyMeasurable.comp_quasiMeasurePreserving D.hT.quasiMeasurePreserving );
  · filter_upwards [ D.hχ_unit ] with p hp using by simp +decide [ UnimodWeightedComp.fn, hp ] ;

/-
The action preserves the `L²` norm of the representative.
-/
theorem eLpNorm_eq (G : ZakTarget) :
    eLpNorm (D.fn G) 2 zakSquareMeasure = eLpNorm (G : ℝ × ℝ → ℂ) 2 zakSquareMeasure := by
  rw [ eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_eq_lintegral_rpow_enorm_toReal ];
  · have h_norm_eq : ∀ᵐ p ∂zakSquareMeasure, ‖D.fn G p‖ₑ = ‖(G : ℝ × ℝ → ℂ) (D.T p)‖ₑ := by
      filter_upwards [ D.hχ_unit ] with p hp;
      unfold UnimodWeightedComp.fn;
      rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num [ hp ];
      exact not_eq_of_beq_eq_false rfl;
    rw [ MeasureTheory.lintegral_congr_ae ( h_norm_eq.mono fun x hx => by rw [ hx ] ) ];
    have := D.hT.lintegral_comp ( show Measurable fun p : ℝ × ℝ => ‖ ( G : ℝ × ℝ → ℂ ) p‖ₑ ^ 2 from by measurability ) ; aesop;
  · norm_num;
  · norm_num;
  · norm_num;
  · norm_num

/-- The `Lp`-class action. -/
def toFun (G : ZakTarget) : ZakTarget := (D.memLp G).toLp _

theorem toFun_coeFn (G : ZakTarget) :
    (D.toFun G : ℝ × ℝ → ℂ) =ᵐ[zakSquareMeasure] D.fn G :=
  MeasureTheory.MemLp.coeFn_toLp _

theorem toFun_add (G H : ZakTarget) : D.toFun (G + H) = D.toFun G + D.toFun H := by
  convert MeasureTheory.MemLp.toLp_add _ _;
  convert ( MemLp.toLp_congr _ _ _ ) using 1;
  have h_add : ∀ᵐ p ∂zakSquareMeasure, (G + H : ZakTarget) (D.T p) = (G : ZakTarget) (D.T p) + (H : ZakTarget) (D.T p) := by
    have h_add : ∀ᵐ p ∂zakSquareMeasure, (G + H : ZakTarget) p = (G : ZakTarget) p + (H : ZakTarget) p := by
      exact MeasureTheory.Lp.coeFn_add G H;
    convert D.hT.quasiMeasurePreserving.ae ( h_add ) using 1;
  filter_upwards [ h_add ] with p hp using by unfold UnimodWeightedComp.fn; aesop;

theorem toFun_smul (c : ℂ) (G : ZakTarget) : D.toFun (c • G) = c • D.toFun G := by
  -- To prove the equality of two L2 functions, it suffices to show they are equal almost everywhere.
  suffices h_ae : D.fn (c • G) =ᵐ[zakSquareMeasure] fun p => c • D.fn G p by
    refine' Subtype.ext ( _ );
    refine' MeasureTheory.AEEqFun.mk_eq_mk.mpr _;
    convert h_ae using 1;
  have h_ae : ∀ᵐ p ∂zakSquareMeasure, (c • G) (D.T p) = c • G (D.T p) := by
    have h_ae : (c • G : ZakTarget) =ᵐ[zakSquareMeasure] fun p => c • G p := by
      exact MeasureTheory.Lp.coeFn_smul c G;
    convert D.hT.quasiMeasurePreserving.ae_eq_comp h_ae using 1;
  filter_upwards [ h_ae ] with p hp using by unfold UnimodWeightedComp.fn; simp +decide [ hp, mul_assoc, mul_left_comm ] ;

theorem toFun_norm (G : ZakTarget) : ‖D.toFun G‖ = ‖G‖ := by
  rw [ MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def ];
  convert congr_arg ENNReal.toReal ( D.eLpNorm_eq G ) using 1;
  rw [ eLpNorm_congr_ae ( D.toFun_coeFn G ) ]

/-- The induced linear isometry of `ZakTarget`. -/
def toLI : ZakTarget →ₗᵢ[ℂ] ZakTarget where
  toFun := D.toFun
  map_add' := D.toFun_add
  map_smul' := by intro c G; simpa using D.toFun_smul c G
  norm_map' := D.toFun_norm

/-- The induced continuous linear operator of `ZakTarget`. -/
def toCLM : ZakTarget →L[ℂ] ZakTarget := D.toLI.toContinuousLinearMap

theorem toCLM_coeFn (G : ZakTarget) :
    (D.toCLM G : ℝ × ℝ → ℂ) =ᵐ[zakSquareMeasure] D.fn G :=
  D.toFun_coeFn G

end UnimodWeightedComp

/-! ## The explicit lattice operator -/

/-- The lattice character `exp(-2π i (n x + m s))`. -/
def latChar (m n : ℤ) : ℝ × ℝ → ℂ :=
  fun p => Complex.exp (-2 * ↑Real.pi * Complex.I * ((n : ℂ) * (p.1 : ℂ) + (m : ℂ) * (p.2 : ℂ)))

theorem latChar_continuous (m n : ℤ) : Continuous (latChar m n) := by
  unfold latChar; fun_prop

theorem latChar_norm (m n : ℤ) (p : ℝ × ℝ) : ‖latChar m n p‖ = 1 := by
  unfold latChar; norm_num [ Complex.norm_exp ] ;

/-- The lattice weighted-composition datum (pure multiplication, `T = id`). -/
def latData (m n : ℤ) : UnimodWeightedComp where
  χ := latChar m n
  T := id
  hχ_meas := (latChar_continuous m n).aestronglyMeasurable
  hχ_unit := Filter.Eventually.of_forall (latChar_norm m n)
  hT := MeasureTheory.MeasurePreserving.id _

/-- **The explicit lattice covariance operator** on `ZakTarget`: multiplication
by the lattice character `exp(-2π i (n x + m s))`. -/
def explicitCharLattice (m n : ℤ) : ZakTarget →L[ℂ] ZakTarget := (latData m n).toCLM

theorem explicitCharLattice_coeFn (m n : ℤ) (G : ZakTarget) :
    (explicitCharLattice m n G : ℝ × ℝ → ℂ)
      =ᵐ[zakSquareMeasure] fun p => latChar m n p * (G : ℝ × ℝ → ℂ) p :=
  (latData m n).toCLM_coeFn G

/-! ## The explicit rogue operator -/

/-- The rogue weight `exp(-2π i b x) · exp(2π i ⌊x - a⌋ · fract(s + b))`. -/
def rogueChar (a b : ℝ) : ℝ × ℝ → ℂ :=
  fun p =>
    Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
      * Complex.exp (2 * ↑Real.pi * Complex.I * (↑(⌊p.1 - a⌋ : ℤ) : ℂ)
          * (↑(Int.fract (p.2 + b)) : ℂ))

/-- The rogue precomposition map `(x,s) ↦ (fract(x - a), fract(s + b))`. -/
def rogueShift (a b : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (Int.fract (p.1 - a), Int.fract (p.2 + b))

theorem rogueChar_measurable (a b : ℝ) : AEStronglyMeasurable (rogueChar a b) zakSquareMeasure := by
  refine' Measurable.aestronglyMeasurable _;
  refine' Measurable.mul _ _;
  · fun_prop;
  · fun_prop (disch := norm_num)

theorem rogueChar_norm (a b : ℝ) (p : ℝ × ℝ) : ‖rogueChar a b p‖ = 1 := by
  unfold rogueChar; norm_num [ Complex.norm_exp ] ;

/-
**The rogue precomposition map is measure-preserving on the fundamental
square.**  This is the torus-translation measure-preservation underlying the
rogue covariance operator.
-/
theorem rogueShift_measurePreserving (a b : ℝ) :
    MeasureTheory.MeasurePreserving (rogueShift a b) zakSquareMeasure zakSquareMeasure := by
  have h_meas_pres : MeasurePreserving (fun x => Int.fract (x - a)) (volume.restrict (Set.Ioc 0 1)) (volume.restrict (Set.Ioc 0 1)) ∧ MeasurePreserving (fun s => Int.fract (s + b)) (volume.restrict (Set.Ioc 0 1)) (volume.restrict (Set.Ioc 0 1)) := by
    have h_measurable : ∀ c : ℝ, MeasurePreserving (fun x => Int.fract (x + c)) (volume.restrict (Set.Ioc 0 1)) (volume.restrict (Set.Ioc 0 1)) := by
      intro c;
      have h_periodic : MeasurePreserving (fun x => Int.fract (x + c)) (volume.restrict (Set.Ico 0 1)) (volume.restrict (Set.Ico 0 1)) := by
        refine' ⟨ _, _ ⟩;
        · exact Measurable.fract ( measurable_id.add_const c );
        · ext s hs;
          rw [ Measure.map_apply ];
          · simp +decide [ Set.preimage, Int.fract_eq_iff ];
            -- By definition of fractional part, we can rewrite the set {x | Int.fract (x + c) ∈ s} ∩ Set.Ico 0 1 as a union of intervals.
            have h_union_intervals : {x : ℝ | Int.fract (x + c) ∈ s} ∩ Set.Ico 0 1 = ⋃ k : ℤ, (Set.Ico (max 0 (k - c)) (min 1 (k + 1 - c)) ∩ {x : ℝ | x + c - k ∈ s}) := by
              ext x;
              simp +zetaDelta at *;
              constructor;
              · intro hx;
                use Int.floor (x + c);
                exact ⟨ ⟨ ⟨ hx.2.1, Int.floor_le _ ⟩, hx.2.2, by linarith [ Int.lt_floor_add_one ( x + c ) ] ⟩, by simpa [ Int.fract_eq_iff ] using hx.1 ⟩;
              · rintro ⟨ k, ⟨ ⟨ hx₀, hk ⟩, hx₁, hx₂ ⟩, hk' ⟩;
                exact ⟨ by convert hk' using 1; rw [ Int.fract ] ; norm_num [ show ⌊x + c⌋ = k from Int.floor_eq_iff.mpr ⟨ by linarith, by linarith ⟩ ], hx₀, hx₁ ⟩;
            rw [ h_union_intervals, MeasureTheory.measure_iUnion ];
            · -- By definition of fractional part, we can rewrite the set {x | Int.fract (x + c) ∈ s} ∩ Set.Ico 0 1 as a union of intervals, each of which has measure equal to the measure of s.
              have h_union_intervals_measure : ∀ k : ℤ, volume (Set.Ico (max 0 (k - c)) (min 1 (k + 1 - c)) ∩ {x : ℝ | x + c - k ∈ s}) = volume (Set.Ico (max 0 (k - c)) (min 1 (k + 1 - c)) ∩ (fun x => x + c - k) ⁻¹' s) := by
                exact fun k => rfl;
              have h_union_intervals_measure : ∀ k : ℤ, volume (Set.Ico (max 0 (k - c)) (min 1 (k + 1 - c)) ∩ (fun x => x + c - k) ⁻¹' s) = volume (Set.Ico (max (c - k) 0) (min (c - k + 1) 1) ∩ s) := by
                intro k; rw [ show ( Set.Ico ( max 0 ( k - c ) ) ( min 1 ( k + 1 - c ) ) ∩ ( fun x => x + c - k ) ⁻¹' s ) = ( fun x => x + c - k ) ⁻¹' ( Set.Ico ( max ( c - k ) 0 ) ( min ( c - k + 1 ) 1 ) ∩ s ) from ?_ ] ;
                · rw [ show ( fun x => x + c - k ) = fun x => x + ( c - k ) by ext; ring ];
                  rw [ MeasureTheory.measure_preimage_add_right ];
                · grind;
              have h_union_intervals_measure : volume (s ∩ Set.Ico 0 1) = ∑' k : ℤ, volume (Set.Ico (max (c - k) 0) (min (c - k + 1) 1) ∩ s) := by
                rw [ ← MeasureTheory.measure_iUnion ];
                · congr with x ; simp +decide [ Set.mem_iUnion, Set.mem_inter_iff ];
                  constructor <;> intro h;
                  · exact ⟨ ⟨ ⌈c - x⌉, ⟨ by linarith [ Int.le_ceil ( c - x ) ], by linarith ⟩, by linarith [ Int.ceil_lt_add_one ( c - x ) ], by linarith ⟩, h.1 ⟩;
                  · exact ⟨ h.2, h.1.choose_spec.1.2, h.1.choose_spec.2.2 ⟩;
                · intro k l hkl; simp [Set.disjoint_iff_forall_ne];
                  intro a ha₁ ha₂ ha₃ ha₄ ha₅ b hb₁ hb₂ hb₃ hb₄ hb₅; contrapose! hkl; exact Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ;
                · exact fun k => MeasurableSet.inter ( measurableSet_Ico ) hs;
              aesop;
            · intro k l hkl; simp [Set.disjoint_iff_forall_ne];
              intro a ha₁ ha₂ ha₃ ha₄ ha₅ b hb₁ hb₂ hb₃ hb₄ hb₅; contrapose! hkl; exact Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith } ) ;
            · exact fun k => MeasurableSet.inter ( measurableSet_Ico ) ( hs.preimage ( measurable_id.add_const _ |> Measurable.sub <| measurable_const ) );
          · exact Measurable.fract ( measurable_id.add_const c );
          · exact hs;
      simp_all +decide [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc ];
    exact ⟨ by simpa using h_measurable ( -a ), h_measurable b ⟩;
  convert h_meas_pres.1.prod h_meas_pres.2 using 1; all_goals rw [ MeasureTheory.Measure.prod_restrict ] ; aesop

/-- The rogue weighted-composition datum. -/
def rogData (a b : ℝ) : UnimodWeightedComp where
  χ := rogueChar a b
  T := rogueShift a b
  hχ_meas := rogueChar_measurable a b
  hχ_unit := Filter.Eventually.of_forall (rogueChar_norm a b)
  hT := rogueShift_measurePreserving a b

/-- **The explicit rogue covariance operator** on `ZakTarget`. -/
def explicitCharRogue (a b : ℝ) : ZakTarget →L[ℂ] ZakTarget := (rogData a b).toCLM

/-- The rogue datum's pointwise action coincides with the expected rogue fibre
formula `exp(-2π i b x) · canonicalQuasiRep G (x - a, s + b)`. -/
theorem rogData_fn_eq (a b : ℝ) (G : ZakTarget) (p : ℝ × ℝ) :
    (rogData a b).fn G p
      = Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * canonicalQuasiRep G (p.1 - a) (p.2 + b) := by
  unfold UnimodWeightedComp.fn rogData rogueChar rogueShift canonicalQuasiRep
  ring

theorem explicitCharRogue_coeFn (a b : ℝ) (G : ZakTarget) :
    (explicitCharRogue a b G : ℝ × ℝ → ℂ)
      =ᵐ[zakSquareMeasure] fun p =>
        Complex.exp (-2 * ↑Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ))
          * canonicalQuasiRep G (p.1 - a) (p.2 + b) := by
  refine ((rogData a b).toCLM_coeFn G).trans ?_
  exact Filter.Eventually.of_forall (rogData_fn_eq a b G)

/-! ## Helper lemmas for the covariance laws -/

/-
The chosen continuous representative of a time-frequency-shifted dense class
is the genuine pointwise shift of the chosen representative.
-/
theorem ccRep_tfShift (a b : ℝ) (d : concreteZakDenseSubspace) :
    ccRep ⟨tfShiftCLM a b (d : Lp ℂ 2 (volume : Measure ℝ)), tfShiftCLM_mem a b d⟩
      = shiftFun a b (ccRep d) := by
  have h_eq : ccRep ⟨(tfShiftCLM a b) ↑d, tfShiftCLM_mem a b d⟩ =ᵐ[volume] shiftFun a b (ccRep d) := by
    refine' Filter.EventuallyEq.trans _ ( shiftFun_congr_ae a b ( ccRep_ae d ) );
    have := ccRep_ae ⟨ ( tfShiftCLM a b ) ↑d, tfShiftCLM_mem a b d ⟩;
    exact this.symm.trans ( tfShiftCLM_coeFn a b d );
  refine' Continuous.ae_eq_iff_eq volume _ _ |>.1 h_eq;
  · exact ccRep_continuous _;
  · exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) ( ccRep_continuous d |> Continuous.comp <| by continuity )

/-
**Quasiperiodic reduction to the fundamental square for the classical Zak
transform.**  Reducing both arguments to their fractional parts pulls out the
`x`-quasiperiodic phase.
-/
theorem concreteZakDense_fract (g : ℝ → ℂ) (u v : ℝ) :
    concreteZakDense g (Int.fract u) (Int.fract v)
      = Complex.exp (-2 * ↑Real.pi * Complex.I * (↑(⌊u⌋ : ℤ) : ℂ) * (↑(Int.fract v) : ℂ))
        * concreteZakDense g u v := by
  -- Apply the periodicity in the second argument.
  have h_periodic_s : ∀ t s : ℝ, ∀ k : ℤ, concreteZakDense g t (s + k) = concreteZakDense g t s := by
    intros t s k; induction' k using Int.induction_on with k ih k ih; all_goals simp_all +decide [ ← add_assoc ] ;
    · rw [ ← ih, CriticalMixedHRT.concreteZakDense_periodic_s ];
    · have := concreteZakDense_periodic_s g t ( s + -↑k - 1 ) ; ring_nf at *; aesop;
  -- Apply the quasiperiodicity in the first argument.
  have h_quasiperiodic_x : ∀ t s : ℝ, ∀ k : ℤ, concreteZakDense g (t + k) s = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)) * concreteZakDense g t s := by
    intros t s k; induction' k using Int.induction_on with k ih k ih ; aesop;
    · have := concreteZakDense_quasiperiodic_x g ( t + k ) s; simp_all +decide [ add_mul, Complex.exp_add ] ; ring;
      convert this using 1 <;> push_cast [ ← mul_assoc, ← Complex.exp_add ] <;> ring;
    · have := concreteZakDense_quasiperiodic_x g ( t + -↑k - 1 ) s; simp_all +decide [ add_mul, mul_add, ← mul_assoc, ← Complex.exp_add ] ; ring;
      simp_all +decide [ Complex.exp_sub, mul_assoc, mul_comm, mul_left_comm ];
      rw [ mul_div, eq_div_iff ( Complex.exp_ne_zero _ ) ] ; ring_nf at * ; aesop;
  have := h_periodic_s u ( Int.fract v ) ⌊v⌋; have := h_quasiperiodic_x ( Int.fract u ) ( Int.fract v ) ⌊u⌋; simp_all +decide [ Complex.exp_neg, mul_assoc, mul_left_comm ] ;

/-! ## The canonical a.e. Zak model -/

/-
**The lattice covariance law for the canonical model.**
-/
theorem canonicalAEZak_lattice_covariance (m n : ℤ) (v : Lp ℂ 2 (volume : Measure ℝ)) :
    zakExt (tfShiftCLM (m : ℝ) (n : ℝ) v) = explicitCharLattice m n (zakExt v) := by
  convert operator_intertwining_extends_from_dense ( concreteZakDenseSubspace ) concreteZakDenseSubspace_dense ( zakExt ) ( tfShiftCLM ( m : ℝ ) ( n : ℝ ) ) ( explicitCharLattice m n ) ?_ v using 1;
  intro d;
  convert zakExt_apply ⟨ ( CriticalMixedHRT.tfShiftCLM ( m : ℝ ) ( n : ℝ ) ) d, CriticalMixedHRT.tfShiftCLM_mem ( m : ℝ ) ( n : ℝ ) d ⟩ using 1;
  rw [ zakExt_apply ];
  refine' MeasureTheory.Lp.ext _;
  filter_upwards [ CriticalMixedHRT.explicitCharLattice_coeFn m n ( CriticalMixedHRT.concreteZakDense_to_Lp d ), CriticalMixedHRT.concreteZakDense_to_Lp_apply_ae d, CriticalMixedHRT.concreteZakDense_to_Lp_apply_ae ⟨ ( CriticalMixedHRT.tfShiftCLM ( m : ℝ ) ( n : ℝ ) ) d, CriticalMixedHRT.tfShiftCLM_mem ( m : ℝ ) ( n : ℝ ) d ⟩ ] with p hp₁ hp₂ hp₃;
  convert hp₁ using 1;
  convert hp₃ using 1;
  rw [ hp₂, ccRep_tfShift ];
  convert CriticalMixedHRT.concreteZakDense_lattice_covariance_int ( ccRep d ) m n p.1 p.2 |> Eq.symm using 1

/-
**The rogue covariance law for the canonical model.**
-/
theorem canonicalAEZak_rogue_covariance (a b : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ)) :
    zakExt (tfShiftCLM a b v) = explicitCharRogue a b (zakExt v) := by
  -- Apply the operator_intertwining_extends_from_dense theorem with the given hypotheses.
  apply Eq.symm; exact (by
  have h_dense : ∀ d : concreteZakDenseSubspace, zakExt (tfShiftCLM a b (d : Lp ℂ 2 (volume : Measure ℝ))) = explicitCharRogue a b (zakExt d) := by
    intro d
    apply Eq.symm; exact (by
      have := zakExt_apply d
      have := zakExt_apply (⟨(tfShiftCLM a b) d, tfShiftCLM_mem a b d⟩ : concreteZakDenseSubspace)
      -- By definition of `rogData`, we know that `rogData a b` is a unitary operator.
      have h_unitary : ∀ G : ZakTarget, (rogData a b).toCLM G =ᵐ[zakSquareMeasure] fun p => Complex.exp (-2 * Real.pi * Complex.I * (b : ℂ) * (p.1 : ℂ)) * canonicalQuasiRep G (p.1 - a) (p.2 + b) := by
        convert explicitCharRogue_coeFn a b using 1;
      have h_eq : ∀ᵐ p ∂zakSquareMeasure, (rogData a b).toCLM (concreteZakDense_to_Lp d) p = concreteZakDense (shiftFun a b (ccRep d)) p.1 p.2 := by
        have h_eq : ∀ᵐ p ∂zakSquareMeasure, (concreteZakDense_to_Lp d : ℝ × ℝ → ℂ) (rogueShift a b p) = concreteZakDense (ccRep d) (Int.fract (p.1 - a)) (Int.fract (p.2 + b)) := by
          have h_eq : ∀ᵐ p ∂zakSquareMeasure, (concreteZakDense_to_Lp d : ℝ × ℝ → ℂ) p = concreteZakDense (ccRep d) p.1 p.2 := by
            exact concreteZakDense_to_Lp_apply_ae d;
          have h_eq : ∀ᵐ p ∂zakSquareMeasure, (concreteZakDense_to_Lp d : ℝ × ℝ → ℂ) (rogueShift a b p) = concreteZakDense (ccRep d) (rogueShift a b p).1 (rogueShift a b p).2 := by
            have h_meas_pres : MeasureTheory.MeasurePreserving (rogueShift a b) zakSquareMeasure zakSquareMeasure := rogueShift_measurePreserving a b
            exact h_meas_pres.quasiMeasurePreserving.ae ( h_eq );
          exact h_eq;
        filter_upwards [ h_unitary ( concreteZakDense_to_Lp d ), h_eq, MeasureTheory.ae_of_all _ ( fun p => CriticalMixedHRT.concreteZakDense_rogue_covariance_real ( ccRep d ) a b p.1 p.2 ) ] with p hp₁ hp₂ hp₃ ; simp_all +decide [canonicalQuasiRep];
        have :=CriticalMixedHRT.concreteZakDense_fract ( ccRep d ) ( p.1 - a ) ( p.2 + b ) ; simp_all +decide [ rogueShift ] ;
        rw [ ← mul_assoc, ← Complex.exp_add ] ; norm_num;
      have h_eq : ∀ᵐ p ∂zakSquareMeasure, (concreteZakDense_to_Lp_linearIsometry ⟨(tfShiftCLM a b) d, tfShiftCLM_mem a b d⟩) p = concreteZakDense (shiftFun a b (ccRep d)) p.1 p.2 := by
        convert concreteZakDense_to_Lp_apply_ae ⟨ ( tfShiftCLM a b ) d, tfShiftCLM_mem a b d ⟩ using 1;
        rw [ ccRep_tfShift ];
        exact Iff.symm (Eq.to_iff rfl);
      convert MeasureTheory.Lp.ext _ using 1;
      filter_upwards [ ‹∀ᵐ p ∂zakSquareMeasure, ( rogData a b ).toCLM ( concreteZakDense_to_Lp d ) p = concreteZakDense ( shiftFun a b ( ccRep d ) ) p.1 p.2›, h_eq ] with p hp₁ hp₂ using by aesop;);
  convert operator_intertwining_extends_from_dense concreteZakDenseSubspace concreteZakDenseSubspace_dense zakExt (tfShiftCLM a b) (explicitCharRogue a b) h_dense v |> Eq.symm using 1)

/-- **The canonical a.e.-level Zak model** with explicit covariance operators. -/
def canonicalAEZakModel : L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget where
  Zak := zakExt
  shift := tfShiftCLM
  charLattice := explicitCharLattice
  charRogue := explicitCharRogue
  lattice_cov := canonicalAEZak_lattice_covariance
  rogue_cov := canonicalAEZak_rogue_covariance

end

end CriticalMixedHRT