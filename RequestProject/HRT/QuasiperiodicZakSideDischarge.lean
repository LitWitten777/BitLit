import Mathlib
import RequestProject.HRT.QuasiperiodicTargetOperatorFormula

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — discharging the whole quasiperiodic Zak side from the two
target-operator formulas

This module proves that the two remaining target-operator formula blockers

```
StandardTargetLatticeOperatorRepresentativeAE
StandardTargetRogueOperatorRepresentativeAE
```

are **sufficient** to discharge the corrected quasiperiodic Zak-side blocker
`StandardActualZakQuasiRepresentativeEquationAE` and all downstream endpoints.

The argument:

1. `oneStepEquation_ae_square_of_operatorFormulas` — applying the (unconditional)
   target `Lp` one-step relation `target_Lp_one_step_Zak_relation` and the two
   operator formulas, the one-step fibre equation for the quasiperiodic
   representative holds a.e. on the fundamental square `zakSquareMeasure`.
2. `oneStepEquation_quasiRep_succ_x_iff` / `oneStepEquation_quasiRep_succ_s_iff`
   — the one-step equation for the quasiperiodic representative is invariant under
   the integer translations `x ↦ x+1`, `s ↦ s+1` (the matching characters cancel,
   using `zakQuasiPeriodicRep_quasiperiodic_x` and `zakQuasiPeriodicRep_periodic_s`).
3. `ae_iterated_of_ae_square_of_periodic` — a general measure-theoretic transport:
   a `ℤ²`-translation-invariant property that holds a.e. on the half-open unit
   square holds a.e. (iterated) on all of `ℝ²` (the square tiles `ℝ²`, and the
   bad set is contained in a countable union of null translates).
4. `StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas` — the
   assembled discharge of the corrected blocker.
5. The closed downstream endpoints.

No `sorry`, no `axiom`, no `unsafe`, no `@[implemented_by]`.
-/

namespace CriticalMixedHRT

/-! ## A general measure-theoretic transport from the unit square to the line -/

/-
**`ℤ²`-periodic a.e. transport.**

If `P : ℝ → ℝ → Prop` is invariant under the integer translations `x ↦ x+1` and
`s ↦ s+1` and holds a.e. on the half-open unit square `zakSquareMeasure`, then it
holds a.e. (iterated) on all of `ℝ²`.  The half-open square `(0,1]²` tiles `ℝ²`
under `ℤ²`-translations, so the bad set is contained in a countable union of
Lebesgue-null translates of a null superset of the bad set on the square.
-/
theorem ae_iterated_of_ae_square_of_periodic
    (P : ℝ → ℝ → Prop)
    (hsq : ∀ᵐ q ∂zakSquareMeasure, P q.1 q.2)
    (hx : ∀ x s, P (x + 1) s ↔ P x s)
    (hs : ∀ x s, P x (s + 1) ↔ P x s) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ), P x s := by
  have h_periodic : ∀ᵐ (q : ℝ × ℝ) ∂(volume : Measure (ℝ × ℝ)), P q.1 q.2 := by
    -- Let's denote the set of points where `P` does not hold by `B`.
    set B : Set (ℝ × ℝ) := {q : ℝ × ℝ | ¬P q.1 q.2};
    -- Since $B$ is periodic with period 1 in both variables, we can cover $B$ with countably many translates of $B \cap (0,1] \times (0,1]$.
    have h_cover : B ⊆ ⋃ (n : ℤ × ℤ), (fun q => q + ((n.1 : ℝ), (n.2 : ℝ))) '' (B ∩ Set.Ioc 0 1 ×ˢ Set.Ioc 0 1) := by
      intro q hq
      simp [B] at hq ⊢;
      refine' ⟨ ⌈q.1⌉ - 1, ⌈q.2⌉ - 1, _, _, _ ⟩ <;> norm_num;
      · -- By periodicity, we have $P(q.1 + (1 - ⌈q.1⌉), q.2 + (1 - ⌈q.2⌉)) ↔ P(q.1, q.2)$.
        have h_periodic : ∀ (x y : ℝ), ∀ (n m : ℤ), P (x + n) (y + m) ↔ P x y := by
          intros x y n m; induction' n using Int.induction_on with n ihn n ihn ; induction' m using Int.induction_on with m ihm m ihm ; aesop;
          · simp_all +decide [ ← add_assoc ];
          · grind;
          · simp_all +decide [ ← add_assoc ];
          · grind;
        specialize h_periodic q.1 q.2 ( 1 - ⌈q.1⌉ ) ( 1 - ⌈q.2⌉ ) ; aesop;
      · exact ⟨ sub_lt_iff_lt_add.mpr <| Int.ceil_lt_add_one _, Int.le_ceil _ ⟩;
      · exact ⟨ sub_lt_iff_lt_add.mpr <| Int.ceil_lt_add_one _, Int.le_ceil _ ⟩;
    -- Since $B \cap (0,1] \times (0,1]$ has measure zero, each translate of it also has measure zero.
    have h_translate_zero : ∀ n : ℤ × ℤ, MeasureTheory.volume ((fun q => q + ((n.1 : ℝ), (n.2 : ℝ))) '' (B ∩ Set.Ioc 0 1 ×ˢ Set.Ioc 0 1)) = 0 := by
      intro n
      have h_measure_zero : MeasureTheory.volume (B ∩ Set.Ioc 0 1 ×ˢ Set.Ioc 0 1) = 0 := by
        rw [ MeasureTheory.ae_iff ] at hsq;
        rw [ zakSquareMeasure ] at hsq;
        rw [ MeasureTheory.Measure.restrict_apply' ] at hsq;
        · exact hsq;
        · exact measurableSet_Ioc.prod measurableSet_Ioc;
      rw [ Set.image_add_right ];
      rw [ MeasureTheory.measure_preimage_add_right ] ; aesop;
    exact MeasureTheory.measure_mono_null h_cover ( MeasureTheory.measure_iUnion_null fun n => h_translate_zero n );
  have h_periodic_swap : ∀ᵐ (q : ℝ × ℝ) ∂(volume : Measure (ℝ × ℝ)), P q.2 q.1 := by
    have h_swap : MeasureTheory.MeasurePreserving (fun q : ℝ × ℝ => (q.2, q.1)) (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
      refine' ⟨ measurable_swap, _ ⟩;
      exact MeasureTheory.Measure.prod_swap ..
    have := h_swap.preimage_null h_periodic; aesop;
  convert MeasureTheory.Measure.ae_ae_of_ae_prod h_periodic_swap using 1

/-! ## Integer-translation invariance of the one-step equation -/

/-
The one-step equation for the quasiperiodic representative is invariant under
`x ↦ x + 1`.
-/
theorem oneStepEquation_quasiRep_succ_x_iff
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (G : ZakTarget) (x s : ℝ) :
    oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (zakQuasiPeriodicRep G) (x + 1) s ↔
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (zakQuasiPeriodicRep G) x s := by
  constructor <;> intro h;
  · unfold oneStepEquation at *;
    convert congr_arg ( fun z => z / Complex.exp ( 2 * Real.pi * Complex.I * ( s + p / ( m : ℂ ) ) ) ) h using 1 <;> norm_num [ Complex.exp_ne_zero, mul_assoc, mul_left_comm, mul_comm ];
    · rw [ eq_div_iff ( Complex.exp_ne_zero _ ) ];
      rw [ show x + 1 - a = ( x - a ) + 1 by ring, zakQuasiPeriodicRep_quasiperiodic_x ] ; ring;
      push_cast; ring;
    · rw [ eq_div_iff ( Complex.exp_ne_zero _ ) ] ; norm_num [ Pfun, zakQuasiPeriodicRep_quasiperiodic_x ] ; ring;
      norm_num [ Complex.exp_add, Complex.exp_sub ] ; ring;
      norm_num [ Complex.exp_neg, Complex.exp_ne_zero ];
      norm_num [ show Complex.exp ( Real.pi * Complex.I * t₁ * 2 ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use t₁; ring, show Complex.exp ( Real.pi * Complex.I * t₂ * 2 ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use t₂; ring ];
  · unfold oneStepEquation at *;
    convert congr_arg ( fun z => Complex.exp ( 2 * Real.pi * Complex.I * ( s + p / m ) ) * z ) h using 1 <;> norm_num [ zakQuasiPeriodicRep_quasiperiodic_x, zakQuasiPeriodicRep_periodic_s ] ; ring;
    · convert zakQuasiPeriodicRep_quasiperiodic_x G ( x - a ) ( s + p / m ) using 1 ; ring;
      push_cast; ring;
    · unfold Pfun; ring; norm_num [ Complex.exp_add ] ; ring;
      norm_num [ sub_eq_add_neg, Complex.exp_add ] ; ring;
      norm_num [ show Complex.exp ( - ( Real.pi * Complex.I * t₁ * 2 ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use -t₁; push_cast; ring, show Complex.exp ( - ( Real.pi * Complex.I * t₂ * 2 ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use -t₂; push_cast; ring ]

/-
The one-step equation for the quasiperiodic representative is invariant under
`s ↦ s + 1`.
-/
theorem oneStepEquation_quasiRep_succ_s_iff
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (r₁ t₁ r₂ t₂ : ℤ)
    (G : ZakTarget) (x s : ℝ) :
    oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (zakQuasiPeriodicRep G) x (s + 1) ↔
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ (zakQuasiPeriodicRep G) x s := by
  unfold oneStepEquation Pfun;
  convert Iff.rfl using 2;
  · rw [ add_right_comm, zakQuasiPeriodicRep_periodic_s ];
  · rw [ zakQuasiPeriodicRep_periodic_s ] ; norm_num [ Complex.exp_add, mul_add ] ; ring;
    norm_num [ show Complex.exp ( - ( Real.pi * Complex.I * r₁ * 2 ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use -r₁; push_cast; ring, show Complex.exp ( - ( Real.pi * Complex.I * r₂ * 2 ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use -r₂; push_cast; ring ]

/-! ## The a.e.-square one-step equation from the operator formulas -/

/-
From the unconditional target `Lp` one-step relation and the two operator
formulas, the one-step fibre equation for the quasiperiodic representative holds
a.e. on the fundamental square.
-/
theorem oneStepEquation_ae_square_of_operatorFormulas
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∀ᵐ q ∂zakSquareMeasure,
      oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakQuasiPeriodicRep (concreteAEZakModel.Zak f)) q.1 q.2 := by
  have := hrel;
  have h_eq : c₀ • (concreteAEZakModel.Zak f) + c₁ • (concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)) + c₂ • (concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)) + c₃ • (concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ)) (concreteAEZakModel.Zak f)) = 0 := by
    convert target_Lp_one_step_Zak_relation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂ f this using 1;
  have h_eq : ∀ᵐ q ∂zakSquareMeasure, c₀ * (concreteAEZakModel.Zak f) q + c₁ * (concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)) q + c₂ * (concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)) q + c₃ * (concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ)) (concreteAEZakModel.Zak f)) q = 0 := by
    have h_eq : ∀ᵐ q ∂zakSquareMeasure, (c₀ • (concreteAEZakModel.Zak f) + c₁ • (concreteAEZakModel.charLattice r₁ t₁ (concreteAEZakModel.Zak f)) + c₂ • (concreteAEZakModel.charLattice r₂ t₂ (concreteAEZakModel.Zak f)) + c₃ • (concreteAEZakModel.charRogue a ((p : ℝ) / (m : ℝ)) (concreteAEZakModel.Zak f))) q = 0 := by
      rw [h_eq];
      exact MeasureTheory.AEEqFun.coeFn_zero;
    filter_upwards [ h_eq, MeasureTheory.Lp.coeFn_add ( c₀ • concreteAEZakModel.Zak f ) ( c₁ • ( concreteAEZakModel.charLattice r₁ t₁ ) ( concreteAEZakModel.Zak f ) ), MeasureTheory.Lp.coeFn_add ( c₀ • concreteAEZakModel.Zak f + c₁ • ( concreteAEZakModel.charLattice r₁ t₁ ) ( concreteAEZakModel.Zak f ) ) ( c₂ • ( concreteAEZakModel.charLattice r₂ t₂ ) ( concreteAEZakModel.Zak f ) ), MeasureTheory.Lp.coeFn_add ( c₀ • concreteAEZakModel.Zak f + c₁ • ( concreteAEZakModel.charLattice r₁ t₁ ) ( concreteAEZakModel.Zak f ) + c₂ • ( concreteAEZakModel.charLattice r₂ t₂ ) ( concreteAEZakModel.Zak f ) ) ( c₃ • ( concreteAEZakModel.charRogue a ( p / m ) ) ( concreteAEZakModel.Zak f ) ), MeasureTheory.Lp.coeFn_smul c₀ ( concreteAEZakModel.Zak f ), MeasureTheory.Lp.coeFn_smul c₁ ( ( concreteAEZakModel.charLattice r₁ t₁ ) ( concreteAEZakModel.Zak f ) ), MeasureTheory.Lp.coeFn_smul c₂ ( ( concreteAEZakModel.charLattice r₂ t₂ ) ( concreteAEZakModel.Zak f ) ), MeasureTheory.Lp.coeFn_smul c₃ ( ( concreteAEZakModel.charRogue a ( p / m ) ) ( concreteAEZakModel.Zak f ) ) ] with q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈;
    simp_all +decide [ add_assoc ];
  filter_upwards [ h_eq, hlat r₁ t₁ ( concreteAEZakModel.Zak f ), hlat r₂ t₂ ( concreteAEZakModel.Zak f ), hrog a ( p / m ) ( concreteAEZakModel.Zak f ), CriticalMixedHRT.zakQuasiPeriodicRep_ae_eq_on_fundamental_domain ( concreteAEZakModel.Zak f ) ] with q hq₁ hq₂ hq₃ hq₄ hq₅;
  unfold oneStepEquation;
  unfold Pfun; simp_all +decide [ Complex.exp_neg ] ;
  field_simp at *;
  linear_combination' hq₁

/-! ## Assembled discharge of the corrected blocker -/

/-- **The two operator formulas discharge the corrected quasiperiodic blocker.**

Combining `oneStepEquation_ae_square_of_operatorFormulas` (a.e. on the square)
with the integer-translation invariance and the general transport
`ae_iterated_of_ae_square_of_periodic`, the corrected blocker
`StandardActualZakQuasiRepresentativeEquationAE` holds. -/
theorem StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE) :
    StandardActualZakQuasiRepresentativeEquationAE := by
  intro m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel
  refine ae_iterated_of_ae_square_of_periodic
    (fun x s => oneStepEquation m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
        (zakQuasiPeriodicRep (concreteAEZakModel.Zak f)) x s)
    (oneStepEquation_ae_square_of_operatorFormulas hlat hrog m p a c₀ c₁ c₂ c₃ hc₃
      r₁ t₁ r₂ t₂ f hrel)
    (fun x s => oneStepEquation_quasiRep_succ_x_iff m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂
      (concreteAEZakModel.Zak f) x s)
    (fun x s => oneStepEquation_quasiRep_succ_s_iff m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂
      (concreteAEZakModel.Zak f) x s)

/-! ## Closed downstream endpoints -/

/-- **Task D — the corrected residual equation, discharged from the two operator
formulas.** -/
theorem StandardActualZakQuasiRepresentativeEquationAE_proved
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE) :
    StandardActualZakQuasiRepresentativeEquationAE :=
  StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas hlat hrog

/-- **Task D — genuine `NontrivialAEFiberExtraction`, discharged from the two
operator formulas.** -/
theorem actual_L2_zak_nontrivial_fiber_extraction_quasi_closed
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE)
    (m : ℕ) (p : ℤ) (a : ℝ) (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0) (r₁ t₁ r₂ t₂ : ℤ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    Nonempty (NontrivialAEFiberExtraction m p a c₀ c₁ c₂ c₃ r₁ t₁ r₂ t₂) :=
  actual_L2_zak_nontrivial_fiber_extraction_quasi
    (StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas hlat hrog)
    m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hf hrel

/-- **Task D — corrected `L²`-level Zak relation feeds the a.e. no-flat-band
machinery, discharged from the two operator formulas.** -/
theorem zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_quasi_closed
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE)
    {m : ℕ} (hm : 0 < m) {p : ℤ} {a : ℝ}
    (hθ_irr : Irrational ((m : ℝ) * a))
    {c₀ c₁ c₂ c₃ : ℂ}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    {r₁ t₁ r₂ t₂ : ℤ} (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0)
    (DK : DenjoyKoksmaReturnData ((m : ℝ) * a))
    (hq : Tendsto DK.q atTop atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (Efin : Set ℝ) (hE : Efin.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (((m : ℝ) * a : ℝ) : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False :=
  zak_relation_feeds_ae_normalized_no_flat_band_actual_L2_Zak_quasi
    (StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas hlat hrog)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

/-- **Task D — final Stage 6B contradiction, discharged from the two operator
formulas (corrected, Zak-side interface reduced to the two operator formulas).** -/
theorem critical_mixed_final_contradiction_without_Zak_side_interface_corrected
    (hlat : StandardTargetLatticeOperatorRepresentativeAE)
    (hrog : StandardTargetRogueOperatorRepresentativeAE)
    {m : ℕ} (hm : 0 < m) {p : ℤ} {a : ℝ}
    (hθ_irr : Irrational ((m : ℝ) * a))
    {c₀ c₁ c₂ c₃ : ℂ}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    {r₁ t₁ r₂ t₂ : ℤ} (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (hrel : c₀ • f + c₁ • concreteAEZakModel.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • concreteAEZakModel.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • concreteAEZakModel.shift a ((p : ℝ) / (m : ℝ)) f = 0)
    (DK : DenjoyKoksmaReturnData ((m : ℝ) * a))
    (hq : Tendsto DK.q atTop atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (Efin : Set ℝ) (hE : Efin.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (((m : ℝ) * a : ℝ) : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hroots : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∃ r : Fin dlau → ℂ,
        (∀ i, ‖r i‖ ≠ 1) ∧
        Mlau = ↑((Finset.univ.filter (fun i : Fin dlau => ‖r i‖ < 1)).card) ∧
        (Finset.univ.filter (fun i : Fin dlau => 1 < ‖r i‖)).card = mlau ∧
        Polynomial.C (evalLaurentCircle ad t) *
          ∏ i : Fin dlau, (Polynomial.X - Polynomial.C (r i)) =
          ∑ j : Fin (dlau + 1),
            Polynomial.C (evalLaurentCircle (coeffs j) t) * Polynomial.X ^ (j : ℕ))
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False :=
  critical_mixed_final_contradiction_with_actual_L2_Zak_quasi
    (StandardActualZakQuasiRepresentativeEquationAE_of_operatorFormulas hlat hrog)
    hm hθ_irr hc₀ hc₁ hc₂ hc₃ unimodular f hf hrel DK hq H hH hHne S hSU hSpos hSres
    Efin hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff hroots hJholo

end CriticalMixedHRT