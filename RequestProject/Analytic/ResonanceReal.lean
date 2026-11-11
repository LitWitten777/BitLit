import Mathlib
import RequestProject.ResonanceGroup

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology

/-!
# The real resonance set is null

The *real resonance set* `resonanceReal q` consists of the real numbers `t`
for which `exp(2πi qₙ t) → 1`.  It is the preimage of the additive-circle
resonance set under the quotient map `ℝ → ℝ/ℤ`, hence (being `1`-periodic and
null on a fundamental domain) it has Lebesgue measure zero on all of `ℝ`.
-/

namespace CriticalMixedHRT

/-- The real resonance set: angles whose `qₙ`-multiples drive `exp(2πi qₙ t)`
to `1`. -/
def resonanceReal (q : ℕ → ℕ) : Set ℝ :=
  {t : ℝ | Filter.Tendsto
    (fun n => Complex.exp (2 * Real.pi * Complex.I * (q n : ℂ) * (t : ℂ)))
    Filter.atTop (nhds 1)}

/-
A `1`-periodic set that is null on the fundamental domain `Ioc 0 1` is
null on all of `ℝ`.
-/
theorem volume_zero_of_periodic_one
    (A : Set ℝ) (hper : ∀ x : ℝ, x + 1 ∈ A ↔ x ∈ A)
    (h01 : volume (A ∩ Set.Ioc (0 : ℝ) 1) = 0) :
    volume A = 0 := by
  -- For each $k \in \mathbb{Z}$, we have $A \cap (k, k+1] = (A \cap (0, 1]) + k$.
  have htranslate : ∀ k : ℤ, A ∩ Set.Ioc (k : ℝ) (k + 1) = (fun y => y + k : ℝ → ℝ) '' (A ∩ Set.Ioc 0 1) := by
    intro k;
    -- By definition of $A$, we know that $x \in A$ if and only if $x - k \in A$ for any integer $k$.
    have h_periodic : ∀ x : ℝ, x ∈ A ↔ x - k ∈ A := by
      induction' k using Int.induction_on with n ihn n ihn;
      · norm_num;
      · grind;
      · grind;
    ext x;
    simp +zetaDelta at *;
    rw [ h_periodic x ] ; ring;
  -- Since $A$ is the union of its intersections with each interval $(k, k+1]$, we can write
  have hunion : A = ⋃ k : ℤ, A ∩ Set.Ioc (k : ℝ) (k + 1) := by
    ext x
    simp [Set.mem_iUnion];
    by_cases hx : x ∈ Set.range (fun n : ℤ => (n : ℝ));
    · obtain ⟨ n, rfl ⟩ := hx; exact fun _ => ⟨ n - 1, by push_cast; linarith, by push_cast; linarith ⟩ ;
    · exact fun hx' => ⟨ ⌊x⌋, lt_of_le_of_ne ( Int.floor_le x ) fun h => hx <| h.symm ▸ Set.mem_range_self _, Int.lt_floor_add_one x |> le_of_lt ⟩;
  rw [ hunion, MeasureTheory.measure_iUnion_null_iff ] ; simp_all +singlePass [ Set.preimage ] ;

/-
The real resonance set equals the preimage, under `ℝ → ℝ/ℤ`, of the
additive-circle resonance set.
-/
theorem resonanceReal_eq_preimage (q : ℕ → ℕ) :
    resonanceReal q
      = (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) ⁻¹'
          {x : AddCircle (1 : ℝ) |
            Filter.Tendsto (fun n => (q n) • x) Filter.atTop (nhds 0)} := by
  convert Set.ext _;
  intro x;
  -- Let `e := AddCircle.homeomorphCircle (T:=1) one_ne_zero : AddCircle 1 ≃ₜ Circle`.
  set e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num);
  -- Since `e` is a homeomorphism, `Tendsto (fun n => (q n) • (↑x : AddCircle 1)) atTop (𝓝 0)` ↔ `Tendsto (fun n => e ((q n) • ↑x)) atTop (𝓝 (e 0))`.
  have h_homeo : Filter.Tendsto (fun n => (q n) • (↑x : AddCircle (1 : ℝ))) Filter.atTop (nhds 0) ↔ Filter.Tendsto (fun n => e ((q n) • (↑x : AddCircle (1 : ℝ)))) Filter.atTop (nhds (e 0)) := by
    constructor <;> intro h;
    · exact e.continuous.continuousAt.tendsto.comp h;
    · convert e.symm.continuous.continuousAt.tendsto.comp h using 1;
      · aesop;
      · rw [ e.symm_apply_apply ];
  simp_all +decide [ resonanceReal ];
  convert tendsto_subtype_rng.symm using 2 ; norm_num [ e, AddCircle.homeomorphCircle_apply ] ; ring;
  · ext; rw [ AddCircle.toCircle_nsmul ] ; norm_num [ AddCircle.toCircle_apply_mk ] ; ring;
    rw [ ← Complex.exp_nat_mul ] ; ring;
  · erw [ AddCircle.homeomorphCircle_apply ] ; norm_num

/-
**The real resonance set is null.**
-/
theorem resonanceReal_volume_zero
    (q : ℕ → ℕ) (hq : Filter.Tendsto q Filter.atTop Filter.atTop) :
    volume (resonanceReal q) = 0 := by
  convert volume_zero_of_periodic_one ( resonanceReal q ) _ _ using 1;
  · unfold resonanceReal;
    norm_num [ mul_add, mul_comm ( 2 * Real.pi * Complex.I ), Complex.exp_add ];
  · rw [ ← MeasureTheory.measure_preimage_add_right ];
    convert resonance_group_haar_measure_zero q hq using 1;
    swap;
    exact 0;
    convert ( AddCircle.measurePreserving_mk ( 1 : ℝ ) 0 |> MeasurePreserving.map_eq ) |> congr_arg ( fun m => m { x : AddCircle ( 1 : ℝ ) | Filter.Tendsto ( fun n => ( q n : ℕ ) • x ) Filter.atTop ( nhds 0 ) } ) using 1;
    rw [ MeasureTheory.Measure.map_apply ];
    · rw [ MeasureTheory.Measure.restrict_apply' ];
      · convert rfl using 2 ; ext ; simp +decide [ resonanceReal_eq_preimage ];
      · norm_num;
    · fun_prop;
    · exact measurableSet_tendsto _ ( by measurability )

end CriticalMixedHRT