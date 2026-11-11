import Mathlib
import RequestProject.TrinomialZeros
import RequestProject.HRT.NormalizedReturnCocycle

open scoped Classical BigOperators Real
open Complex

set_option maxHeartbeats 1000000

/-!
# Parts B & C — finite zero set of the return multiplier and finite exceptional fibers

Working in the **character coordinates** `w = exp(2πi s)`, `z = exp(2πi x)` of the
torus (as in the dossier's Lemma 5.1 and Corollary 5.2), this module proves that:

* each translated lattice trinomial factor of the return multiplier has a finite
  zero set on the unit torus `S¹ × S¹`
  (`monomial_trinomial_char_zero_set_finite`);
* therefore the return multiplier's character zero set is finite
  (`normalized_return_multiplier_char_zero_set_finite`);
* and consequently the exceptional-parameter set (the `w`-projection of the zero
  set) is finite (`normalized_exceptional_parameter_set_finite`).

All factors are trinomials in the **same** pair of unimodular monomials
`ζ₁ = z^{-t₁} w^{-r₁}`, `ζ₂ = z^{-t₂} w^{-r₂}`; the monomial substitution
`(z,w) ↦ (ζ₁, ζ₂)` is injective on the torus (unimodularity), so each factor's
zero set pulls back the at-most-two trinomial zeros to finitely many torus points.
-/

namespace CriticalMixedHRT

/-
**Genuine finiteness of the trinomial character zero set.**

A trinomial `c₀ + c₁ ζ₁ + c₂ ζ₂` with nonzero coefficients has a *finite* zero
set on the unit torus `S¹ × S¹` (the certified `…_zero_set_finite` gives the
sharper `ncard ≤ 2`, but `ncard` alone does not entail finiteness for possibly
infinite sets, so we record the genuine `Set.Finite` statement here).
-/
theorem trinomial_char_zero_set_finite
    (c0 c1 c2 : ℂ) (h0 : c0 ≠ 0) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) :
    {z : ℂ × ℂ | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ c0 + c1 * z.1 + c2 * z.2 = 0}.Finite := by
  by_contra h_inf;
  -- Let $Q(z) = \overline{c_0} c_1 z^2 + (|c_0|^2 + |c_1|^2 - |c_2|^2) z + \overline{c_1} c_0$.
  set Q : Polynomial ℂ := Polynomial.C (starRingEnd ℂ c0 * c1) * Polynomial.X^2 + Polynomial.C (starRingEnd ℂ c0 * c0 + starRingEnd ℂ c1 * c1 - starRingEnd ℂ c2 * c2) * Polynomial.X + Polynomial.C (starRingEnd ℂ c1 * c0);
  -- By definition of $Q$, we know that for any $(z_1, z_2)$ in the set, $z_1$ is a root of $Q$.
  have h_root : ∀ z : ℂ × ℂ, ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ c0 + c1 * z.1 + c2 * z.2 = 0 → Q.eval z.1 = 0 := by
    simp +zetaDelta at *;
    simp_all +decide [ Complex.ext_iff, sq ];
    simp_all +decide [ Complex.normSq, Complex.norm_def, div_eq_mul_inv ];
    grind;
  -- Since $Q$ is a non-zero polynomial, it has only finitely many roots.
  have h_finite_roots : Set.Finite {z : ℂ | Q.eval z = 0} := by
    refine' Q.roots.toFinset.finite_toSet.subset fun x hx => _;
    simp +zetaDelta at *;
    exact ⟨ ne_of_apply_ne ( fun p => p.coeff 2 ) <| by norm_num [ Polynomial.coeff_C, Polynomial.coeff_X, mul_assoc, h0, h1, h2 ], hx ⟩;
  refine' h_inf ( Set.Finite.subset ( h_finite_roots.image fun x => ( x, - ( c0 + c1 * x ) / c2 ) ) _ );
  exact fun x hx => ⟨ x.1, h_root x hx, by ext <;> simp +decide [ mul_div_cancel₀ _ h2, show x.2 = - ( c0 + c1 * x.1 ) / c2 from eq_div_of_mul_eq h2 <| by linear_combination hx.2.2 ] ⟩

/-
**Injectivity of the unimodular monomial substitution on the torus.**

If `(r₁,t₁),(r₂,t₂)` is a unimodular ℤ²-basis, the monomial map
`(z,w) ↦ (z^{-t₁} w^{-r₁}, z^{-t₂} w^{-r₂})` is injective on the unit torus.
-/
theorem unimodular_monomial_torus_injOn
    (r1 t1 r2 t2 : ℤ) (huni : r1 * t2 - r2 * t1 = 1) :
    Set.InjOn (fun zw : ℂ × ℂ => (zw.1 ^ (-t1) * zw.2 ^ (-r1), zw.1 ^ (-t2) * zw.2 ^ (-r2)))
      {zw : ℂ × ℂ | ‖zw.1‖ = 1 ∧ ‖zw.2‖ = 1} := by
  intro x hx y hy hxy;
  -- Set `u = x.1 / y.1` and `v = x.2 / y.2` (both nonzero).
  set u := x.1 / y.1
  set v := x.2 / y.2
  have hu : u ^ (-t1) * v ^ (-r1) = 1 := by
    have huv : u ^ (-t1) * v ^ (-r1) = (x.1 ^ (-t1) * x.2 ^ (-r1)) / (y.1 ^ (-t1) * y.2 ^ (-r1)) := by
      rw [ div_zpow, div_zpow, mul_div_mul_comm ];
    simp_all +decide [ Prod.ext_iff ];
    exact ⟨ zpow_ne_zero _ ( by aesop_cat ), zpow_ne_zero _ ( by aesop_cat ) ⟩
  have hv : u ^ (-t2) * v ^ (-r2) = 1 := by
    simp +zetaDelta at *;
    by_cases hx1 : x.1 = 0 <;> by_cases hy1 : y.1 = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    convert congr_arg ( fun z => z * ( y.1 ^ t2 * y.2 ^ r2 ) ) hxy.2 using 1 <;> ring;
    · simp +decide [ mul_zpow, zpow_neg, mul_assoc, mul_comm, mul_left_comm ];
    · simp +decide [ show y.1 ^ t2 ≠ 0 from zpow_ne_zero _ hy1, show y.2 ^ r2 ≠ 0 from zpow_ne_zero _ ( by aesop ) ];
  -- From `u^(-t1) * v^(-r1) = 1` and `u^(-t2) * v^(-r2) = 1`, we get `u = 1` and `v = 1`.
  have hu_one : u = 1 := by
    have hu_one : u ^ (r1 * t2 - r2 * t1) = 1 := by
      have hu_one : u ^ (r1 * t2) * v ^ (r1 * r2) = 1 ∧ u ^ (r2 * t1) * v ^ (r1 * r2) = 1 := by
        have hu_one : u ^ (r1 * t2) * v ^ (r1 * r2) = (u ^ (-t2) * v ^ (-r2)) ^ (-r1) := by
          rw [ mul_zpow ] ; group
        have hv_one : u ^ (r2 * t1) * v ^ (r1 * r2) = (u ^ (-t1) * v ^ (-r1)) ^ (-r2) := by
          rw [ mul_zpow ] ; group;
        aesop;
      rw [ zpow_sub₀ ] <;> norm_num [ hu_one ];
      · grind;
      · aesop;
    aesop
  have hv_one : v = 1 := by
    have h_coprime : ∃ a b : ℤ, a * r1 + b * r2 = 1 := by
      exact ⟨ t2, -t1, by linarith ⟩;
    obtain ⟨ a, b, h ⟩ := h_coprime; rw [ show v = v ^ ( a * r1 + b * r2 ) by rw [ h, zpow_one ] ] ; rw [ zpow_add', zpow_mul', zpow_mul' ] <;> aesop;
  exact Prod.ext ( eq_of_div_eq_one hu_one ) ( eq_of_div_eq_one hv_one )

/-
**Part B (single factor).**  A monomial-substituted trinomial
`c₀ + b₁ (z^{-t₁} w^{-r₁}) + b₂ (z^{-t₂} w^{-r₂})` with nonzero coefficients and a
unimodular exponent pair has a finite zero set on the unit torus.
-/
theorem monomial_trinomial_char_zero_set_finite
    (c0 : ℂ) (h0 : c0 ≠ 0) (b1 b2 : ℂ) (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (r1 t1 r2 t2 : ℤ) (huni : r1 * t2 - r2 * t1 = 1) :
    {zw : ℂ × ℂ | ‖zw.1‖ = 1 ∧ ‖zw.2‖ = 1 ∧
        c0 + b1 * (zw.1 ^ (-t1) * zw.2 ^ (-r1)) + b2 * (zw.1 ^ (-t2) * zw.2 ^ (-r2)) = 0}.Finite := by
  convert Set.Finite.of_finite_image _ _;
  exact ℂ × ℂ;
  use fun zw => ( zw.1 ^ ( -t1 ) * zw.2 ^ ( -r1 ), zw.1 ^ ( -t2 ) * zw.2 ^ ( -r2 ) );
  · refine' Set.Finite.subset ( trinomial_char_zero_set_finite c0 b1 b2 h0 hb1 hb2 ) _;
    simp +contextual [ Set.image_subset_iff ];
  · exact Set.InjOn.mono ( fun x hx => by aesop ) ( unimodular_monomial_torus_injOn r1 t1 r2 t2 huni )

/-
**Part B (return multiplier).**  Since every factor is a trinomial in the same
unimodular monomials, the character zero set of a finite product of such factors
(the return multiplier, up to its nowhere-zero monomial prefactor) is finite — it
is the finite union of the per-factor finite zero sets.
-/
theorem normalized_return_multiplier_char_zero_set_finite
    {ι : Type*} (s : Finset ι)
    (c0 : ℂ) (h0 : c0 ≠ 0) (b1 b2 : ι → ℂ)
    (hb1 : ∀ j ∈ s, b1 j ≠ 0) (hb2 : ∀ j ∈ s, b2 j ≠ 0)
    (r1 t1 r2 t2 : ℤ) (huni : r1 * t2 - r2 * t1 = 1) :
    {zw : ℂ × ℂ | ‖zw.1‖ = 1 ∧ ‖zw.2‖ = 1 ∧
        ∏ j ∈ s,
          (c0 + b1 j * (zw.1 ^ (-t1) * zw.2 ^ (-r1)) +
                 b2 j * (zw.1 ^ (-t2) * zw.2 ^ (-r2))) = 0}.Finite := by
  refine' Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet s ) fun j hj => monomial_trinomial_char_zero_set_finite c0 h0 ( b1 j ) ( b2 j ) ( hb1 j hj ) ( hb2 j hj ) r1 t1 r2 t2 huni ) _;
  simp +contextual [ Finset.prod_eq_zero_iff, Set.subset_def ]

/-
**Part C — finite exceptional-parameter set.**

The exceptional `w`-set — those frequency-circle points `w` for which some
time-circle point `z` makes the return multiplier vanish — is the `w`-projection
of the finite zero set, hence finite.
-/
theorem normalized_exceptional_parameter_set_finite
    {ι : Type*} (s : Finset ι)
    (c0 : ℂ) (h0 : c0 ≠ 0) (b1 b2 : ι → ℂ)
    (hb1 : ∀ j ∈ s, b1 j ≠ 0) (hb2 : ∀ j ∈ s, b2 j ≠ 0)
    (r1 t1 r2 t2 : ℤ) (huni : r1 * t2 - r2 * t1 = 1) :
    {w : ℂ | ‖w‖ = 1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
        ∏ j ∈ s,
          (c0 + b1 j * (z ^ (-t1) * w ^ (-r1)) +
                 b2 j * (z ^ (-t2) * w ^ (-r2))) = 0}.Finite := by
  have h_finite : {zw : ℂ × ℂ | ‖zw.1‖ = 1 ∧ ‖zw.2‖ = 1 ∧ ∏ j ∈ s, (c0 + b1 j * (zw.1 ^ (-t1) * zw.2 ^ (-r1)) + b2 j * (zw.1 ^ (-t2) * zw.2 ^ (-r2))) = 0}.Finite := by
    convert normalized_return_multiplier_char_zero_set_finite s c0 h0 b1 b2 hb1 hb2 r1 t1 r2 t2 huni using 1;
  exact Set.Finite.subset ( h_finite.image fun zw => zw.2 ) fun w hw => by cases' hw with hw₁ hw₂; cases' hw₂ with z hz; aesop;

/-
Preimage finiteness: the set of frequencies `s` in a **bounded** window whose
character `exp(2πi s)` lands in a finite set is finite (the character map is
injective on intervals of length `< 1`, and a bounded window meets only finitely
many integer translates).
-/
theorem char_preimage_window_finite (Echar : Set ℂ) (hE : Echar.Finite) (A B : ℝ) :
    {s : ℝ | s ∈ Set.Ioo A B ∧
        Complex.exp (2 * ↑Real.pi * Complex.I * (s : ℂ)) ∈ Echar}.Finite := by
  -- Define `g : ℝ → ℂ × ℤ` by `g s = (Complex.exp (2 * π * I * s), ⌊s⌋)`.
  set g : ℝ → ℂ × ℤ := fun s => (Complex.exp (2 * Real.pi * Complex.I * s), Int.floor s);
  -- We show `g` is injective on `T`, and that `g '' T` is finite; then `T` is finite by `Set.Finite.of_finite_image`.
  have hg_inj : Set.InjOn g {s : ℝ | s ∈ Set.Ioo A B ∧ Complex.exp (2 * Real.pi * Complex.I * s) ∈ Echar} := by
    intro s hs t ht; simp_all +decide;
    simp +zetaDelta at *;
    intro h1 h2; rw [ Complex.exp_eq_exp_iff_exists_int ] at h1; obtain ⟨ k, hk ⟩ := h1; simp_all +decide [ Complex.ext_iff ] ;
    rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, Int.floor_le s, Int.lt_floor_add_one s, Int.floor_le t, Int.lt_floor_add_one t, show ( ⌊s⌋ : ℝ ) = ⌊t⌋ from mod_cast h2 ];
  refine Set.Finite.of_finite_image ?_ hg_inj;
  refine' Set.Finite.subset ( hE.prod ( Set.finite_Icc ( ⌊A⌋ ) ( ⌊B⌋ ) ) ) _;
  exact Set.image_subset_iff.mpr fun x hx => ⟨ hx.2, ⟨ Int.floor_mono hx.1.1.le, Int.floor_mono hx.1.2.le ⟩ ⟩

/-
**Part C (windowed form).**  On a bounded frequency window `(A, B)`, the
exceptional-parameter set — those `σ` for which some time-circle point `z` makes
the return multiplier vanish — is finite.  This is the form discharging the
finite-exceptional hypothesis `E` of the strengthened Stage-6A bridge
`normalized_return_cocycle_feeds_no_flat_band_integrated`.
-/
theorem normalized_window_exceptional_parameter_set_finite
    {ι : Type*} (sfin : Finset ι)
    (c0 : ℂ) (h0 : c0 ≠ 0) (b1 b2 : ι → ℂ)
    (hb1 : ∀ j ∈ sfin, b1 j ≠ 0) (hb2 : ∀ j ∈ sfin, b2 j ≠ 0)
    (r1 t1 r2 t2 : ℤ) (huni : r1 * t2 - r2 * t1 = 1) (A B : ℝ) :
    {σ : ℝ | σ ∈ Set.Ioo A B ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
        ∏ j ∈ sfin,
          (c0 + b1 j * (z ^ (-t1) * (Complex.exp (2 * ↑Real.pi * Complex.I * (σ : ℂ))) ^ (-r1)) +
                 b2 j * (z ^ (-t2) * (Complex.exp (2 * ↑Real.pi * Complex.I * (σ : ℂ))) ^ (-r2))) = 0}.Finite := by
  convert char_preimage_window_finite _ ( normalized_exceptional_parameter_set_finite sfin c0 h0 b1 b2 hb1 hb2 r1 t1 r2 t2 huni ) A B;
  simp +decide [ Complex.norm_exp ]

end CriticalMixedHRT