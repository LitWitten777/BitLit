import Mathlib
import RequestProject.JensenHolonomy
import RequestProject.HRT.ReturnMultiplierRootData
import RequestProject.HRT.RootDataAdapter

open Complex Polynomial Finset
open scoped BigOperators Real Classical ENNReal
open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000

/-!
# Root-data minimal interface — canonical reduction of `hroots_min`

`RootDataAdapter.lean` reduced the certificate's full root-factorisation data
`hroots` to the *minimal geometric core* `hroots_min`, namely, per active fibre
`t`:

```
(∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1)                       -- (1) off-circle
∧ Mlau = ((fibrePoly coeffs t).roots.filter (‖·‖ < 1)).card        -- (2) inside count
∧ ((fibrePoly coeffs t).roots.filter (1 < ‖·‖)).card = mlau.       -- (3) outside count
```

This module carries that reduction one step further, replacing each part of
`hroots_min` by a *more canonical* statement tied directly to the analytic
content of the return multiplier:

* **Part (1) — off-circle ⇐ zero-free arc.**
  `return_multiplier_no_unit_circle_roots_on_active_arc`: if the fibre polynomial
  is zero-free along the unit-circle parametrisation `x ↦ circleParam x` (which is
  exactly the statement that the *return multiplier* is zero-free along the fibre,
  since `(fibrePoly coeffs t).eval (circleParam x) = B_t(x)·(circleParam x)^M`),
  then the polynomial has no root on the unit circle.  The bridge is the
  surjectivity of `circleParam` onto the unit circle
  (`circleParam_surjective_onto_unit_circle`).

* **Part (3) — outside count ⇐ inside count + degree.**
  `fibrePoly_inside_add_outside` shows that, when the leading coefficient is
  nonzero and there are no roots on the circle, the inside and outside counts sum
  to the degree `d`.  Hence the outside count `(3)` is *not* independent data: it
  is forced by the inside count `(2)` together with the single global numeric
  identity `mlau = d - Mlau` (the certificate root-list compatibility).
  `fibrePoly_outside_count_of_inside_count` records this.

Putting these together, `hroots_min` is implied by the strictly smaller
**canonical reduced interface**

```
(∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)           -- (1') zero-free arc
∧ Mlau = ((fibrePoly coeffs t).roots.filter (‖·‖ < 1)).card        -- (2) inside count
```

together with the global numeric compatibility `(mlau : ℤ) = d - Mlau`.

Main declarations:

* `circleParam_surjective_onto_unit_circle`;
* `return_multiplier_no_unit_circle_roots_on_active_arc` (Task C);
* `fibrePoly_inside_add_outside`, `fibrePoly_outside_count_of_inside_count`;
* `return_multiplier_root_data_minimal_proved` — per fibre: the canonical reduced
  interface yields `hroots_min`;
* `hroots_min_proved` — interval form;
* `normalized_return_cocycle_feeds_no_flat_band_root_data_closed` — the Stage 6A →
  Stage 5 bridge driven by the canonical reduced interface.

The residual genuinely-missing content is the *inside-count* datum `(2)` (root-
count constancy on the active arc); it is isolated precisely in the `Standard…`
abbreviations near the end of this file.
-/

namespace CriticalMixedHRT

/-- **`circleParam` is surjective onto the unit circle.**

Every `z : ℂ` with `‖z‖ = 1` is `circleParam x = exp(2πi x)` for some real `x`
(take `x = arg z / (2π)`). -/
theorem circleParam_surjective_onto_unit_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ x : ℝ, circleParam x = z := by
  refine ⟨Complex.arg z / (2 * Real.pi), ?_⟩
  unfold circleParam
  have key := norm_mul_exp_arg_mul_I z
  rw [hz] at key
  push_cast at key ⊢
  have heq : (2 * (Real.pi : ℂ) * Complex.I * (Complex.arg z / (2 * Real.pi)))
      = (Complex.arg z : ℂ) * Complex.I := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [heq]
  simpa using key

/-- **Task C — no unit-circle roots on the zero-free active arc.**

If the fibre polynomial `fibrePoly coeffs t` is zero-free along the unit-circle
parametrisation `x ↦ circleParam x` — equivalently, the return multiplier is
zero-free along the fibre `t` — then `fibrePoly coeffs t` has no root on the unit
circle.  This is exactly the off-circle component `(1)` of `hroots_min`, derived
from the analytically natural zero-free hypothesis. -/
theorem return_multiplier_no_unit_circle_roots_on_active_arc
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (t : ℝ)
    (hzf : ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0) :
    ∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1 := by
  intro z hz hnorm
  obtain ⟨x, hx⟩ := circleParam_surjective_onto_unit_circle z hnorm
  have hroot : (fibrePoly coeffs t).eval z = 0 := (Polynomial.mem_roots'.mp hz).2
  rw [← hx] at hroot
  exact hzf x hroot

/-- **Inside + outside counts sum to the degree.**

When the leading coefficient is nonzero (degree `= d`) and there are no roots on
the unit circle, every root is strictly inside or strictly outside the unit
disk, so the inside and outside counts sum to `d`. -/
theorem fibrePoly_inside_add_outside
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (t : ℝ)
    (hlast : (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d) ≠ 0)
    (hoff : ∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) :
    ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card
      + ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = d := by
  have hcard : Multiset.card (fibrePoly coeffs t).roots = d := by
    unfold fibrePoly
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
        polyOfCoeffs_natDegree _ hlast]
  have hsplit := Multiset.filter_add_not (fun z => ‖z‖ < 1) (fibrePoly coeffs t).roots
  have hcongr : Multiset.filter (fun z => ¬ ‖z‖ < 1) (fibrePoly coeffs t).roots
      = Multiset.filter (fun z => 1 < ‖z‖) (fibrePoly coeffs t).roots := by
    apply Multiset.filter_congr
    intro z hz
    have hne : ‖z‖ ≠ 1 := hoff z hz
    rw [not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hne), le_of_lt⟩
  rw [hcongr] at hsplit
  have := congrArg Multiset.card hsplit
  rw [Multiset.card_add] at this
  omega

/-- **Outside count from inside count and the degree compatibility.**

Given no roots on the unit circle, the inside count `Mlau`, and the global numeric
compatibility `(mlau : ℤ) = d - Mlau`, the outside count equals `mlau`.  Thus the
outside-count datum `(3)` of `hroots_min` is redundant. -/
theorem fibrePoly_outside_count_of_inside_count
    {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (t : ℝ)
    (hlast : (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d) ≠ 0)
    (hoff : ∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1)
    (hin : Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau) :
    ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau := by
  have hsum := fibrePoly_inside_add_outside coeffs t hlast hoff
  have : (mlau : ℤ) = ((((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card : ℕ) : ℤ) := by
    rw [hmM, hin]
    have : (((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card : ℤ)
        + (((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card : ℤ) = (d : ℤ) := by
      exact_mod_cast hsum
    omega
  exact_mod_cast this.symm

/-- Bridge: the leading coefficient `evalLaurentCircle ad t` is the top fibre
coefficient `(fun j => evalLaurentCircle (coeffs j) t) (Fin.last d)`. -/
theorem fibre_last_coeff_eq
    {d : ℕ} (ad : LaurentPolynomial ℂ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad) (t : ℝ) :
    (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d) = evalLaurentCircle ad t := by
  simp only [Fin.last]
  rw [show (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1))
        = ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ from rfl, h_ad_coeff]

/-- **Per-fibre canonical reduced interface ⟹ `hroots_min`.**

From the canonical reduced interface at a fibre `t` — the zero-free condition
along the circle `(1')`, the inside count `(2)`, and the global numeric
compatibility `(mlau : ℤ) = d - Mlau` — we obtain the full minimal geometric data
`hroots_min` consumed by `RootDataAdapter.lean`.  The off-circle condition `(1)`
is produced by `return_multiplier_no_unit_circle_roots_on_active_arc` and the
outside count `(3)` by `fibrePoly_outside_count_of_inside_count`. -/
theorem return_multiplier_root_data_minimal_proved
    {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (t : ℝ) (had_t : evalLaurentCircle ad t ≠ 0)
    (hzf : ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hin : Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau) :
    (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
    Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
    ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau := by
  have hlast : (fun j => evalLaurentCircle (coeffs j) t) (Fin.last d) ≠ 0 := by
    rw [fibre_last_coeff_eq ad coeffs h_ad_coeff t]; exact had_t
  have hoff := return_multiplier_no_unit_circle_roots_on_active_arc coeffs t hzf
  exact ⟨hoff, hin,
    fibrePoly_outside_count_of_inside_count mlau Mlau coeffs t hlast hoff hin hmM⟩

/-- **Interval form — the canonical reduced interface implies `hroots_min`.**

The minimal interface `hroots_min` of `RootDataAdapter.lean` over a window
`(a,b)` follows from the strictly smaller canonical reduced interface: the
zero-free arc condition `(1')` and the inside count `(2)` per fibre, plus the
single global numeric compatibility `(mlau : ℤ) = d - Mlau`. -/
theorem hroots_min_proved
    {a b : ℝ} {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hmM : (mlau : ℤ) = (d : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hin : ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card) :
    ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau := by
  intro t ht had_t
  exact return_multiplier_root_data_minimal_proved mlau Mlau ad coeffs h_ad_coeff
    t had_t (hzf t ht had_t) (hin t ht had_t) hmM

/-- **Stage 6A → Stage 5 bridge driven by the canonical reduced interface.**

This is the strongest no-`sorry` Stage 6A bridge produced in this run.  Compared
with `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`, the minimal
geometric interface `hroots_min` is itself replaced by the strictly smaller
canonical reduced interface:

* `hzf` — the return multiplier is zero-free along the active arc
  (`(fibrePoly coeffs t).eval (circleParam x) ≠ 0`); this *replaces* the
  off-circle root condition and the outside count;
* `hin` — the inside-disk root count equals `Mlau`;
* `hmM` — the single global numeric compatibility `(mlau : ℤ) = d - Mlau`.

The off-circle condition, the outside count, the factorisation identity, the root
enumeration, and the periodic-logarithm input are all synthesised internally.
The remaining holonomy identification is the choice-free `hJholo`. -/
theorem normalized_return_cocycle_feeds_no_flat_band_root_data_closed
    (D : NormalizedReturnData)
    (DK : DenjoyKoksmaReturnData D.θ)
    (hq : Tendsto DK.q atTop atTop)
    {a₀ b₀ : ℝ}
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀))
    (hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0)
    (S : Set ℝ) (hSU : S ⊆ Set.Ioo a₀ b₀)
    (hSpos : 0 < MeasureTheory.volume S)
    (hSres : ∀ s ∈ S, H s ∈ resonanceGroupC DK.q)
    (E : Set ℝ) (hE : E.Finite)
    (J : ℝ → ℂ)
    (hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
        J s = H s * Complex.exp (-2 * π * Complex.I * (D.θ : ℂ) * (s : ℂ)))
    {dlau : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (had : ad ≠ 0)
    (coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (hmM : (mlau : ℤ) = (dlau : ℤ) - Mlau)
    (hzf : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0)
    (hin : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card)
    (hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
      ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
        J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)) :
    False := by
  have hroots_min := hroots_min_proved mlau Mlau ad coeffs h_ad_coeff hmM hzf hin
  exact normalized_return_cocycle_feeds_no_flat_band_root_data_minimal D DK hq H hH
    hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs h_ad_coeff
    hroots_min hJholo

/-!
## Task F — the exact residual root-data blockers

After the reductions above, the only genuinely-missing analytic input is the
*inside-disk root-count* datum on the active arc (Task D: root-count constancy).
We record the exact Lean types of the residual blockers as abbreviations, tied
directly to the fibre polynomial `fibrePoly coeffs t = ∑ⱼ C (coeffsⱼ(t)) Xʲ`.
-/

/-- **Residual blocker (Task C, fully discharged form).**

No unit-circle roots on the active arc.  This abbreviation is *provable* from the
zero-free hypothesis via `return_multiplier_no_unit_circle_roots_on_active_arc`;
it is recorded here as the exact statement that part `(1)` of `hroots_min`
requires. -/
def StandardNoUnitCircleRootsOnActiveArc
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ)
    (ad : LaurentPolynomial ℂ) : Prop :=
  ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
    ∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1

/-- **Residual blocker (Task D — genuinely missing).**

The inside-disk root count of the fibre polynomial is the constant `Mlau` on the
active arc.  This is the root-count-constancy content: on an open parameter arc
where no root crosses the unit circle, the number of roots inside the unit disk
is locally constant.  This is the *only* genuinely-missing datum of the root-data
interface after the reductions in this module. -/
def StandardRootCountConstancyOnActiveArc
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ)
    (ad : LaurentPolynomial ℂ) (Mlau : ℤ) : Prop :=
  ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
    Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card

/-- **Residual root-data, minimal assembled form.**

The complete canonical reduced root-data interface: zero-free active arc, inside
count, and the degree compatibility.  By `hroots_min_proved` this *implies* the
certificate's `hroots_min`, so it is the smallest exact root-data interface for
the return multiplier. -/
def StandardReturnMultiplierRootDataMinimal
    {d : ℕ} (coeffs : Fin (d + 1) → LaurentPolynomial ℂ) (a b : ℝ)
    (ad : LaurentPolynomial ℂ) (mlau : ℕ) (Mlau : ℤ) : Prop :=
  (mlau : ℤ) = (d : ℤ) - Mlau ∧
  (∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
    ∀ x : ℝ, (fibrePoly coeffs t).eval (circleParam x) ≠ 0) ∧
  StandardRootCountConstancyOnActiveArc coeffs a b ad Mlau

/-- The canonical reduced interface `StandardReturnMultiplierRootDataMinimal`
implies the certificate's minimal geometric data `hroots_min`. -/
theorem standardReturnMultiplierRootDataMinimal_implies_hroots_min
    {a b : ℝ} {d : ℕ} (mlau : ℕ) (Mlau : ℤ)
    (ad : LaurentPolynomial ℂ) (coeffs : Fin (d + 1) → LaurentPolynomial ℂ)
    (h_ad_coeff : coeffs ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = ad)
    (h : StandardReturnMultiplierRootDataMinimal coeffs a b ad mlau Mlau) :
    ∀ t ∈ Set.Ioo a b, evalLaurentCircle ad t ≠ 0 →
      (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
      Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
      ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau :=
  hroots_min_proved mlau Mlau ad coeffs h_ad_coeff h.1 h.2.1 h.2.2

end CriticalMixedHRT
