import Mathlib
import RequestProject.Zak.L2Zak
import RequestProject.Zak.PolyphaseUnitary
import RequestProject.HRT.ZakCovariance
import RequestProject.HRT.FiberOperator
import RequestProject.HRT.NormalizedReturnCocycle
import RequestProject.HRT.ReturnCocycleToNoFlatBand

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (Parts D & F) — from the four-term HRT relation to the normalized cocycle

This module performs the central Stage 6B reduction: applying the Zak transform
to a normalized four-term HRT relation
```
    c₀ f + c₁ π(λ₁) f + c₂ π(λ₂) f + c₃ π(a, p/m) f = 0
```
turns it into the **one-step Zak fibre equation**
```
    P(x,s) F(x,s) + c₃ e^{-2πi(p/m)x} F(x-a, s+p/m) = 0,
```
equivalently the solved form consumed by `NormalizedReturnData.hone`.  The result
is packaged as a `NormalizedReturnData` object (`hrt_relation_to_one_step_zak_equation`),
which is exactly the Stage 6A input.

Finally `zak_relation_feeds_normalized_no_flat_band` connects an original
normalized four-term HRT relation to the Stage 5 / Stage 6A no-flat-band
contradiction framework
(`normalized_return_cocycle_feeds_no_flat_band_synthesized`).
-/

namespace CriticalMixedHRT

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The Zak transform sends `0` to the zero fibre function. -/
theorem zak_zero (Z : L2ZakModel V) (x s : ℝ) : Z.Zak 0 x s = 0 := by
  have h := Z.Zak_smul 0 0 x s
  simpa using h

/-
**Part D — the one-step Zak fibre equation.**

Applying the Zak transform to the normalized four-term HRT relation
`c₀ f + c₁ π(λ₁) f + c₂ π(λ₂) f + c₃ π(a,p/m) f = 0` yields the solved one-step
fibre equation
`F(x-a, s+p/m) = -c₃⁻¹ e^{2πi(p/m)x} P(x,s) F(x,s)`,
where `F = Zak f` and `P` is the lattice trinomial `Pfun`.
-/
theorem zak_one_step_fiber_equation
    (Z : L2ZakModel V)
    (m : ℕ) (p : ℤ) (a : ℝ)
    (c₀ c₁ c₂ c₃ : ℂ) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ)
    (f : V)
    (hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    ∀ x s, Z.Zak f (x - a) (s + ((p : ℝ) / (m : ℝ))) =
      -c₃⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ((↑p / ↑m : ℂ)) * (↑x : ℂ))
        * Pfun c₀ c₁ c₂ r₁ t₁ r₂ t₂ x s * Z.Zak f x s := by
  intro x s;
  have h_eq : c₀ * Z.Zak f x s + c₁ * Complex.exp (-2 * Real.pi * Complex.I * ((t₁ * x + r₁ * s) : ℂ)) * Z.Zak f x s + c₂ * Complex.exp (-2 * Real.pi * Complex.I * ((t₂ * x + r₂ * s) : ℂ)) * Z.Zak f x s + c₃ * Complex.exp (-2 * Real.pi * Complex.I * ((p / m) : ℂ) * x) * Z.Zak f (x - a) (s + p / m) = 0 := by
    convert congr_arg ( fun f => Z.Zak f x s ) hrel using 1 ; simp +decide [ Z.Zak_add, Z.Zak_smul, Z.lattice_cov, Z.rogue_cov ] ; ring;
    exact Eq.symm ( zak_zero Z x s );
  unfold Pfun;
  field_simp;
  rw [ show ( 2 * Real.pi * I * p * x / m : ℂ ) = - ( -2 * Real.pi * I * ( p / m ) * x ) by ring ] ; rw [ Complex.exp_neg ] ; ring;
  field_simp;
  grind

/-- **Part D — construction of the Stage 6A `NormalizedReturnData`.**

From a normalized four-term HRT relation in the `L²` model `V`, together with the
arithmetic normalization data (`m > 0`, `p`, `a`, `Irrational (m·a)`), the four
nonzero coefficients and the unimodular ℤ²-basis, we construct the
`NormalizedReturnData` object that drives Stage 6A.  Its Zak fibre function is
`F = Zak f`, its frequency periodicity is the Zak quasiperiodicity
`Zak_periodic_s`, and its one-step fibre equation is
`zak_one_step_fiber_equation`. -/
noncomputable def hrt_relation_to_one_step_zak_equation
    (Z : L2ZakModel V)
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : V)
    (hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0) :
    NormalizedReturnData where
  m := m
  hm := hm
  p := p
  a := a
  θ := (m : ℝ) * a
  hθ_eq := rfl
  hθ_irr := hθ_irr
  c₀ := c₀
  c₁ := c₁
  c₂ := c₂
  c₃ := c₃
  hc₀ := hc₀
  hc₁ := hc₁
  hc₂ := hc₂
  hc₃ := hc₃
  r₁ := r₁
  t₁ := t₁
  r₂ := r₂
  t₂ := t₂
  unimodular := unimodular
  F := Z.Zak f
  hFper := Z.Zak_periodic_s f
  hone := zak_one_step_fiber_equation Z m p a c₀ c₁ c₂ c₃ hc₃ r₁ t₁ r₂ t₂ f hrel

/-- **Part F — original normalized HRT relation feeds the no-flat-band framework.**

An original nontrivial normalized four-term HRT relation in the `L²` model `V`
(supplied through the Zak interface `Z`), together with the full Stage 5 / Stage
6A active-fibre, analytic-rigidity, periodic-gauge and local-certificate input
data, produces the no-flat-band contradiction.

This is the Stage 6B endpoint: it constructs the Stage 6A
`NormalizedReturnData` from the relation (via
`hrt_relation_to_one_step_zak_equation`) and feeds it into
`normalized_return_cocycle_feeds_no_flat_band_synthesized`.  It does *not* prove
the global HRT theorem; it only connects the original relation to the
no-flat-band contradiction framework. -/
theorem zak_relation_feeds_normalized_no_flat_band
    (Z : L2ZakModel V)
    (m : ℕ) (hm : 0 < m) (p : ℤ) (a : ℝ)
    (hθ_irr : Irrational ((m : ℝ) * a))
    (c₀ c₁ c₂ c₃ : ℂ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0)
    (r₁ t₁ r₂ t₂ : ℤ) (unimodular : r₁ * t₂ - r₂ * t₁ = 1)
    (f : V)
    (hrel : c₀ • f + c₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) f
              + c₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) f
              + c₃ • Z.shift a ((p : ℝ) / (m : ℝ)) f = 0)
    (DK : DenjoyKoksmaReturnData ((m : ℝ) * a))
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
  normalized_return_cocycle_feeds_no_flat_band_synthesized
    (hrt_relation_to_one_step_zak_equation Z m hm p a hθ_irr c₀ c₁ c₂ c₃
      hc₀ hc₁ hc₂ hc₃ r₁ t₁ r₂ t₂ unimodular f hrel)
    DK hq H hH hHne S hSU hSpos hSres E hE J hJgauge mlau Mlau ad had coeffs
    h_ad_coeff hroots hJholo

end CriticalMixedHRT