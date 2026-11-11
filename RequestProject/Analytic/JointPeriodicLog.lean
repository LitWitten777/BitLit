import Mathlib

open scoped Classical BigOperators Real
open MeasureTheory Filter Topology Complex intervalIntegral

/-!
# Stage 4 — Joint analytic periodic logarithm on a zero-free cylinder

This file formalizes the analytic form of Lemma 7.1 (the "joint analytic
periodic logarithm") of the dossier.

We model the cylinder `U × Circle` as `ℝ × ℝ` with the second coordinate
carrying the circle structure encoded by `1`-periodicity, exactly as in the
rest of this project (where the period is taken to be `1`).  A map
`A : ℝ → ℝ → ℂ` is thought of as `A s x` with `s` the parameter and `x` the
circle variable.

Following the manuscript, instead of phrasing the hypothesis through Mathlib's
winding-number API we use its *analytic form of zero winding*:

```
    ∫₀¹ (∂ₓ A(s,x) / A(s,x)) dx = 0     for every s,
```

which is exactly what the HRT proof needs.  Under this hypothesis (plus
differentiability, continuity of the derivative, nonvanishing, and
`1`-periodicity in `x`), we construct a periodic logarithm

```
    ell(s,x) = Complex.log (A s 0) + ∫₀ˣ (∂ᵧ A(s,y) / A(s,y)) dy
```

and prove

* `Complex.exp (ell s x) = A s x`  (the logarithm property);
* `Function.Periodic (ell s) 1`     (periodicity in the circle variable);
* `HasDerivAt (ell s) (A' s x / A s x) x`  (the regularity needed downstream).

Finally we record the analytic regularity of the holonomy map
`H(s) = exp (∫₀¹ ell s x dx)` (deliverable 3), feeding the interface used by
`analytic_map_into_resonance_group_constant`.
-/

namespace CriticalMixedHRT

/-- The logarithmic-derivative integrand `y ↦ A'(s,y) / A(s,y)`. -/
noncomputable def logDerivIntegrand (A A' : ℝ → ℝ → ℂ) (s : ℝ) : ℝ → ℂ :=
  fun y => A' s y / A s y

/-- The explicit periodic logarithm
`ell(s,x) = log (A s 0) + ∫₀ˣ A'(s,y)/A(s,y) dy`. -/
noncomputable def jointPeriodicLog (A A' : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun s x => Complex.log (A s 0) + ∫ y in (0 : ℝ)..x, logDerivIntegrand A A' s y

/-- Continuity of `A s`, from differentiability. -/
theorem continuous_of_hasDerivAt
    (A A' : ℝ → ℝ → ℂ) (s : ℝ)
    (hderiv : ∀ x, HasDerivAt (A s) (A' s x) x) :
    Continuous (A s) :=
  continuous_iff_continuousAt.2 (fun x => (hderiv x).continuousAt)

/-- The integrand `y ↦ A'(s,y)/A(s,y)` is continuous. -/
theorem continuous_logDerivIntegrand
    (A A' : ℝ → ℝ → ℂ) (s : ℝ)
    (hderiv : ∀ x, HasDerivAt (A s) (A' s x) x)
    (hA'cont : Continuous (A' s))
    (hne : ∀ x, A s x ≠ 0) :
    Continuous (logDerivIntegrand A A' s) :=
  hA'cont.div (continuous_of_hasDerivAt A A' s hderiv) hne

/-- The derivative function `A' s` is `1`-periodic, derived from periodicity of
`A s` and uniqueness of derivatives. -/
theorem periodic_deriv
    (A A' : ℝ → ℝ → ℂ) (s : ℝ)
    (hderiv : ∀ x, HasDerivAt (A s) (A' s x) x)
    (hper : Function.Periodic (A s) 1) :
    Function.Periodic (A' s) 1 := by
  intro x
  have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 : ℝ)
  have h1 : HasDerivAt (fun y => A s (y + 1)) (A' s (x + 1)) x := by
    have := (hderiv (x + 1)).scomp x hinner
    simpa using this
  have h2 : HasDerivAt (fun y => A s (y + 1)) (A' s x) x := by
    refine (hderiv x).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun y => (hper y))
  exact (h1.unique h2)

/-- The integrand is `1`-periodic. -/
theorem periodic_logDerivIntegrand
    (A A' : ℝ → ℝ → ℂ) (s : ℝ)
    (hderiv : ∀ x, HasDerivAt (A s) (A' s x) x)
    (hper : Function.Periodic (A s) 1) :
    Function.Periodic (logDerivIntegrand A A' s) 1 := by
  intro y
  unfold logDerivIntegrand
  rw [periodic_deriv A A' s hderiv hper y, hper y]

/-- `HasDerivAt` for the explicit periodic logarithm. -/
theorem hasDerivAt_jointPeriodicLog
    (A A' : ℝ → ℝ → ℂ) (s : ℝ)
    (hderiv : ∀ x, HasDerivAt (A s) (A' s x) x)
    (hA'cont : Continuous (A' s))
    (hne : ∀ x, A s x ≠ 0)
    (x : ℝ) :
    HasDerivAt (jointPeriodicLog A A' s) (logDerivIntegrand A A' s x) x := by
  have hcont := continuous_logDerivIntegrand A A' s hderiv hA'cont hne
  have hFTC : HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, logDerivIntegrand A A' s y)
      (logDerivIntegrand A A' s x) x :=
    integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  unfold jointPeriodicLog
  exact hFTC.const_add (Complex.log (A s 0))

/-- **Stage 4 (joint analytic periodic logarithm; analytic zero-winding form).**

Let `A : ℝ → ℝ → ℂ` be differentiable in the circle variable with continuous
derivative `A'`, nonvanishing, and `1`-periodic in the circle variable.  Assume
the analytic zero-winding condition

```
    ∫₀¹ A'(s,x)/A(s,x) dx = 0   for every s.
```

Then there is `ell : ℝ → ℝ → ℂ` with `exp (ell s x) = A s x`, `ell s`
`1`-periodic, and `HasDerivAt (ell s) (A'(s,x)/A(s,x)) x`. -/
theorem analytic_zero_winding_log_on_cylinder
    (A A' : ℝ → ℝ → ℂ)
    (hderiv : ∀ s x, HasDerivAt (A s) (A' s x) x)
    (hA'cont : ∀ s, Continuous (A' s))
    (hne : ∀ s x, A s x ≠ 0)
    (hper : ∀ s, Function.Periodic (A s) 1)
    (hwind : ∀ s, ∫ x in (0 : ℝ)..1, A' s x / A s x = 0) :
    ∃ ell : ℝ → ℝ → ℂ,
      (∀ s x, Complex.exp (ell s x) = A s x) ∧
      (∀ s, Function.Periodic (ell s) 1) ∧
      (∀ s x, HasDerivAt (ell s) (A' s x / A s x) x) := by
  refine ⟨jointPeriodicLog A A', ?_, ?_, ?_⟩
  · -- exp (ell s x) = A s x
    intro s x
    set ell := jointPeriodicLog A A' s with hell
    have hd : ∀ x, HasDerivAt ell (logDerivIntegrand A A' s x) x :=
      hasDerivAt_jointPeriodicLog A A' s (hderiv s) (hA'cont s) (hne s)
    set q : ℝ → ℂ := fun x => Complex.exp (- ell x) * A s x with hq
    have hqderiv : ∀ x, HasDerivAt q 0 x := by
      intro x
      have h1 : HasDerivAt (fun y => Complex.exp (- ell y))
          (Complex.exp (- ell x) * (- logDerivIntegrand A A' s x)) x := by
        simpa using ((hd x).neg).cexp
      have hval : Complex.exp (- ell x) * (- logDerivIntegrand A A' s x) * A s x
            + Complex.exp (- ell x) * A' s x = 0 := by
        unfold logDerivIntegrand
        have hA := hne s x
        field_simp
        ring
      have h2 := h1.mul (hderiv s x)
      rw [hval] at h2
      simpa [hq] using h2
    have hqconst : ∀ y, q y = q 0 := fun y =>
      is_const_of_deriv_eq_zero (fun x => (hqderiv x).differentiableAt)
        (fun x => (hqderiv x).deriv) y 0
    have h0 : q 0 = 1 := by
      simp only [hq, hell, jointPeriodicLog, logDerivIntegrand,
        intervalIntegral.integral_same, add_zero]
      rw [Complex.exp_neg, Complex.exp_log (hne s 0)]
      exact inv_mul_cancel₀ (hne s 0)
    have key : Complex.exp (- ell x) * A s x = 1 := by
      have := (hqconst x).trans h0
      simpa [hq] using this
    have hAx : A s x = Complex.exp (ell x) := by
      have h2 : Complex.exp (ell x) * (Complex.exp (- ell x) * A s x)
          = Complex.exp (ell x) * 1 := by rw [key]
      rwa [mul_one, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
        Complex.exp_zero, one_mul] at h2
    exact hAx.symm
  · -- periodicity
    intro s x
    have hcont := continuous_logDerivIntegrand A A' s (hderiv s) (hA'cont s) (hne s)
    have hper' := periodic_logDerivIntegrand A A' s (hderiv s) (hper s)
    simp only [jointPeriodicLog]
    rw [add_right_inj]
    have hadj : (∫ y in (0:ℝ)..x, logDerivIntegrand A A' s y)
        + (∫ y in x..(x+1), logDerivIntegrand A A' s y)
        = ∫ y in (0:ℝ)..(x+1), logDerivIntegrand A A' s y :=
      integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)
    have hshift : (∫ y in x..(x+1), logDerivIntegrand A A' s y)
        = ∫ y in (0:ℝ)..(0+1), logDerivIntegrand A A' s y := by
      simpa using hper'.intervalIntegral_add_eq x 0
    have hzero : (∫ y in x..(x+1), logDerivIntegrand A A' s y) = 0 := by
      rw [hshift]
      simpa [logDerivIntegrand] using hwind s
    rw [← hadj, hzero, add_zero]
  · -- regularity
    intro s x
    simpa [logDerivIntegrand] using
      hasDerivAt_jointPeriodicLog A A' s (hderiv s) (hA'cont s) (hne s) x

/-- The holonomy map `H(s) = exp (∫₀¹ ell s x dx)` is nonvanishing. -/
theorem holonomy_ne_zero (ell : ℝ → ℝ → ℂ) (s : ℝ) :
    Complex.exp (∫ x in (0 : ℝ)..1, ell s x) ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Deliverable 3 — analytic regularity of the holonomy map.**

If the parameter integral `s ↦ ∫₀¹ ell s x dx` is real analytic on `U`, then the
holonomy map `H(s) = exp (∫₀¹ ell s x dx)` is real analytic and nonvanishing on
`U`, which is exactly the interface required by
`analytic_map_into_resonance_group_constant`. -/
theorem holonomy_analytic_of_integral_analytic
    (U : Set ℝ) (ell : ℝ → ℝ → ℂ)
    (hI : AnalyticOnNhd ℝ (fun s => ∫ x in (0 : ℝ)..1, ell s x) U) :
    AnalyticOnNhd ℝ (fun s => Complex.exp (∫ x in (0 : ℝ)..1, ell s x)) U
      ∧ (∀ s, Complex.exp (∫ x in (0 : ℝ)..1, ell s x) ≠ 0) := by
  refine ⟨?_, fun s => Complex.exp_ne_zero _⟩
  have he : ∀ z : ℂ, AnalyticAt ℝ Complex.exp z :=
    fun z => (analyticAt_cexp (z := z)).restrictScalars
  exact fun s hs => (he _).comp (hI s hs)

end CriticalMixedHRT
