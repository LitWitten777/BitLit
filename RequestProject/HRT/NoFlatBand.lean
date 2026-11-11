import Mathlib
import RequestProject.AnalyticRigidity
import RequestProject.NoLaurentObstruction
import RequestProject.Analytic.JointPeriodicLog
import RequestProject.Rotation.DenjoyKoksmaInterface
import RequestProject.Rotation.C1UniformReturnSums
import RequestProject.Rotation.HolonomyQuantizationPeriodic
import RequestProject.Rotation.MeasurableWinding

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

/-!
# Stage 5 — the no-flat-band theorem (conditional form)

This module assembles the previously certified stages into the **no-flat-band
theorem** that drives the contradiction in the critical mixed-arithmetic
four-point HRT argument.

The geometric picture is the following.  After the `SL(2,ℤ)` normal form and the
finite Zak iteration, a hypothetical four-point dependence produces, on an active
parameter arc `U`, a zero-free jointly analytic cocycle family `A : U × Circle →
ℂ` (encoded here, as throughout the project, with the circle variable carried by
`1`-periodicity) together with, for a positive-measure set of parameters
`s ∈ U`, a nonzero periodic `L²` window `h_s` satisfying the fiber cocycle

```
    h_s(x - θ) = A(s,x) h_s(x).
```

Running the already-certified measurable-winding (`MeasurableWinding`), periodic
logarithm (`JointPeriodicLog`), holonomy-quantization / resonance-membership
(`HolonomyQuantizationPeriodic`) and analytic-rigidity (`AnalyticRigidity`)
stages, the holonomy

```
    H(s) = exp (∫₀¹ ell_s(x) dx)
```

lies in the Haar-null resonance group `resonanceGroupC D.q` for every active `s`.
Since the active set has positive measure and `H` is analytic, the analytic
rigidity theorem `analytic_map_into_resonance_group_constant` forces `H` to be
**constant** on `U` — this is `constant_holonomy_of_active_fibers` below
(deliverable 2).

Undoing the periodic Zak gauge turns the constant holonomy into the exact
irrational-character holonomy law `J(e^{2πis}) = C·e^{-2πiθs}`.  Feeding this to
the (imported) local Laurent holonomy certificate
`local_holonomy_certificate_full_periodic_log_form` produces a nontrivial Laurent
relation `∑ᵣ Aᵣ(w) J(w)ʳ = 0`; the already-certified no-Laurent
irrational-character obstruction
(`no_laurent_irrational_character_obstruction`) then forces every `Aᵣ` to vanish,
contradicting their nontriviality.  This contradiction is
`no_flat_band_of_laurent_holonomy_certificate` and its active-fiber wrapper
`no_flat_band_of_active_fibers_and_certificate` below (deliverable 3).

As the local Laurent certificate package is **not** present in the active
archive, it is *not* introduced as an axiom.  Instead, following the task's
fallback policy, its conclusion (the existence of nontrivial Laurent polynomials
satisfying the holonomy relation) is carried as an explicit hypothesis, and the
strongest theorem provable from the certified stages is stated in that
conditional form.
-/

namespace CriticalMixedHRT

/-- **Active-fiber resonance membership.**

If for every parameter `s` in an active set there is a nonzero periodic `L²`
window `h` and a periodic logarithm `ell` of the cocycle `b` realising
`H s = exp (∫₀¹ ell)`, then — by the certified holonomy-quantization and
resonance-membership stage — `H s` lies in the resonance group
`resonanceGroupC D.q`.

This is the bridge from the per-fiber cocycle data to the positive-measure
resonance hypothesis consumed by `constant_holonomy_of_active_fibers`. -/
theorem active_fibers_resonant
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (H : ℝ → ℂ) (Active : Set ℝ)
    (hfiber : ∀ s ∈ Active, ∃ h b ell : ℝ → ℂ,
        Measurable h ∧ Function.Periodic h 1 ∧
        Measurable ell ∧ Function.Periodic ell 1 ∧
        Integrable ell (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        MemLp h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        eLpNorm h 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0 ∧
        (∀ x, h (x - θ) = b x * h x) ∧
        (∀ x, Complex.exp (ell x) = b x) ∧
        TrigApproxInVariation D
          (fun x => ell x - ∫ y in Set.Ioc (0 : ℝ) 1, ell y) ∧
        H s = Complex.exp (∫ y in Set.Ioc (0 : ℝ) 1, ell y)) :
    ∀ s ∈ Active, H s ∈ resonanceGroupC D.q := by
  intro s hs
  obtain ⟨h, b, ell, hh_meas, hh_per, hell_meas, hell_per, hell_int, hmem, hpos,
    hcocycle, hlog, happrox, hHs⟩ := hfiber s hs
  rw [hHs]
  exact measurable_cocycle_holonomy_resonant_periodic hθ D h b ell hh_meas hh_per
    hell_meas hell_per hell_int hmem hpos hcocycle hlog happrox

/-- **Deliverable 2 — constant holonomy from positive-measure active fibers.**

Let `U ⊆ ℝ` be a connected open parameter arc and `H : U → ℂ` a zero-free
real-analytic holonomy function.  If `H` takes values in the Haar-null resonance
group `resonanceGroupC D.q` on a positive-measure active set `Active ⊆ U`, then
`H` is constant on `U`.

This is the analytic-rigidity assembly: by the certified
`analytic_map_into_resonance_group_constant`, a real-analytic map landing in the
resonance group on a set of positive measure must be constant. -/
theorem constant_holonomy_of_active_fibers
    {θ : ℝ} (D : DenjoyKoksmaReturnData θ)
    (hq : Tendsto D.q atTop atTop)
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U) (hHne : ∀ s ∈ U, H s ≠ 0)
    (Active : Set ℝ) (hActiveU : Active ⊆ U)
    (hActivePos : 0 < volume Active)
    (hActiveRes : ∀ s ∈ Active, H s ∈ resonanceGroupC D.q) :
    ∀ s ∈ U, ∀ t ∈ U, H s = H t := by
  apply analytic_map_into_resonance_group_constant D.q hq U hU hUc H hH hHne
  refine lt_of_lt_of_le hActivePos (measure_mono ?_)
  intro s hs
  exact ⟨hActiveU hs, hActiveRes s hs⟩

/-- **Deliverable 3 (core) — no flat band from the Laurent holonomy certificate.**

Given the exact irrational-character holonomy law
`J(s) = C·e^{-2πiθs}` on a nonempty arc `Ioo a b` (the output of undoing the
periodic Zak gauge once the holonomy is constant), together with the *conclusion*
of the local Laurent holonomy certificate — nontrivial Laurent polynomials
`Acoef 0,…,Acoef Dlau` satisfying `∑ᵣ Acoef_r(e^{2πis}) J(s)ʳ = 0` on the arc —
the certified no-Laurent irrational-character obstruction
(`no_laurent_irrational_character_obstruction`) forces every `Acoef_r` to vanish,
contradicting their nontriviality.

The local Laurent certificate package being absent from the archive, its output
is carried here as the explicit hypotheses `hcert` and `hA_ne` rather than as an
axiom. -/
theorem no_flat_band_of_laurent_holonomy_certificate
    (θ : ℝ) (hθ : Irrational θ) (Cc : ℂ) (hC : Cc ≠ 0)
    {a b : ℝ} (hab : a < b)
    (J : ℝ → ℂ)
    (hlaw : ∀ s ∈ Set.Ioo a b,
        J s = Cc * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)))
    (Dlau : ℕ) (Acoef : ℕ → (ℤ →₀ ℂ))
    (hA_ne : ∃ r ∈ Finset.range (Dlau + 1), Acoef r ≠ 0)
    (hcert : ∀ s ∈ Set.Ioo a b,
        ∑ r ∈ Finset.range (Dlau + 1), evalChar (Acoef r) s * (J s) ^ r = 0) :
    False := by
  obtain ⟨r₀, hr₀, hr₀ne⟩ := hA_ne
  have hcert' : ∀ s ∈ Set.Ioo a b,
      ∑ r ∈ Finset.range (Dlau + 1),
        evalChar (Acoef r) s
          * (Cc * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ))) ^ r = 0 := by
    intro s hs
    have := hcert s hs
    rwa [hlaw s hs] at this
  exact hr₀ne
    (no_laurent_irrational_character_obstruction θ hθ Cc hC Dlau Acoef hab hcert' r₀ hr₀)

/-- **Deliverable 3 (assembly) — the conditional no-flat-band theorem.**

Combining the constant-holonomy theorem with the exact holonomy law and the
local Laurent certificate interface: a positive-measure family of active fibers
landing in the resonance group, an analytic zero-free holonomy `H`, the gauge
identification `J s = H s · e^{-2πiθs}`, and the (conditional) Laurent
certificate together produce a contradiction.  Hence no such flat band of active
fibers can exist.

`constant_holonomy_of_active_fibers` makes `H` constant, the gauge then yields the
exact irrational-character law, and `no_flat_band_of_laurent_holonomy_certificate`
delivers the contradiction. -/
theorem no_flat_band_of_active_fibers_and_certificate
    {θ : ℝ} (hθ : Irrational θ) (D : DenjoyKoksmaReturnData θ)
    (hq : Tendsto D.q atTop atTop)
    (U : Set ℝ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (H : ℝ → ℂ) (hH : AnalyticOnNhd ℝ H U) (hHne : ∀ s ∈ U, H s ≠ 0)
    (Active : Set ℝ) (hActiveU : Active ⊆ U)
    (hActivePos : 0 < volume Active)
    (hActiveRes : ∀ s ∈ Active, H s ∈ resonanceGroupC D.q)
    {a b : ℝ} (hab : a < b) (hsub : Set.Ioo a b ⊆ U)
    (J : ℝ → ℂ)
    (hJ : ∀ s ∈ Set.Ioo a b,
        J s = H s * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)))
    (Dlau : ℕ) (Acoef : ℕ → (ℤ →₀ ℂ))
    (hA_ne : ∃ r ∈ Finset.range (Dlau + 1), Acoef r ≠ 0)
    (hcert : ∀ s ∈ Set.Ioo a b,
        ∑ r ∈ Finset.range (Dlau + 1), evalChar (Acoef r) s * (J s) ^ r = 0) :
    False := by
  -- Constant holonomy from the active fibers.
  have hconst := constant_holonomy_of_active_fibers D hq U hU hUc H hH hHne
    Active hActiveU hActivePos hActiveRes
  -- Fix the constant value `C = H s₀` at a point of the arc.
  obtain ⟨s₀, hs₀⟩ : (Set.Ioo a b).Nonempty := ⟨(a + b) / 2, by constructor <;> linarith⟩
  have hCne : H s₀ ≠ 0 := hHne s₀ (hsub hs₀)
  -- The exact irrational-character holonomy law.
  have hlaw : ∀ s ∈ Set.Ioo a b,
      J s = H s₀ * Complex.exp (-2 * π * Complex.I * (θ : ℂ) * (s : ℂ)) := by
    intro s hs
    rw [hJ s hs, hconst s (hsub hs) s₀ (hsub hs₀)]
  exact no_flat_band_of_laurent_holonomy_certificate θ hθ (H s₀) hCne hab J hlaw
    Dlau Acoef hA_ne hcert

end CriticalMixedHRT
