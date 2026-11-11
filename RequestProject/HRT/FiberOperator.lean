import Mathlib
import RequestProject.Zak.L2Zak
import RequestProject.Zak.PolyphaseUnitary

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B (Part E) — the active fibre set and its positivity

The *fibre density* of a Zak transform `F` is `s ↦ ∫₀¹ ‖F(x,s)‖² dx`, and the
**active set** is the set of frequencies whose fibre carries positive `L²`-mass:
`S = {s : ∫₀¹ ‖F(x,s)‖² dx > 0}`.

Through the polyphase gauge `K_s(x) = e^{-2πi s x} F(x,s)`, this is the same as
the dossier's `S = {s : ∫₀¹ |K_s(x)|² dx > 0}` (see `fiberDensity_zakGauge`).

The main result `active_set_positive_measure_of_nonzero_window` shows that, for a
nonzero window `f`, the active set has positive measure.  Its mathematical
content is exactly the Plancherel identity of the interface
(`L2ZakModel.norm_sq_integral`): the total fibre mass equals `‖f‖² > 0`, so the
nonnegative density cannot vanish almost everywhere.  Following the task's
fallback policy, the *interval-integrability* of the fibre density (a regularity
fact about the concrete Zak transform, not available from the abstract
interface) is supplied as an explicit hypothesis rather than postulated.
-/

namespace CriticalMixedHRT

/-- Fibre `L²`-density `s ↦ ∫₀¹ ‖F(x,s)‖² dx`. -/
noncomputable def fiberDensity (F : ℝ → ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, ‖F x s‖ ^ 2

/-- The active fibre set `S = {s : ∫₀¹ ‖F(x,s)‖² dx > 0}`. -/
def activeSet (F : ℝ → ℝ → ℂ) : Set ℝ := {s | 0 < fiberDensity F s}

/-- The fibre density is the same whether computed through the periodic gauge
`K_s` or the raw Zak transform `F`: `∫₀¹ ‖K_s(x)‖² dx = ∫₀¹ ‖F(x,s)‖² dx`. -/
theorem fiberDensity_zakGauge (F : ℝ → ℝ → ℂ) (s : ℝ) :
    (∫ x in (0:ℝ)..1, ‖zakGauge F s x‖ ^ 2) = fiberDensity F s :=
  integral_norm_sq_zakGauge F s

/-- The fibre density is nonnegative. -/
theorem fiberDensity_nonneg (F : ℝ → ℝ → ℂ) (s : ℝ) : 0 ≤ fiberDensity F s := by
  unfold fiberDensity
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _
  positivity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Part E — active-set positivity.**

For a nonzero window `f`, the active fibre set has positive Lebesgue measure.
The total fibre mass is `∫₀¹ (fibre density) ds = ‖f‖² > 0` by the interface
Plancherel identity; since the density is nonnegative, the set on which it is
positive cannot be null.

The interval-integrability hypothesis `hint` is the only regularity input; it is
a property of the concrete Zak transform (documented Fubini/Zak-unitarity
obligation) and is taken as an explicit hypothesis, never an axiom. -/
theorem active_set_positive_measure_of_nonzero_window
    (Z : L2ZakModel V) (f : V) (hf : f ≠ 0)
    (hint : IntervalIntegrable (fiberDensity (Z.Zak f)) volume 0 1) :
    0 < MeasureTheory.volume (activeSet (Z.Zak f) ∩ Set.Ioc (0:ℝ) 1) := by
  set g := fiberDensity (Z.Zak f) with hg
  have hgnn : ∀ s, 0 ≤ g s := fun s => fiberDensity_nonneg (Z.Zak f) s
  have htot : (∫ s in (0:ℝ)..1, g s) = ‖f‖ ^ 2 := Z.norm_sq_integral f
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hpos : 0 < ‖f‖ ^ 2 := by positivity
  have hI : 0 < ∫ s in (0:ℝ)..1, g s := by rw [htot]; exact hpos
  obtain ⟨_, hsupp⟩ :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ hgnn) hint).mp hI
  have hset : activeSet (Z.Zak f) = Function.support g :=
    Set.ext fun s => ⟨fun h => h.ne', fun h => (hgnn s).lt_of_ne (Ne.symm h)⟩
  rw [hset]
  exact hsupp

end CriticalMixedHRT
