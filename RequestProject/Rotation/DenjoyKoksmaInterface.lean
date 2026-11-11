import Mathlib
import RequestProject.Rotation.ReturnData
import RequestProject.Rotation.FourierReturnSums

open scoped Classical BigOperators Real
open Filter Topology

/-!
# The Denjoy–Koksma return-data interface (Stage 2B)

The Denjoy–Koksma inequality states that for an irrational rotation by `θ` with
continued-fraction denominators `qₙ`, and for any function `g` of bounded
variation with `∫ g = 0`, the Birkhoff sums over a full return period are
controlled by the variation:
```
  sup_x | ∑_{j<qₙ} g(x - jθ) | ≤ Var(g).
```

A full proof from continued fractions is not currently available in Mathlib, so
in this stage we **record exactly this estimate as a conditional interface**.
Downstream theorems are conditional on having such data, exactly as the
finite Fourier-mode return sums of Stage 2A are conditional on
`RotationReturnData`.

The interface bundles, in addition to the rotation return data:

* an abstract *bounded variation* predicate `HasBV`;
* an abstract *variation* functional `variation`;
* an abstract *mean* (period integral) functional `mean`;
* the Denjoy–Koksma bound itself, as data.

We deliberately keep the analytic notions abstract (as fields) rather than
committing to a specific — and currently weak — Mathlib bounded-variation API.
This is sound: no axioms are introduced; the bound is recorded as a hypothesis
carried by the structure, to be supplied (or proved) by a later module.

The bound is stated pointwise in `x` (`∀ x, ‖·‖ ≤ variation g`), which is the
same content as the supremum statement `sup_x ‖·‖ ≤ variation g`, but avoids any
dependence on a particular `supNorm` definition.
-/

namespace CriticalMixedHRT

/-- **Denjoy–Koksma return data** for the rotation by `θ`.

Extends `RotationReturnData θ` (the return-time sequence `(qₙ, pₙ)`) with the
analytic data needed to state the Denjoy–Koksma estimate: a bounded-variation
predicate, a variation functional, a mean (period-integral) functional, and the
Denjoy–Koksma bound itself.

The Denjoy–Koksma bound is carried as a field (`dk_bound`): for every `g` of
bounded variation with zero mean, every full-period return sum
`∑_{j<qₙ} g(x - jθ)` is bounded in norm by `variation g`, uniformly in `x`. -/
structure DenjoyKoksmaReturnData (θ : ℝ) extends RotationReturnData θ where
  /-- An abstract *bounded variation* predicate on functions `ℝ → ℂ`. -/
  HasBV : (ℝ → ℂ) → Prop
  /-- An abstract *total variation* functional. -/
  variation : (ℝ → ℂ) → ℝ
  /-- An abstract *mean* (period integral) functional. -/
  mean : (ℝ → ℂ) → ℂ
  /-- The **Denjoy–Koksma bound**: for any bounded-variation, zero-mean `g`,
  every full-period return sum is bounded in norm by `variation g`,
  uniformly in `x`. -/
  dk_bound :
    ∀ g : ℝ → ℂ, HasBV g → mean g = 0 →
      ∀ (n : ℕ) (x : ℝ),
        ‖∑ j ∈ Finset.range (q n), g (x - (j : ℝ) * θ)‖ ≤ variation g

end CriticalMixedHRT
