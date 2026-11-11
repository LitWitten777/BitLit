import Mathlib
import RequestProject.Zak.ZakTargetSpace
import RequestProject.Zak.ConcreteZakDenseSubspace

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex

set_option maxHeartbeats 1000000

/-!
# Stage 6B — the concrete a.e.-level `L²(ℝ)` Zak model (TASKs C/D)

This module assembles the honest a.e.-level Zak model `L2ZakModelAE` on the
concrete Hilbert space `L²(ℝ) = Lp ℂ 2 volume` out of:

* the concrete dense test subspace `concreteZakDenseSubspace` and its density
  `concreteZakDenseSubspace_dense` (TASK B), and
* the general dense-data reduction `l2ZakModelAE_of_dense_data` (proved in
  `ZakTargetSpace.lean`).

The target space is the genuine `L²([0,1]²)` quotient `ZakTarget` (a complete
inner-product space).

The remaining concrete input — the densely-defined Zak isometry on
`concreteZakDenseSubspace` valued in `ZakTarget`, together with the
time-frequency shift operators and the lattice/rogue covariance identities
witnessed on the dense class — is packaged as the structure
`ConcreteZakDenseData`.  Producing such a term is exactly the standard
`L²(ℝ)` Zak-to-`L²([0,1]²)` isometric-lift theorem; it is isolated (NOT as an
axiom) as the precisely-typed proposition `StandardConcreteZakToLpTheorem`.

Given that data, `concrete_L2ZakModelAE_of_data` produces a genuine
`L2ZakModelAE (Lp ℂ 2 volume) ZakTarget` with **no** `sorry` and **no** axiom:
the Plancherel/unitary identity is automatic (the model's Zak transform is a
linear isometry) and the covariance identities are propagated from the dense
class to all of `L²(ℝ)` by `operator_intertwining_extends_from_dense`.
-/

namespace CriticalMixedHRT

/-- The concrete `L²([0,1]²)` target measure: Lebesgue measure restricted to the
unit square. -/
noncomputable def zakSquareMeasure : Measure (ℝ × ℝ) :=
  (volume).restrict (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1)

/-- The concrete a.e.-level Zak target space `L²([0,1]²)`. -/
abbrev ZakTarget : Type := Lp ℂ 2 zakSquareMeasure

/-- **The concrete dense Zak isometry data on `L²(ℝ)`.**

This bundles exactly the hypotheses consumed by `l2ZakModelAE_of_dense_data`,
specialized to `V = Lp ℂ 2 volume` with the concrete dense test subspace
`concreteZakDenseSubspace` and the concrete `L²([0,1]²)` target `ZakTarget`:

* `T₀` — the Zak transform as a densely-defined linear isometry on the test
  class (Plancherel built in);
* `shift` — the time-frequency shift operators on `L²(ℝ)`;
* `charLattice`/`charRogue` — the lattice/rogue modulation operators on the
  target;
* `hshiftD` — the test class is closed under the shift;
* `hlat`/`hrog` — the lattice/rogue covariance identities on the test class. -/
structure ConcreteZakDenseData where
  /-- The densely-defined Zak transform as a linear isometry on the test class. -/
  T₀ : concreteZakDenseSubspace →ₗᵢ[ℂ] ZakTarget
  /-- The time-frequency shift operators on `L²(ℝ)`. -/
  shift : ℝ → ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
  /-- Lattice modulation operators on the target. -/
  charLattice : ℤ → ℤ → (ZakTarget →L[ℂ] ZakTarget)
  /-- Rogue (real) modulation operators on the target. -/
  charRogue : ℝ → ℝ → (ZakTarget →L[ℂ] ZakTarget)
  /-- The test class is closed under the time-frequency shift. -/
  hshiftD : ∀ (a b : ℝ) (d : concreteZakDenseSubspace),
    shift a b (d : Lp ℂ 2 (volume : Measure ℝ)) ∈ concreteZakDenseSubspace
  /-- Integer lattice covariance on the test class. -/
  hlat : ∀ (m n : ℤ) (d : concreteZakDenseSubspace),
    T₀ ⟨shift (m : ℝ) (n : ℝ) (d : Lp ℂ 2 (volume : Measure ℝ)), hshiftD _ _ d⟩
      = charLattice m n (T₀ d)
  /-- Rogue (real) covariance on the test class. -/
  hrog : ∀ (a b : ℝ) (d : concreteZakDenseSubspace),
    T₀ ⟨shift a b (d : Lp ℂ 2 (volume : Measure ℝ)), hshiftD a b d⟩
      = charRogue a b (T₀ d)

/-- **TASK D — assembling the concrete a.e. Zak model from the dense data.**

Given the concrete dense Zak isometry data, the general dense-extension reduction
`l2ZakModelAE_of_dense_data` produces a genuine a.e.-level Zak model
`L2ZakModelAE (Lp ℂ 2 volume) ZakTarget`.  No `sorry`, no axiom. -/
theorem concrete_L2ZakModelAE_of_data (data : ConcreteZakDenseData) :
    Nonempty (L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget) :=
  l2ZakModelAE_of_dense_data concreteZakDenseSubspace concreteZakDenseSubspace_dense
    data.T₀ data.shift data.charLattice data.charRogue data.hshiftD data.hlat data.hrog

/-- **The isolated remaining concrete-lift obligation (TASK C).**

The single fact still required to construct the concrete a.e. Zak model: the
existence of the concrete dense Zak isometry data, i.e. the standard isometric
lift of the densely-defined classical Zak transform `concreteZakDense` (on
continuous compactly supported windows) into the `L²([0,1]²)` quotient
`ZakTarget`, with its time-frequency covariance.  This is *not* an axiom; it is a
precisely-typed proposition recording the remaining gap, reduced from the
previous run's `StandardL2ZakModelTheorem`. -/
def StandardConcreteZakToLpTheorem : Prop := Nonempty ConcreteZakDenseData

/-- **TASK D — the concrete a.e. Zak model, conditional on the isolated lift.**

Given `StandardConcreteZakToLpTheorem`, the concrete a.e.-level Zak model on
`L²(ℝ)` (valued in `L²([0,1]²)`) exists. -/
theorem concrete_L2ZakModelAE_nonempty (h : StandardConcreteZakToLpTheorem) :
    Nonempty (L2ZakModelAE (Lp ℂ 2 (volume : Measure ℝ)) ZakTarget) :=
  h.elim fun data => concrete_L2ZakModelAE_of_data data

end CriticalMixedHRT
