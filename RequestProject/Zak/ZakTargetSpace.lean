import Mathlib
import RequestProject.Zak.IsometryExtension

open scoped Classical BigOperators
open MeasureTheory

set_option maxHeartbeats 1000000

/-!
# An honest a.e.-level `L²` Zak model and the dense-data reduction

The pointwise `L2ZakModel` (`RequestProject/Zak/L2Zak.lean`) demands its
additivity, quasiperiodicity and time-frequency covariance fields to hold
*pointwise for every `x s : ℝ` and every `f : V`*.  For a genuine `L²(ℝ)`
class `f` the Zak transform `∑' k, f(x+k) e^{-2πiks}` only converges a.e. on
fibres, and any map out of an `Lp` quotient that is pointwise-everywhere additive
must be built from a *linear section* of the quotient `{functions} ↠ L²`, which
cannot simultaneously intertwine the (uncountable family of) modulation
characters appearing in the covariance fields.  Hence the pointwise interface is
**too strong** to populate honestly from `L²` quotient data (documented in
`L2_ZAK_COMPLETION_STATUS.md`).

This module records the *honest* replacement: an a.e.-level model in which the
Zak transform is a genuine **linear isometry** `V →ₗᵢ[ℂ] W` into an abstract
complete `L²`-target `W` (the `L²([0,1]²)` stand-in), and the covariance
identities are equalities of `L²` classes.  In this formulation the Plancherel /
unitary identity is exactly the isometry property (`‖Zak f‖ = ‖f‖`), which is the
faithful `L²` content of the pointwise `norm_sq_integral` field.

The main results are the **dense-extension reductions** (`TASK D`/`TASK E`): a
densely-defined isometric Zak transform, together with covariance witnessed only
on the dense class, extends to a full a.e.-level model.  These are proved
unconditionally from the abstract extension tool
`linear_isometry_extends_from_dense_subspace`.
-/

namespace CriticalMixedHRT

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-
**Operator intertwining extends from a dense subspace.**

If a linear isometry `T : V →ₗᵢ[ℂ] W` intertwines the bounded operators `A` (on
`V`) and `B` (on `W`) on a dense subspace `D`, then it intertwines them
everywhere.  This is the abstract engine behind extending the dense Zak
covariance identities (lattice / rogue covariance) to the full `L²` transform.
-/
omit [CompleteSpace W] in
theorem operator_intertwining_extends_from_dense
    (D : Submodule ℂ V) (hD : Dense (D : Set V))
    (T : V →ₗᵢ[ℂ] W) (A : V →L[ℂ] V) (B : W →L[ℂ] W)
    (h : ∀ d : D, T (A d) = B (T d)) :
    ∀ v : V, T (A v) = B (T v) := by
  intro v;
  -- By the density of $D$, there exists a sequence $\{d_n\}$ in $D$ such that $d_n \to v$.
  obtain ⟨d_n, hd_n⟩ : ∃ d_n : ℕ → D, Filter.Tendsto (fun n => d_n n : ℕ → V) Filter.atTop (nhds v) := by
    exact mem_closure_iff_seq_limit.mp ( hD v ) |> fun ⟨ d_n, hd_n ⟩ => ⟨ fun n => ⟨ d_n n, hd_n.1 n ⟩, hd_n.2 ⟩;
  exact tendsto_nhds_unique ( T.continuous.continuousAt.tendsto.comp ( A.continuous.continuousAt.tendsto.comp hd_n ) ) ( B.continuous.continuousAt.tendsto.comp ( T.continuous.continuousAt.tendsto.comp hd_n ) |> Filter.Tendsto.congr ( by aesop ) )

/-- **The honest a.e.-level `L²` Zak model.**

A genuine `L²`-level Zak interface on `V` with values in a complete `L²`-target
`W`.  Unlike the pointwise `L2ZakModel`, the Zak transform is packaged as a
**linear isometry** (so the Plancherel/unitary identity `‖Zak f‖ = ‖f‖` holds by
construction) and the time-frequency covariance identities are equalities in the
`L²` target `W`, realized through bounded modulation operators
`charLattice`/`charRogue` and the time-frequency shift operators `shift` on `V`.

This is the faithful a.e. replacement for the (too strong) pointwise model. -/
structure L2ZakModelAE (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] where
  /-- The Zak transform as a genuine `L²` isometry (Plancherel built in). -/
  Zak : V →ₗᵢ[ℂ] W
  /-- The time-frequency shift operators on `V`. -/
  shift : ℝ → ℝ → (V →L[ℂ] V)
  /-- Modulation by the integer-lattice characters on the `L²` target. -/
  charLattice : ℤ → ℤ → (W →L[ℂ] W)
  /-- Modulation by the rogue (real) characters on the `L²` target. -/
  charRogue : ℝ → ℝ → (W →L[ℂ] W)
  /-- Integer lattice covariance, as an `L²` equality. -/
  lattice_cov : ∀ (m n : ℤ) (v : V),
    Zak (shift (m : ℝ) (n : ℝ) v) = charLattice m n (Zak v)
  /-- Rogue (real) covariance, as an `L²` equality. -/
  rogue_cov : ∀ (a b : ℝ) (v : V),
    Zak (shift a b v) = charRogue a b (Zak v)

/-
**TASK D / TASK E (abstract form): dense-data reduction to an a.e. model.**

Given a dense subspace `D` of `V`, a densely-defined Zak isometry `T₀ : D →ₗᵢ W`,
families of time-frequency shift operators on `V` and modulation operators on the
target, and the lattice/rogue covariance identities *witnessed only on the dense
class `D`*, there is a full `L2ZakModelAE V W` whose isometry extends `T₀`.

The Plancherel identity is automatic (the extension is a linear isometry); the
covariance identities are propagated from `D` to all of `V` by
`operator_intertwining_extends_from_dense`.
-/
theorem l2ZakModelAE_of_dense_data
    (D : Submodule ℂ V) (hD : Dense (D : Set V))
    (T₀ : D →ₗᵢ[ℂ] W)
    (shift : ℝ → ℝ → (V →L[ℂ] V))
    (charLattice : ℤ → ℤ → (W →L[ℂ] W))
    (charRogue : ℝ → ℝ → (W →L[ℂ] W))
    (hshiftD : ∀ (a b : ℝ) (d : D), shift a b (d : V) ∈ D)
    (hlat : ∀ (m n : ℤ) (d : D),
      T₀ ⟨shift (m : ℝ) (n : ℝ) (d : V), hshiftD _ _ d⟩ = charLattice m n (T₀ d))
    (hrog : ∀ (a b : ℝ) (d : D),
      T₀ ⟨shift a b (d : V), hshiftD a b d⟩ = charRogue a b (T₀ d)) :
    Nonempty (L2ZakModelAE V W) := by
  -- First obtain the extended isometry: `obtain ⟨T, hT⟩ := linear_isometry_extends_from_dense_subspace D hD T₀`, so `hT : ∀ x : D, T x = T₀ x`.
  obtain ⟨T, hT⟩ := linear_isometry_extends_from_dense_subspace D hD T₀
  generalize_proofs at *; (
  refine' ⟨ ⟨ T, shift, charLattice, charRogue, _, _ ⟩ ⟩;
  · refine' fun m n v => operator_intertwining_extends_from_dense D hD T ( shift m n ) ( charLattice m n ) _ v
    generalize_proofs at *; (
    intro d; specialize hlat m n d; aesop;);
  · intro a b v
    generalize_proofs at *; (
    apply operator_intertwining_extends_from_dense D hD T (shift a b) (charRogue a b) (fun d => by
      grind) v))

end CriticalMixedHRT