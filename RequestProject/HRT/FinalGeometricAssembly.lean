import Mathlib
import RequestProject.MainStatement
import RequestProject.HRT.ConditionalFinalAssembly

/-!
# Final geometric-assembly layer of the critical mixed-arithmetic four-point HRT theorem

This module isolates and (where possible) discharges the **four final
geometric-assembly blockers** of the certification, stated faithfully against the
*actual* data of the main theorem `critical_mixed_orbit_HRT_L2`
(`RequestProject.MainStatement`): the time-frequency shift `tfShift`, the four
orbit points `0, u, v, ν`, an `L²` function `f`, and a coefficient vector
`c : Fin 4 → ℂ`.

The four blockers named in the task are:

* `StandardCriticalMixedNormalForm` — the SL(2,ℤ)/metaplectic *normal-form
  contradiction*: a four-term relation with **all nonzero** coefficients in the
  critical mixed orbit is impossible;
* `StandardFourTermRelationToNormalizedRelation` — *transport* of the explicit
  four-term Gabor relation to the normalized Zak/return-cocycle data;
* `StandardThreePointNonzeroCoefficients` — from the **three-point HRT theorem**,
  all four coefficients of a nontrivial four-term relation are nonzero;
* `StandardNormalizedContradictionImpliesLinearIndependence` — the logical glue
  turning the normal-form contradiction into linear independence (`c = 0`).

## What is proved here (no `sorry`, no `axiom`)

* **Task D** — `StandardThreePointNonzeroCoefficients_proved`: a *genuine*
  reduction of the nonzero-coefficient property to the exact imported three-point
  HRT type `StandardThreePointHRTTheorem`.

* **Task E** — `StandardNormalizedContradictionImpliesLinearIndependence_proved`:
  a *genuine* proof of linear independence from the normal-form contradiction
  plus the three-point HRT input (pure logic: contrapose + Task D).

* **Task B/C** — `StandardCriticalMixedNormalForm_proved` and
  `StandardFourTermRelationToNormalizedRelation_proved`: *genuine* reductions of
  the normal-form contradiction to the exact (deep, metaplectic-covariance) input
  type `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`), realised by feeding the
  Zak/return-cocycle witness into the already-proved project endpoint
  `normalized_return_cocycle_feeds_no_flat_band_root_data_minimal`.

* **Task F** — `critical_mixed_orbit_HRT_L2_conditional_on_classical_inputs`:
  the headline conditional theorem.  It proves the *exact conclusion* `c = 0` of
  `critical_mixed_orbit_HRT_L2` from precisely two clearly-named classical
  inputs — the three-point HRT theorem and the geometric normal-form
  contradiction — and nothing else.  No assumption is hidden, no statement is
  weakened, and `critical_mixed_orbit_HRT_L2` itself is untouched.

The only remaining content (the two named hypotheses
`StandardThreePointHRTTheorem` and either `StandardCriticalMixedNormalForm` or,
upstream of it, `StandardGaborRelationToNormalizedCriticalMixedRelation`)
corresponds to the deep external inputs (three-point HRT and the
metaplectic/affine-symplectic covariance producing the Zak witness), which are
genuinely absent from Mathlib `v4.28.0`.
-/

namespace CriticalMixedHRT

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Complex Filter Topology Polynomial

/-! ## The four orbit points and the relation in sum form -/

/-- The four time-frequency orbit points `0, u, v, ν` of the main theorem, as a
function `Fin 4 → ℝ × ℝ`. -/
def orbitPts (u v ν : ℝ × ℝ) : Fin 4 → ℝ × ℝ := ![0, u, v, ν]

/-- The explicit four-term relation of `critical_mixed_orbit_HRT_L2` written as a
sum over the four orbit points. -/
lemma orbitPts_sum_eq (u v ν : ℝ × ℝ) (f : ℝ → ℂ) (c : Fin 4 → ℂ) :
    (fun t => ∑ j, c j * tfShift (orbitPts u v ν j) f t)
      = (fun t => c 0 * tfShift 0 f t + c 1 * tfShift u f t
                  + c 2 * tfShift v f t + c 3 * tfShift ν f t) := by
  funext t
  simp [orbitPts, Fin.sum_univ_four]

/-- Distinctness of the four orbit points (as in the `Nodup` hypothesis of the
main theorem) is exactly injectivity of `orbitPts`. -/
lemma orbitPts_injective (u v ν : ℝ × ℝ)
    (h : ([(0 : ℝ × ℝ), u, v, ν] : List (ℝ × ℝ)).Nodup) :
    Function.Injective (orbitPts u v ν) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    and_true, not_or] at h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [orbitPts]

/-! ## Task D — three-point HRT ⇒ all coefficients nonzero

`StandardThreePointHRTTheorem` is the **exact imported three-point HRT type**:
any nontrivial linear combination of three *distinct* time-frequency translates
of a nonzero `L²` function does not vanish a.e.  We phrase it equivalently over a
four-point injective family with one coefficient set to zero (the remaining three
points are automatically distinct). -/

/-- **Exact imported three-point HRT theorem type.**  For a nonzero `g ∈ L²`, an
injective family of four orbit points `P`, and a coefficient vector with at least
one zero entry (so supported on `≤ 3` distinct points), an a.e.-vanishing
combination forces *all* coefficients to vanish — i.e. any three distinct
time-frequency translates of `g` are linearly independent. -/
def StandardThreePointHRTTheorem : Prop :=
  ∀ (g : ℝ → ℂ), MemLp g 2 volume → ¬ g =ᵐ[volume] 0 →
    ∀ (P : Fin 4 → ℝ × ℝ), Function.Injective P →
      ∀ (i : Fin 4) (d : Fin 4 → ℂ), d i = 0 →
        (fun t => ∑ j, d j * tfShift (P j) g t) =ᵐ[volume] 0 → d = 0

/-- **Task D.**  From the three-point HRT theorem, every coefficient of a
*nontrivial* four-term relation (over distinct points, nonzero `g`) is nonzero.
Genuine reduction (no `sorry`): if some `c i = 0` then the three-point HRT
theorem forces `c = 0`, contradicting nontriviality. -/
theorem StandardThreePointNonzeroCoefficients_proved
    (h3 : StandardThreePointHRTTheorem)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (hg0 : ¬ g =ᵐ[volume] 0)
    (P : Fin 4 → ℝ × ℝ) (hP : Function.Injective P)
    (c : Fin 4 → ℂ) (hc : c ≠ 0)
    (hrel : (fun t => ∑ j, c j * tfShift (P j) g t) =ᵐ[volume] 0) :
    ∀ i, c i ≠ 0 := by
  intro i hi
  exact hc (h3 g hg hg0 P hP i c hi hrel)

/-! ## Task E — normal-form contradiction ⇒ linear independence -/

/-- The **normalized contradiction** datum for `(g, P)`: there is *no*
all-nonzero four-term relation over the points `P` that vanishes a.e.  This is
the abstract form of the geometric normal-form obstruction. -/
def StandardNormalizedContradiction (g : ℝ → ℂ) (P : Fin 4 → ℝ × ℝ) : Prop :=
  ∀ (c : Fin 4 → ℂ), (∀ i, c i ≠ 0) →
    ¬ (fun t => ∑ j, c j * tfShift (P j) g t) =ᵐ[volume] 0

/-- **Task E.**  The normal-form contradiction together with the three-point HRT
theorem yields linear independence (`c = 0`) for *every* a.e.-vanishing four-term
relation.  Genuine proof (no `sorry`): contrapose, then use Task D to upgrade a
nontrivial relation to an all-nonzero one, contradicting the normal-form
obstruction. -/
theorem StandardNormalizedContradictionImpliesLinearIndependence_proved
    (h3 : StandardThreePointHRTTheorem)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (hg0 : ¬ g =ᵐ[volume] 0)
    (P : Fin 4 → ℝ × ℝ) (hP : Function.Injective P)
    (hcontra : StandardNormalizedContradiction g P)
    (c : Fin 4 → ℂ)
    (hrel : (fun t => ∑ j, c j * tfShift (P j) g t) =ᵐ[volume] 0) :
    c = 0 := by
  by_contra hc
  exact hcontra c
    (StandardThreePointNonzeroCoefficients_proved h3 g hg hg0 P hP c hc hrel) hrel

/-! ## Tasks B/C — the normal-form contradiction from the Zak/return witness

The deep geometric input — SL(2,ℤ)/metaplectic affine-symplectic covariance plus
the Zak/polyphase reduction — produces, from an all-nonzero four-term relation in
the *physical* `L²` model, a `NormalizedReturnData` together with the four
remaining certificate interfaces.  We bundle that output as a single (universe-
and instance-free) witness, and feed it into the already-proved project endpoint
`normalized_return_cocycle_feeds_no_flat_band_root_data_minimal` to derive the
contradiction.  Constructing the witness from the relation is exactly the
remaining deep covariance content, isolated as the explicit hypothesis
`StandardGaborRelationToNormalizedCriticalMixedRelation`. -/

/-- **The Zak/return-cocycle witness.**  A bundle of a normalized return-cocycle
datum `nrd` and the four remaining certificate interfaces (Denjoy–Koksma return
data, the analytic/active holonomy amplitude data, the holonomy/phase-lift gauge
data, and the minimal root data) over a common active window `(a₀, b₀)`.  It is
the precise output type of the metaplectic-covariance/Zak reduction.  Every field
is genuine certificate data — `witness_gives_false` shows the project already
derives a contradiction from it. -/
structure CriticalMixedReturnWitness where
  nrd : NormalizedReturnData
  dk : DenjoyKoksmaReturnData nrd.θ
  hq : Tendsto dk.q atTop atTop
  a₀ : ℝ
  b₀ : ℝ
  H : ℝ → ℂ
  hH : AnalyticOnNhd ℝ H (Set.Ioo a₀ b₀)
  hHne : ∀ s ∈ Set.Ioo a₀ b₀, H s ≠ 0
  S : Set ℝ
  hSU : S ⊆ Set.Ioo a₀ b₀
  hSpos : 0 < MeasureTheory.volume S
  hSres : ∀ s ∈ S, H s ∈ resonanceGroupC dk.q
  E : Set ℝ
  hE : E.Finite
  J : ℝ → ℂ
  hJgauge : ∀ s ∈ Set.Ioo a₀ b₀,
      J s = H s * Complex.exp (-2 * π * Complex.I * (nrd.θ : ℂ) * (s : ℂ))
  dlau : ℕ
  mlau : ℕ
  Mlau : ℤ
  ad : LaurentPolynomial ℂ
  had : ad ≠ 0
  coeffs : Fin (dlau + 1) → LaurentPolynomial ℂ
  h_ad_coeff : coeffs ⟨dlau, Nat.lt_succ_iff.mpr le_rfl⟩ = ad
  hroots_min : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    (∀ z ∈ (fibrePoly coeffs t).roots, ‖z‖ ≠ 1) ∧
    Mlau = ((fibrePoly coeffs t).roots.filter (fun z => ‖z‖ < 1)).card ∧
    ((fibrePoly coeffs t).roots.filter (fun z => 1 < ‖z‖)).card = mlau
  hJholo : ∀ t ∈ Set.Ioo a₀ b₀, evalLaurentCircle ad t ≠ 0 →
    ∀ ell_t : ℝ → ℂ, IsPeriodicLog ell_t (evalBiLaurentPoly coeffs Mlau t) →
      J t = Complex.exp (∫ x in (0 : ℝ)..1, ell_t x)

/-- The project's root-data-minimal no-flat-band endpoint derives a contradiction
from any `CriticalMixedReturnWitness`. -/
theorem witness_gives_false (w : CriticalMixedReturnWitness) : False :=
  normalized_return_cocycle_feeds_no_flat_band_root_data_minimal
    w.nrd w.dk w.hq w.H w.hH w.hHne w.S w.hSU w.hSpos w.hSres w.E w.hE
    w.J w.hJgauge w.mlau w.Mlau w.ad w.had w.coeffs w.h_ad_coeff w.hroots_min w.hJholo

/-- **Exact imported metaplectic-covariance / Zak-reduction type** (Task C).
From an all-nonzero four-term relation in the critical mixed orbit `(u, v, ν)`
that vanishes a.e., it produces the Zak/return-cocycle witness.  This is the deep
affine-symplectic-covariance content (genuinely absent from Mathlib). -/
def StandardGaborRelationToNormalizedCriticalMixedRelation
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ (c : Fin 4 → ℂ), (∀ i, c i ≠ 0) →
    (fun t => ∑ j, c j * tfShift (orbitPts u v ν j) f t) =ᵐ[volume] 0 →
    Nonempty CriticalMixedReturnWitness

/-- Alias of the covariance input under its affine-symplectic-reduction name
(Task B). -/
abbrev StandardAffineSymplecticReductionForHRT (u v ν : ℝ × ℝ) (f : ℝ → ℂ) : Prop :=
  StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f

/-- The **normal-form contradiction** specialised to the critical mixed orbit:
no all-nonzero four-term relation over `0, u, v, ν` vanishes a.e. -/
def StandardCriticalMixedNormalForm (u v ν : ℝ × ℝ) (f : ℝ → ℂ) : Prop :=
  StandardNormalizedContradiction f (orbitPts u v ν)

/-- **Task C.**  The metaplectic-covariance/Zak-reduction input implies the
normal-form contradiction.  Genuine reduction (no `sorry`): take the witness
produced from the all-nonzero relation and apply `witness_gives_false`. -/
theorem StandardFourTermRelationToNormalizedRelation_proved
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hcov : StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f) :
    StandardCriticalMixedNormalForm u v ν f := by
  intro c hc hrel
  exact (hcov c hc hrel).elim witness_gives_false

/-- **Task B.**  The affine-symplectic reduction implies the critical-mixed
normal-form contradiction. -/
theorem StandardCriticalMixedNormalForm_proved
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hcov : StandardAffineSymplecticReductionForHRT u v ν f) :
    StandardCriticalMixedNormalForm u v ν f :=
  StandardFourTermRelationToNormalizedRelation_proved u v ν f hcov

/-! ## Task F — the conditional final theorem -/

/-- **Task F (conditional final theorem).**

The exact conclusion `c = 0` of `critical_mixed_orbit_HRT_L2`, proved from
precisely two clearly-named classical inputs:

* `h3`  — the **three-point HRT theorem** (`StandardThreePointHRTTheorem`);
* `hNF` — the **geometric normal-form contradiction**
  (`StandardCriticalMixedNormalForm`, i.e. no all-nonzero four-term relation
  vanishes a.e.).

Every hypothesis of the original main theorem is carried verbatim (the
geometric/number-theoretic content `hν, hsymp, hrank` is absorbed into the deep
input `hNF`), nothing is hidden, and the conclusion is the *exact* `c = 0`.  The
main theorem `critical_mixed_orbit_HRT_L2` itself is untouched. -/
theorem critical_mixed_orbit_HRT_L2_conditional_on_classical_inputs
    (u v : ℝ × ℝ) (α β : ℝ) (ν : ℝ × ℝ)
    (hν : ν = (α * u.1 + β * v.1, α * u.2 + β * v.2))
    (hsymp : |symp u v| = 1)
    (hdistinct : ([(0 : ℝ × ℝ), u, v, ν] : List (ℝ × ℝ)).Nodup)
    (hrank : Module.finrank ℚ (Submodule.span ℚ ({1, α, β} : Set ℝ)) = 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0)
    (h3 : StandardThreePointHRTTheorem)
    (hNF : StandardCriticalMixedNormalForm u v ν f)
    (c : Fin 4 → ℂ)
    (hrel : (fun t => c 0 * tfShift 0 f t + c 1 * tfShift u f t
              + c 2 * tfShift v f t + c 3 * tfShift ν f t) =ᵐ[volume] 0) :
    c = 0 := by
  have hP : Function.Injective (orbitPts u v ν) := orbitPts_injective u v ν hdistinct
  have hrel' : (fun t => ∑ j, c j * tfShift (orbitPts u v ν j) f t) =ᵐ[volume] 0 := by
    rw [orbitPts_sum_eq]; exact hrel
  exact StandardNormalizedContradictionImpliesLinearIndependence_proved h3 f hf hf0
    (orbitPts u v ν) hP hNF c hrel'

/-- **Task F variant — fully upstream form.**  The same conclusion `c = 0` from
the three-point HRT theorem and the *covariance* input
`StandardGaborRelationToNormalizedCriticalMixedRelation` (which feeds the
normal-form contradiction through Task C). -/
theorem critical_mixed_orbit_HRT_L2_conditional_on_covariance
    (u v : ℝ × ℝ) (α β : ℝ) (ν : ℝ × ℝ)
    (hν : ν = (α * u.1 + β * v.1, α * u.2 + β * v.2))
    (hsymp : |symp u v| = 1)
    (hdistinct : ([(0 : ℝ × ℝ), u, v, ν] : List (ℝ × ℝ)).Nodup)
    (hrank : Module.finrank ℚ (Submodule.span ℚ ({1, α, β} : Set ℝ)) = 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0)
    (h3 : StandardThreePointHRTTheorem)
    (hcov : StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f)
    (c : Fin 4 → ℂ)
    (hrel : (fun t => c 0 * tfShift 0 f t + c 1 * tfShift u f t
              + c 2 * tfShift v f t + c 3 * tfShift ν f t) =ᵐ[volume] 0) :
    c = 0 :=
  critical_mixed_orbit_HRT_L2_conditional_on_classical_inputs u v α β ν hν hsymp
    hdistinct hrank f hf hf0 h3
    (StandardFourTermRelationToNormalizedRelation_proved u v ν f hcov) c hrel

end CriticalMixedHRT
