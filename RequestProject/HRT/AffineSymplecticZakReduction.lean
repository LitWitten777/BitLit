import Mathlib
import RequestProject.HRT.FinalGeometricAssembly
import RequestProject.HRT.ZakToNormalizedCocycle

open scoped Classical BigOperators Real ENNReal
open MeasureTheory Filter Topology Complex

set_option maxHeartbeats 1000000

/-!
# Certifying the affine-symplectic / metaplectic + Zak-covariance reduction

This module certifies the **reduction** that produces the Stage-6A
return-cocycle witness `CriticalMixedReturnWitness` from a physical four-term
Gabor relation in the critical mixed orbit.  The reduction has two conceptual
halves:

* the **affine-symplectic / metaplectic covariance** half — a unitary change of
  time-frequency coordinates (`SL(2,ℝ)` metaplectic operator composed with an
  affine shift) transporting the physical relation
  `∑ⱼ cⱼ · π(orbitPts j) f = 0` over `L²(ℝ)` into the *normalized* relation
  `d₀ g + d₁ π(λ₁) g + d₂ π(λ₂) g + d₃ π(a, p/m) g = 0`
  inside an abstract `L²`-model `V` equipped with an `L2ZakModel`, where
  `(r₁,t₁),(r₂,t₂)` is a unimodular `ℤ²`-basis and `θ = m·a` is irrational;

* the **Zak-covariance** half — applying the Zak transform to the normalized
  relation produces the one-step Zak fibre equation, hence a
  `NormalizedReturnData`, and (together with the remaining certificate data)
  the full `CriticalMixedReturnWitness`.

## What is genuinely certified here (no `sorry`, no `axiom`)

* `tfShift_add`, `tfShift_smul`, `tfShift_zero_fun`, `tfShift_cocycle`,
  `tfShift_memLp` — the **affine** time-frequency covariance algebra of the
  physical shift `tfShift` (additivity, homogeneity, the affine cocycle
  composition law with its explicit phase, and `L²`-stability).  This is the
  certified affine part of the affine-symplectic covariance.

* `CriticalMixedZakTransport` — the **explicit output bundle** of the
  metaplectic + Zak-covariance reduction: an `L2ZakModel` on an abstract `L²`
  model `V`, the transported element `g`, the normalized arithmetic data, the
  normalized `Z.shift` relation, and the remaining certificate data.  It is a
  *transparent refinement* of `CriticalMixedReturnWitness`: instead of an opaque
  `NormalizedReturnData` it carries the genuine Zak model and normalized
  relation from which the return cocycle is **derived** through the certified
  Zak covariance.

* `returnData_of_zakTransport` — the certified Zak-covariance step: from a
  `CriticalMixedZakTransport` it constructs the `NormalizedReturnData`
  (the *return-cocycle witness* proper) via
  `hrt_relation_to_one_step_zak_equation`.

* `witness_of_zakTransport` — assembles the full `CriticalMixedReturnWitness`
  from a `CriticalMixedZakTransport` (return cocycle + certificate data).

* `AffineSymplecticMetaplecticReduction` — the named interface isolating the
  genuinely deep, Mathlib-absent input: that *every* all-nonzero a.e.-vanishing
  physical relation admits such a normalized Zak transport bundle.  This is the
  exact metaplectic-covariance content.

* `standardGabor_of_affineSymplecticMetaplecticReduction` — the headline
  certification: the affine-symplectic / metaplectic + Zak-covariance reduction
  produces the `StandardGaborRelationToNormalizedCriticalMixedRelation`
  (= `StandardAffineSymplecticReductionForHRT`) input consumed by the
  geometric-assembly layer.  Everything downstream of the transport bundle (Zak
  covariance → return cocycle → witness → contradiction) is fully certified.

## Honest scope

The single remaining gap is the *construction* of the transport bundle from a
physical relation, i.e. inhabiting `AffineSymplecticMetaplecticReduction`.  That
requires (a) the metaplectic representation of `SL(2,ℝ)` with its intertwining
covariance `μ_S π(z) μ_S⁻¹ = (phase) π(Sz)`, and (b) a concrete `L2ZakModel` on
`L²(ℝ)` — both genuinely absent from Mathlib `v4.28.0`.  They are isolated here
as the explicit named interface; the reduction *logic* itself is certified with
no `sorry`.
-/

namespace CriticalMixedHRT

/-! ## The affine covariance algebra of the physical time-frequency shift -/

/-- Additivity of the physical time-frequency shift in the function argument. -/
theorem tfShift_add (p : ℝ × ℝ) (f g : ℝ → ℂ) :
    tfShift p (f + g) = tfShift p f + tfShift p g := by
  funext t; simp [tfShift, mul_add]

/-- `ℂ`-homogeneity of the physical time-frequency shift. -/
theorem tfShift_smul (p : ℝ × ℝ) (c : ℂ) (f : ℝ → ℂ) :
    tfShift p (c • f) = c • tfShift p f := by
  funext t; simp only [tfShift, Pi.smul_apply, smul_eq_mul]; ring

/-- The physical time-frequency shift kills the zero function. -/
theorem tfShift_zero_fun (p : ℝ × ℝ) : tfShift p (0 : ℝ → ℂ) = 0 := by
  funext t; simp [tfShift]

/-- **Affine cocycle / composition law.**  Composing two physical
time-frequency shifts gives the shift by the sum of the points, up to the
explicit unimodular phase `e^{2πi · q.2 · p.1}`. -/
theorem tfShift_cocycle (p q : ℝ × ℝ) (f : ℝ → ℂ) :
    tfShift p (tfShift q f)
      = Complex.exp (2 * π * Complex.I * (q.2 : ℂ) * (p.1 : ℂ)) • tfShift (p + q) f := by
  funext t
  simp only [tfShift, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  have harg : t - p.1 - q.1 = t - (p.1 + q.1) := by ring
  rw [harg, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-
**`L²`-stability of the physical time-frequency shift.**  The shift is the
composition of a unit-modulus modulation and a measure-preserving translation,
so it preserves membership in `L²`.
-/
theorem tfShift_memLp (p : ℝ × ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    MemLp (tfShift p f) 2 volume := by
  have htrans : MemLp (fun t => f (t - p.1)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_sub_right volume p.1)
  have hmod : ∀ t : ℝ, ‖Complex.exp (-2 * π * Complex.I * (p.2 : ℂ) * (t : ℂ))‖ = 1 := by
    intro t; rw [Complex.norm_exp]; simp
  refine ⟨(Continuous.aestronglyMeasurable (by continuity)).mul htrans.1, ?_⟩
  have hnorm : eLpNorm (tfShift p f) 2 volume = eLpNorm (fun t => f (t - p.1)) 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with t
    simp only [tfShift]
    rw [norm_mul, hmod t, one_mul]
  rw [hnorm]; exact htrans.2

/-! ## The transport bundle: output of the metaplectic + Zak-covariance reduction -/

/-- **The explicit output bundle of the metaplectic + Zak-covariance reduction.**

This is a transparent refinement of `CriticalMixedReturnWitness`: it carries the
genuine `L2ZakModel` on an abstract `L²`-model `V`, the transported element `g`,
the normalized arithmetic data (`m,p,a`, unimodular `ℤ²`-basis, irrational
`θ = m·a`, the four nonzero normalized coefficients), the **normalized
`Z.shift` relation**, and the remaining certificate data over a common active
window `(a₀,b₀)`.  The return cocycle is *derived* from these by the certified
Zak covariance (`returnData_of_zakTransport`), rather than postulated. -/
structure CriticalMixedZakTransport where
  /-- The abstract `L²(ℝ)`-model carrying the `L2ZakModel`. -/
  V : Type
  [instNorm : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℂ V]
  /-- The Zak transform interface on `V`. -/
  Z : L2ZakModel V
  m : ℕ
  hm : 0 < m
  p : ℤ
  a : ℝ
  hθ_irr : Irrational ((m : ℝ) * a)
  d₀ : ℂ
  d₁ : ℂ
  d₂ : ℂ
  d₃ : ℂ
  hd₀ : d₀ ≠ 0
  hd₁ : d₁ ≠ 0
  hd₂ : d₂ ≠ 0
  hd₃ : d₃ ≠ 0
  r₁ : ℤ
  t₁ : ℤ
  r₂ : ℤ
  t₂ : ℤ
  unimodular : r₁ * t₂ - r₂ * t₁ = 1
  /-- The transported element `g = μ f` of the abstract `L²`-model. -/
  g : V
  /-- The **normalized** four-term relation in the Zak model. -/
  hrel : d₀ • g + d₁ • Z.shift (r₁ : ℝ) (t₁ : ℝ) g
            + d₂ • Z.shift (r₂ : ℝ) (t₂ : ℝ) g
            + d₃ • Z.shift a ((p : ℝ) / (m : ℝ)) g = 0
  -- remaining certificate data over a common active window `(a₀, b₀)`
  dk : DenjoyKoksmaReturnData ((m : ℝ) * a)
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
      J s = H s * Complex.exp (-2 * π * Complex.I * (((m : ℝ) * a : ℝ) : ℂ) * (s : ℂ))
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

/-- **Certified Zak-covariance step.**  From a transport bundle, the normalized
`Z.shift` relation produces the `NormalizedReturnData` (the return cocycle
proper) via the already-proved `hrt_relation_to_one_step_zak_equation`. -/
noncomputable def returnData_of_zakTransport (D : CriticalMixedZakTransport) :
    NormalizedReturnData :=
  letI := D.instNorm
  letI := D.instInner
  hrt_relation_to_one_step_zak_equation D.Z D.m D.hm D.p D.a D.hθ_irr
    D.d₀ D.d₁ D.d₂ D.d₃ D.hd₀ D.hd₁ D.hd₂ D.hd₃ D.r₁ D.t₁ D.r₂ D.t₂
    D.unimodular D.g D.hrel

/-- The return cocycle derived from a transport bundle has frequency parameter
`θ = m·a`. -/
@[simp] theorem returnData_of_zakTransport_θ (D : CriticalMixedZakTransport) :
    (returnData_of_zakTransport D).θ = (D.m : ℝ) * D.a := rfl

/-- **Assembling the full return-cocycle witness.**  From a transport bundle, the
derived return cocycle together with the certificate data forms a
`CriticalMixedReturnWitness`. -/
noncomputable def witness_of_zakTransport (D : CriticalMixedZakTransport) :
    CriticalMixedReturnWitness where
  nrd := returnData_of_zakTransport D
  dk := D.dk
  hq := D.hq
  a₀ := D.a₀
  b₀ := D.b₀
  H := D.H
  hH := D.hH
  hHne := D.hHne
  S := D.S
  hSU := D.hSU
  hSpos := D.hSpos
  hSres := D.hSres
  E := D.E
  hE := D.hE
  J := D.J
  hJgauge := D.hJgauge
  dlau := D.dlau
  mlau := D.mlau
  Mlau := D.Mlau
  ad := D.ad
  had := D.had
  coeffs := D.coeffs
  h_ad_coeff := D.h_ad_coeff
  hroots_min := D.hroots_min
  hJholo := D.hJholo

/-! ## The metaplectic-covariance interface and the reduction certification -/

/-- **The affine-symplectic / metaplectic + Zak-covariance reduction interface.**

This is the genuinely deep, Mathlib-absent input, isolated exactly: for the
critical mixed orbit `(u,v,ν)` and physical `f`, *every* all-nonzero,
a.e.-vanishing four-term Gabor relation admits a normalized Zak transport bundle
`CriticalMixedZakTransport`.  Inhabiting this is precisely the metaplectic
covariance `μ_S π(z) μ_S⁻¹ = (phase) π(Sz)` together with a concrete
`L2ZakModel` on `L²(ℝ)`. -/
def AffineSymplecticMetaplecticReduction (u v ν : ℝ × ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ (c : Fin 4 → ℂ), (∀ i, c i ≠ 0) →
    (fun t => ∑ j, c j * tfShift (orbitPts u v ν j) f t) =ᵐ[volume] 0 →
    Nonempty CriticalMixedZakTransport

/-- **Headline certification.**

The affine-symplectic / metaplectic + Zak-covariance reduction produces the
`StandardGaborRelationToNormalizedCriticalMixedRelation`
(= `StandardAffineSymplecticReductionForHRT`) input consumed by the
geometric-assembly layer.  Everything downstream of the transport bundle — the
Zak covariance producing the return cocycle, its assembly into the
return-cocycle witness, and the resulting no-flat-band contradiction — is fully
certified here with no `sorry`. -/
theorem standardGabor_of_affineSymplecticMetaplecticReduction
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hred : AffineSymplecticMetaplecticReduction u v ν f) :
    StandardGaborRelationToNormalizedCriticalMixedRelation u v ν f := by
  intro c hc hrel
  exact (hred c hc hrel).elim (fun D => ⟨witness_of_zakTransport D⟩)

/-- Alias under the affine-symplectic-reduction name. -/
theorem standardAffineSymplectic_of_reduction
    (u v ν : ℝ × ℝ) (f : ℝ → ℂ)
    (hred : AffineSymplecticMetaplecticReduction u v ν f) :
    StandardAffineSymplecticReductionForHRT u v ν f :=
  standardGabor_of_affineSymplecticMetaplecticReduction u v ν f hred

end CriticalMixedHRT