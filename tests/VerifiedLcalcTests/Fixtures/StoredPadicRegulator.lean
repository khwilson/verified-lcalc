/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.WorkedExamples.Curve37a1
import VerifiedLcalcTests.Fixtures.Geometry

/-! # Proof-parametric native ordinary regulator of 37.a at 5

The source row is https://www.lmfdb.org/EllipticCurve/Q/data/37.a.
The finite logarithm uses an independently computed sigma-log argument, while the
proof that the canonical sigma function gives that approximation remains explicit.
-/

@[expose] public section

namespace VerifiedLcalcTests.StoredPadic37

open VerifiedLcalc VerifiedLcalc.EllipticCurve WeierstrassCurve TauCeti.WorkedExamples

/-- The unique rational isomorphism class belonging to 37.a. -/
abbrev curve : WeierstrassCurve ℤ := curve37a1

/-- The rational model of 37.a1. -/
abbrev W := curve.baseChange ℚ

/-- The reduced minimal model of 37.a1 is already proved by TauCeti. -/
theorem reducedModel : W.IsReducedMinimal := isReducedMinimal_curve37a1

/-- The integral equation of 37.b3, the other class representative. -/
abbrev other : WeierstrassCurve ℤ := ⟨0, 1, 1, -3, 1⟩

/-- Rational isogeny representatives in the published conductor-37 class order. -/
def representatives : Fin 2 → WeierstrassCurve ℚ :=
  ![W, other.baseChange ℚ]

/-- The point generating the free quotient, as asserted by the separate basis premise. -/
abbrev generator : W.toAffine.Point := curve37a1Point

/-- The second integral model has the same prime discriminant as 37.a1. -/
theorem otherDiscriminant : other.Δ = 37 := by decide +kernel

/-- Both conductor roster representatives are nonsingular. -/
theorem rosterElliptic (i : Fin 2) : (representatives i).IsElliptic := by
  fin_cases i
  · change W.IsElliptic
    infer_instance
  · exact ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Both conductor roster representatives have intrinsic conductor 37. -/
theorem rosterConductor (i : Fin 2) :
    letI := rosterElliptic i
    Ideal.absNorm ((representatives i).algorithmicConductor ℤ) = 37 := by
  let _ := rosterElliptic i
  fin_cases i
  · exact Geometry.conductor37
  · let _ : (other.baseChange ℚ).IsElliptic := rosterElliptic 1
    change Ideal.absNorm ((other.baseChange ℚ).algorithmicConductor ℤ) = 37
    have hc : IsCoprime other.Δ other.c₄ := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide +kernel
    have hs := isSemistable_baseChange_of_isCoprime (F := ℚ) other hc
    have hm := isGlobalMinimal_baseChange_of_isCoprime (K := ℚ) other hc
    have hp : Prime (Ideal.span {(37 : ℤ)}) :=
      Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
    rw [(isSemistable_iff_algorithmicConductor_eq_radical _).mp hs,
      minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal hm
        (d := other.Δ) (by simp [baseChange]), otherDiscriminant,
      UniqueFactorizationMonoid.radical_of_prime hp]
    simp

/-- The two normalized coefficient sequences first differ at two. -/
theorem rosterOrdered (i j : Fin 2) (hij : i < j) :
    ∃ n : ℕ, 0 < n ∧
      (∀ m : ℕ, 0 < m → m < n → (representatives i).LFunction m =
        (representatives j).LFunction m) ∧
      (representatives i).LFunction n < (representatives j).LFunction n := by
  have hi : i = 0 := by omega
  have hj : j = 1 := by omega
  subst i
  subst j
  refine ⟨2, by decide, ?_, ?_⟩
  · intro m hm hm'
    have he : m = 1 := by omega
    subst m
    simp only [LFunction_apply_one]
  · let a : EllipticWitness := { equation := curve, primeCoefficients := some [(2, -2)] }
    let b : EllipticWitness := { equation := other, primeCoefficients := some [(2, 0)] }
    have ha := a.primeCoefficientsValid_sound (by decide +kernel) (by decide +kernel)
      2 (-2) (by decide)
    have hb := b.primeCoefficientsValid_sound (by decide +kernel) (by decide +kernel)
      2 0 (by decide)
    change (a.equation.baseChange ℚ).LFunction 2 < (b.equation.baseChange ℚ).LFunction 2
    rw [ha, hb]
    decide

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The independent catalogue, Mordell–Weil and normalized sigma inputs.
These premises contain no stated enclosure of the height or regulator. -/
class Premises (model : outParam (WeierstrassCurve ℤ)) where
  /-- The model supporting the formal parameter and sigma proof is the source equation. -/
  model_eq : model = curve
  /-- The two actual rational isogeny classes exhaust the conductor. -/
  exhaustive : ∀ E : WeierstrassCurve ℚ, ∀ h : E.IsElliptic,
    letI := h
    Ideal.absNorm (E.algorithmicConductor ℤ) = 37 →
      ∃ i, Nonempty (TauCeti.Isogeny E.toAffine (representatives i).toAffine)
  /-- The rational class of 37.a1 consists of just its rational isomorphism type. -/
  singletonClass : {m : IsogenyClassModel curve // m.classSize = 1}
  /-- A basis of the rational points modulo torsion. -/
  basis : Module.Basis (Fin 1) ℤ W.toAffine.PointModTorsion
  /-- The independent generator proof for the image of `(0, 0)`. -/
  generator_eq : Submodule.Quotient.mk generator = basis 0
  /-- The point used for sigma has nonsingular reduction at every finite prime. -/
  goodAtFinite : ∀ l : Nat.Primes,
    letI : Fact (l : ℕ).Prime := ⟨l.property⟩
    (8 : ℕ) • generator ∈ W.toAffine.nonsingularReduction ((rationalPlace l).valuation ℚ)
  /-- The formal `s = -1/y` expansion of this model. -/
  parameter : PowerSeries ℚ_[5]
  /-- The chosen formal expansion is the unique one at infinity. -/
  parameter_spec :
    IsWeierstrassParameterSeries (model.baseChange ℚ_[5]) parameter ∧
      ∀ s, IsWeierstrassParameterSeries (model.baseChange ℚ_[5]) s → s = parameter
  /-- The actual normalized sigma expansion at 5. -/
  sigma : PowerSeries ℚ_[5]
  /-- The differential equation and integrality characterize the series uniquely. -/
  sigma_spec :
    IsNormalizedOrdinarySigma (model.baseChange ℚ_[5]) parameter sigma ∧
      ∀ s, IsNormalizedOrdinarySigma (model.baseChange ℚ_[5]) parameter s → s = sigma
  /-- The independently calculated sigma-log argument to absolute precision 24. -/
  argument :
    ‖ordinarySigmaLogArgument sigma (21 / 25) (-69 / 125) 5 -
      ((11712203528994585 : ℚ) : ℚ_[5])‖ ≤
      (5 : ℝ) ^ (-(24 : ℤ))

/-- The marked rational multiple is an affine point on the exact source model. -/
theorem multiple_onCurve :
    W.toAffine.Equation (21 / 25) (-69 / 125) := by
  rw [Affine.equation_iff]
  decide +kernel

/-- The group computation gives the actual coordinates of eight times the generator. -/
theorem multiple_correct :
    (8 : ℕ) • generator = .mk (x := 21 / 25) (y := -69 / 125) multiple_onCurve := by
  rw [generator, curve37a1Point_def]
  decide +kernel

/-- The local parameter of the marked multiple is in the formal neighbourhood at five. -/
theorem formal_at_five :
    ‖-((21 / 25 : ℚ) : ℚ_[5]) / ((-69 / 125 : ℚ) : ℚ_[5])‖ < 1 := by
  have h : -((21 / 25 : ℚ) : ℚ_[5]) / ((-69 / 125 : ℚ) : ℚ_[5]) =
      ((35 / 23 : ℚ) : ℚ_[5]) := by
    rw [← Rat.cast_neg, ← Rat.cast_div]
    congr 1
    decide +kernel
  rw [h, Padic.eq_padicNorm, ← Certification.rationalPadicNorm_eq]
  have hr : Certification.rationalPadicNorm 5 (35 / 23) < 1 := by decide +kernel
  exact_mod_cast hr

/-- Assemble the independent inputs and kernel-checked multiple into the proof attachment. -/
def proofs {model : WeierstrassCurve ℤ} (h : Premises model) : IntegralCurveProofs curve :=
  { storedPadicRegulator := some {
      roster := {
        conductor := 37
        conductor_eq := rosterConductor 0
        size := 2
        representatives := representatives
        elliptic := rosterElliptic
        sameConductor := rosterConductor
        exhaustive := h.exhaustive
        ordered := rosterOrdered
        classIndex := 0
        subjectIsogenous := ⟨TauCeti.Isogeny.id _⟩ }
      singletonClass := h.singletonClass
      reduced := reducedModel
      p := ⟨5, by decide⟩
      prime_gt_three := by decide
      basis := h.basis
      generator := generator
      generator_eq := h.generator_eq
      multiple := 8
      x := 21 / 25
      y := ⟨-69 / 125, by decide +kernel⟩
      onCurve := multiple_onCurve
      multiple_eq := multiple_correct
      goodAtFinite := h.goodAtFinite
      denominator := ⟨5, by decide +kernel⟩
      parameter := h.parameter
      parameter_spec := by simpa only [h.model_eq] using h.parameter_spec
      sigma := h.sigma
      sigma_spec := by simpa only [h.model_eq] using h.sigma_spec
      formal := formal_at_five
      approximation := 11712203528994585
      approximationPrecision := 24
      approximation_correct := h.argument
      logTerms := 35 } }

section

variable {model : WeierstrassCurve ℤ} [h : Premises model]

set_option maxRecDepth 8000 in
-- The 35-term exact rational prefix has a denominator with repeated prime powers.
certify_ec Checked from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"conductor":37,"minimality":[37],
    "local_data":{"at_two":null,"at_three":null},"padic_regulator":
    {"lmfdb_iso":"37.a","p":5,"prec":20,"val":1,"unit":17009699681281}}"#
  with_proofs (proofs h)

end

end VerifiedLcalcTests.StoredPadic37
