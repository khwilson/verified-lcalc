/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.Reduced
import VerifiedLcalc.UpstreamCandidates.TauCeti.ConductorDenominator

/-! # Geometry and modified Szpiro certificates for 37.a1 -/

@[expose] public section

namespace VerifiedLcalcTests.Geometry

open VerifiedLcalc WeierstrassCurve TauCeti.WorkedExamples

/-- TauCeti’s intrinsic algorithmic conductor for 37.a1 has norm 37. -/
theorem conductor37 : Ideal.absNorm ((curve37a1.baseChange ℚ).algorithmicConductor ℤ) = 37 := by
  have hs : IsSemistable ℤ (curve37a1.baseChange ℚ) :=
    isSemistable_baseChange_of_isCoprime curve37a1 (by
      rw [Δ_curve37a1, c₄_curve37a1, Int.isCoprime_iff_gcd_eq_one]
      norm_num)
  have hp : Prime (Ideal.span {(37 : ℤ)}) :=
    Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
  rw [(isSemistable_iff_algorithmicConductor_eq_radical _).mp hs,
    minimalDiscriminantIdeal_curve37a1, UniqueFactorizationMonoid.radical_of_prime hp]
  simp

/-- Every quadratic twist of 37.a1 has conductor at least 37, since its j-invariant
still has denominator divisible by 37. -/
theorem minimum37 (d : ℚ) (h : ((curve37a1.baseChange ℚ).quadraticTwistOf 0 (-d)).IsElliptic) :
    letI := h
    37 ≤ Ideal.absNorm (((curve37a1.baseChange ℚ).quadraticTwistOf 0 (-d)).algorithmicConductor ℤ) := by
  let := h
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (algorithmicConductor_ne_bot ℤ _)))
  apply prime_dvd_absNorm_algorithmicConductor_of_dvd_j_den _ (by decide)
  rw [j_quadraticTwistOf _ _ _ h]
  norm_num [j_eq, baseChange, map_Δ, map_c₄, Δ_curve37a1, c₄_curve37a1]
/-- The original minimal integral equation with trivial discriminant attains the lower bound. -/
def twist37 : VerifiedLcalc.MinimumQuadraticTwistFacts curve37a1 where
  equation := curve37a1
  discriminant := 1
  fundamental := Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨rfl, squarefree_one⟩)
  change := (curve37a1.baseChange ℚ).quadraticTwistOfVariableChange 1 0
    (Units.mk0 2 (by norm_num)) (-1)
  twist_eq := by
    have e := (curve37a1.baseChange ℚ).quadraticTwistOfVariableChange_smul 1 0
      (Units.mk0 2 (by norm_num)) (-1)
    norm_num at e ⊢
    exact e
  elliptic := inferInstance
  minimal := isReducedMinimal_curve37a1.isGlobalMinimal
  conductor_minimal d _ h := by
    rw [conductor37]
    exact minimum37 d h

/-- Independently proved arithmetic inputs for the modified Szpiro enclosure. -/
def arithmetic37 : ModifiedSzpiroRatioEvidence curve37a1 where
  minimal := isReducedMinimal_curve37a1.isGlobalMinimal
  conductor := 37
  conductor_eq := conductor37

/-- The arithmetic proof attachment shared by the Lean and exact JSON tests. -/
def arithmeticProofs : IntegralCurveProofs curve37a1 where
  minimumQuadraticTwist := some { minimum := twist37 }
  modifiedSzpiroRatio := some arithmetic37

certify_ec Geometry37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"discriminant":37,"min_quad_twist_ainvs":[0,0,1,-1,0],
      "min_quad_twist_disc":"1","szpiro_ratio":"3.216246758769211",
      "szpiro_ratio_evidence":{"error":"0.00000000000001"}}"#
  with_proofs arithmeticProofs

/-- Explicit geometric and uniqueness hypotheses for the conditional fixture. -/
class GeometryHypotheses (W : outParam (WeierstrassCurve ℚ)) [W.IsElliptic] : Prop where
  /-- The given curve is the rational base change of 37.a1. -/
  equation_eq : W = curve37a1.baseChange ℚ
  /-- The full geometric endomorphism ring is the integer ring. -/
  endomorphismRing : Nonempty (ℤ ≃+* W.GeometricEnd)
  /-- All reduced minimum-conductor models agree with the chosen equation and discriminant. -/
  uniqueMinimum : ∀ other : MinimumQuadraticTwistFacts curve37a1,
    let := other.elliptic
    IsReducedMinimal (other.equation.baseChange ℚ) →
      other.equation = twist37.equation ∧ other.discriminant = twist37.discriminant

/-- Transport the supplied endomorphism ring proof to 37.a1. -/
theorem GeometryHypotheses.ofEquation {W : WeierstrassCurve ℚ} [W.IsElliptic] (h : GeometryHypotheses W) :
    Nonempty (ℤ ≃+* (curve37a1.baseChange ℚ).GeometricEnd) := by
  obtain ⟨heq, hEnd, _⟩ := h
  subst W
  exact hEnd

/-- Attach a proof of the full geometric endomorphism ring with its zero catalogue code. -/
def nonCMProofs (h : Nonempty (ℤ ≃+* (curve37a1.baseChange ℚ).GeometricEnd)) :
    IntegralCurveProofs curve37a1 :=
  { arithmeticProofs with complexMultiplication := some ⟨0, Or.inl ⟨rfl, h⟩⟩ }

section

variable {W : WeierstrassCurve ℚ} [W.IsElliptic] [h : GeometryHypotheses W]

/-- Attach both geometric evidence and uniqueness of the ordinary reduced minimizer. -/
def geometryProofs (h : GeometryHypotheses W) : IntegralCurveProofs curve37a1 :=
  { nonCMProofs h.ofEquation with minimumQuadraticTwist := some {
    minimum := twist37
    uniqueMinimum := some {
      nonCM := h.ofEquation
      nonexceptional := by
        norm_num [j_eq, baseChange, map_Δ, map_c₄, Δ_curve37a1, c₄_curve37a1]
      reduced := isReducedMinimal_curve37a1
      unique := h.uniqueMinimum } } }

certify_ec Geometry37WithCM from
  { equation := curve37a1, complexMultiplication := some 0,
    minimumTwistEquation := some curve37a1, minimumTwistDiscriminant := some 1 }
  with_proofs (geometryProofs h)

end

end VerifiedLcalcTests.Geometry
