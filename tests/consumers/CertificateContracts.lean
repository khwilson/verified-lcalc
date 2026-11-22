import VerifiedLcalc.Certificates
import Lean

/-! This consumer checks the public data contracts without importing certification backends. -/

open VerifiedLcalc Lean Elab Command

example (curve : WeierstrassCurve ℤ) : Type := IntegralXSupport curve
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    Type := CompleteIntegralPointFacts curve
example (source target : WeierstrassCurve ℤ) : Type := DegreeTwoIsogenyFact source target
example : Type := TorsionBoundWitness
example {R : Type} [CommRing R] : Type := DiscriminantWitness R
example {R : Type} [CommRing R] (curve : WeierstrassCurve R) : Type := EllipticProofs curve
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    Type := RationalInvariantFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionDivisorFacts curve
example (curve : WeierstrassCurve ℤ) : Type := CyclicTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TwoFactorTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionPrimeSupportFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionFacts curve
example : Type := Box
example : Type := PrecisionPolicy
example : Type := EllipticCurve.MinimalityWitness
example : Type := EllipticCurve.TateWitness
example : Type := EllipticCurve.WildData
example : Type := EllipticCurve.CentralResult
example : Type := EllipticCurve.DerivativeResult
example (result : EllipticCurve.CentralResult) : Prop := EllipticCurve.CentralPayloadCorrect result
example (result : EllipticCurve.DerivativeResult) : Prop :=
  EllipticCurve.DerivativePayloadCorrect result
example {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic] :
    Type := EllipticCurve.AlgebraicRankBounds W

section MordellWeilInstance
variable {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]

example : Module.Finite ℤ W.toAffine.Point := by infer_instance

example (n : ℕ) (h : Module.rank ℤ W.toAffine.Point = (n : Cardinal)) :
    EllipticCurve.AlgebraicRankBounds W :=
  .ofRankEq n h
end MordellWeilInstance

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Certification.CurveData,
    `VerifiedLcalc.Certification.IntegralPointCount,
    `VerifiedLcalc.Certification.DegreeTwoIsogeny,
    `VerifiedLcalc.Certification.DegreeTwoIsogenyRaw,
    `VerifiedLcalc.Certification.TorsionBoundFacts,
    `VerifiedLcalc.EllipticCurve.TorsionBound,
    `VerifiedLcalc.Scan,
    `VerifiedLcalc.Precision,
    `VerifiedLcalc.Certificate,
    `VerifiedLcalc.EllipticCurve.CentralCore,
    `VerifiedLcalc.EllipticCurve.DerivativeCore,
    `VerifiedLcalc.Certification.CentralEvaluator,
    `VerifiedLcalc.Certification.AbcQuality,
    `VerifiedLcalc.Certification.StoredInvariants,
    `VerifiedLcalc.Certification.DerivativeEvaluator] do
    if imported.contains backend then
      throwError m!"contract umbrella imported backend module {backend}"
