/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Certificates
import VerifiedLcalc.Certificate.Witnesses
import Lean

/-! This consumer checks the public data contracts without importing certification backends. -/

open VerifiedLcalc Lean Elab Command

#check RealPeriodFact
#check TamagawaProductFact
#check AnalyticShaFact
#check RoundedAnalyticShaFact
#check IntegralXSupport
#check CompleteIntegralPointFacts
#check DegreeTwoIsogenyFact
#check IsogenyClassModel
#check IsogenyClassOrdering
#check IsogenyClassEvidence
#check EllipticCertificate.isogenyClass
#check NonmaxPrimeSupportFact
#check AdelicGeneratorsClaim
#check FiniteGaloisImageFact
#check EllipticCertificate.nonmaxPrimes
#check EllipticCertificate.adelicGenerators
#check Box
#check PrecisionPolicy
#check EllipticCurve.MinimalityWitness
#check EllipticCurve.TateWitness
#check EllipticCurve.WildData
#check EllipticCurve.CentralResult
#check EllipticCurve.DerivativeResult
#check EllipticCurve.CentralPayloadCorrect
#check EllipticCurve.DerivativePayloadCorrect
#check EllipticCurve.AlgebraicRankBounds
#check Witness
#check Certificate
#check Box.Contains
#check Encloses
#check AnalyticCertificate
#check Artifacts.WitnessAccepts
#check Artifacts.Checked
#check NumericalRanks.CutoffAccepts
#check NumericalRanks.Checked
#check Artifacts.AnalyticEvidence
#check NumericalRanks.Evidence
#check NumericalRanks.SmallDerivatives
#check NumericalRanks.ExactVanishingHypothesis
example (curve : WeierstrassCurve ℤ) : Type := IntegralXSupport curve
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    Type := CompleteIntegralPointFacts curve
example (source target : WeierstrassCurve ℤ) : Type := DegreeTwoIsogenyFact source target
example : Type := TorsionBoundWitness
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    MinimalModelArithmeticFacts curve → List (LocalRootNumberFact curve) :=
  MinimalModelArithmeticFacts.localRootNumbers
example : LocalReductionClaim → Option ℤ := LocalReductionClaim.rootNumber
example {R : Type} [CommRing R] : Type := DiscriminantWitness R
example {R : Type} [CommRing R] (curve : WeierstrassCurve R) : Type := EllipticProofs curve
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    Type := RationalInvariantFacts curve
example {R : Type} [CommRing R] (curve : WeierstrassCurve R) :
    Type := AffineMembership curve
example (curve : WeierstrassCurve ℤ) : Type := IntegralYFiberFacts curve
example (coordinates : List (Rat × Rat)) : Type := GeneratorCountFacts coordinates
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
  for backend in [`VerifiedLcalc.Verification.CurveData,
    `VerifiedLcalc.Verification.IntegralPointCount,
    `VerifiedLcalc.Verification.DegreeTwoIsogeny,
    `VerifiedLcalc.Verification.DegreeTwoIsogenyRaw,
    `VerifiedLcalc.Verification.IsogenyClass,
    `VerifiedLcalc.Certificate.Support.GaloisImage,
    `VerifiedLcalc.Tactic.CertifyECGalois,
    `VerifiedLcalc.Analytic,
    `VerifiedLcalc.Verification.TorsionBoundFacts,
    `VerifiedLcalc.EllipticCurve.TorsionBound,
    `VerifiedLcalc.Scan,
    `VerifiedLcalc.CertificateSoundness,
    `VerifiedLcalc.NumericalRankSoundness,
    `VerifiedLcalc.Precision,
    `VerifiedLcalc.Certificate,
    `VerifiedLcalc.EllipticCurve.CentralCore,
    `VerifiedLcalc.EllipticCurve.DerivativeCore,
    `VerifiedLcalc.Verification.CentralEvaluator,
    `VerifiedLcalc.Verification.AbcQuality,
    `VerifiedLcalc.Verification.StoredInvariants,
    `VerifiedLcalc.Verification.DerivativeEvaluator] do
    if imported.contains backend then
      throwError m!"contract umbrella imported backend module {backend}"
