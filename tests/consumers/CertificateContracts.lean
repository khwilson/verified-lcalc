import VerifiedLcalc.Certificates
import Lean

/-! This consumer checks the public data contracts without importing certification backends. -/

open VerifiedLcalc Lean Elab Command

#check IntegralXSupport
#check CompleteIntegralPointFacts
#check DegreeTwoIsogenyFact
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
    `VerifiedLcalc.Scan,
    `VerifiedLcalc.Precision,
    `VerifiedLcalc.Certificate,
    `VerifiedLcalc.EllipticCurve.CentralCore,
    `VerifiedLcalc.EllipticCurve.DerivativeCore,
    `VerifiedLcalc.Certification.CentralEvaluator,
    `VerifiedLcalc.Certification.DerivativeEvaluator] do
    if imported.contains backend then
      throwError m!"contract umbrella imported backend module {backend}"
