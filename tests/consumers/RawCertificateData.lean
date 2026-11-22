import VerifiedLcalc.Certificates.Enclosures
import VerifiedLcalc.Certificates.PrecisionPolicy
import VerifiedLcalc.Certificates.Transcripts
import VerifiedLcalc.Certificates.NumericalData
import Lean

/-! Import-only check that raw payload records stay independent of formulas and evaluators. -/

open Lean Elab Command

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for implementation in [`VerifiedLcalc.EllipticCurve.CoefficientCore,
    `VerifiedLcalc.EllipticCurve.CentralDefinitions,
    `VerifiedLcalc.EllipticCurve.DerivativeDefinitions,
    `VerifiedLcalc.EllipticCurve.CentralCore,
    `VerifiedLcalc.EllipticCurve.DerivativeCore,
    `VerifiedLcalc.Certification.CentralEvaluator,
    `VerifiedLcalc.Certification.DerivativeEvaluator] do
    if imported.contains implementation then
      throwError m!"raw certificate data imported implementation module {implementation}"
