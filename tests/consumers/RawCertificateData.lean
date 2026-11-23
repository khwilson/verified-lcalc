import VerifiedLcalc.Certificate.Numerical.Intervals
import VerifiedLcalc.Certificate.Numerical.Precision
import VerifiedLcalc.Certificate.Support.Transcripts
import VerifiedLcalc.Certificate.Numerical.Outputs
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
    `VerifiedLcalc.Verification.CentralEvaluator,
    `VerifiedLcalc.Verification.DerivativeEvaluator] do
    if imported.contains implementation then
      throwError m!"raw certificate data imported implementation module {implementation}"
