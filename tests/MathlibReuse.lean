import VerifiedLcalc.EllipticCurve.CoefficientCore
import VerifiedLcalc.EllipticCurve.Tate.TameCore

-- Retain the former valuation routine's zero, unit, and composite-base behavior.
example : padicValNat 0 72 = 0 ∧ padicValNat 1 72 = 0 ∧ padicValNat 2 0 = 0 := by
  decide +kernel
example : padicValNat 4 64 = 3 ∧ padicValNat 2 72 = 3 ∧ padicValNat 3 72 = 2 := by
  decide +kernel

example : padicValNat 0 72 = 0 ∧ padicValNat 1 72 = 0 ∧ padicValNat 2 0 = 0 := by
  decide +kernel

-- These cases exercise the finite-ring API, rather than only its prime-field case.
example : VerifiedLcalc.EllipticCurve.isSquareMod 0 0 = false := by decide +kernel
example : VerifiedLcalc.EllipticCurve.isSquareMod 1 27 = true := by decide +kernel
example : VerifiedLcalc.EllipticCurve.isSquareMod 2 (-1) = true := by decide +kernel
example : VerifiedLcalc.EllipticCurve.isSquareMod 4 1 = true ∧
    VerifiedLcalc.EllipticCurve.isSquareMod 4 2 = false := by decide +kernel
