import VerifiedLcalc.EllipticCurve.DerivativeCore
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Numerics

-- Invalid inputs must remain failures, without producing evidence.
example : evaluateDerivative ⟨0,0,1,-1,0⟩ 0 8 1 8 = none := by decide +kernel
example : evaluateDerivative ⟨0,0,1,-1,0⟩ 37 8 0 8 = none := by decide +kernel
example : evaluateDerivative ⟨0,0,1,-1,0⟩ 37 8 1 1 = none := by decide +kernel
-- A signed Fourier prefix must use all endpoint products.
example : intervalMul (-3,2) (-5,7) = (-21,15) := by decide +kernel
example : polynomialBounds 16 (0,1) [-2,1] = (-2,-1) := by decide +kernel
example : logBounds 1 8 53 = (0,0) := by decide +kernel
-- Divergent majorants cannot be used as tail bounds.
example : polynomialTailBound 1 3 8 = none := by decide +kernel
example : derivativeInfiniteTail 0 53 8 = none := by decide +kernel
example : derivativeInfiniteTail (1/100) 53 8 = none := by decide +kernel
