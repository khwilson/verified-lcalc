module

public import VerifiedLcalc.EllipticCurve.Central
public import VerifiedLcalc.EllipticCurve.Examples

@[expose] public section

namespace VerifiedLcalc.EllipticCurve.Examples

example : primeExponent 2 72 = 3 ∧ primeExponent 3 72 = 2 ∧ primeExponent 5 72 = 0 := by
  decide +kernel

/-- Includes mixed-prime coefficients, prime powers and the singular prime 11.
The equation's bad factor still needs minimality to identify the actual Euler factor. -/
theorem curve11_coefficient_prefix :
    modelCoefficients curve11 12 = [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2] := by
  decide +kernel

example : evaluateCentral curve11 0 1 8 = none := by decide +kernel
example : evaluateCentral curve11 11 0 8 = none := by decide +kernel
example : squareTailBound 1 8 = none := by decide +kernel
example : squareTailBound (-1) 8 = none := by decide +kernel

/-- The negative-sign central expression is identically zero; it says nothing
about the first derivative or the truth of a supplied root number. -/
theorem negative_sign_finite (coefficients : List Int) (alpha : ℝ) :
    centralFiniteValue coefficients (-1) alpha = 0 := by
  simp [centralFiniteValue]

end VerifiedLcalc.EllipticCurve.Examples
