module

public import VerifiedLcalc.EllipticCurve.Correctness
public import VerifiedLcalc.EllipticCurve.Euler
public import VerifiedLcalcTests.Arithmetic.Examples

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.Curve11Arithmetic
open VerifiedLcalc.EllipticCurve VerifiedLcalc.EllipticCurve.Examples

/-- First real-curve arithmetic certificate: the actual mathlib point type has
five points over F₂. This is a point-count certificate, not an analytic rank. -/
theorem point_count_two :
    Nat.card (WeierstrassCurve.baseChange curve11 (ZMod 2)).toAffine.Point = 5 :=
  (analysePrime_sound curve11 2 ⟨2, 5, -2⟩ curve11_at_two).2.2.1.symm

/-- The corresponding good Euler factor is 1 + 2T + 2T². -/
theorem trace_two :
    (2 : Int) + 1 - Nat.card (WeierstrassCurve.baseChange curve11 (ZMod 2)).toAffine.Point = -2 :=
  (analysePrime_sound curve11 2 ⟨2, 5, -2⟩ curve11_at_two).2.2.2.symm

/-- The computed prime-power coefficients belong to Mathlib's inverse Euler polynomial. -/
theorem euler_factor_two (k : ℕ) :
    localCoefficient (-2) 2 k = PowerSeries.coeff k
      (PowerSeries.invOfUnit
        (1 - PowerSeries.C (-2 : Int) * PowerSeries.X + PowerSeries.C (2 : Int) * PowerSeries.X ^ 2) 1) :=
  localCoefficient_eq_coeff_invOfUnit (-2) 2 k

end VerifiedLcalcTests.Fixtures.Curve11Arithmetic
