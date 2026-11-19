module

public import VerifiedLcalc.EllipticCurve.Correctness
public import VerifiedLcalc.EllipticCurve.Euler
public import VerifiedLcalc.EllipticCurve.Examples

@[expose] public section

namespace VerifiedLcalc.Certificates.Curve11Arithmetic
open VerifiedLcalc.EllipticCurve VerifiedLcalc.EllipticCurve.Examples

/-- First real-curve arithmetic certificate: the actual mathlib point type has
five points over F₂. This is a point-count certificate, not an analytic rank. -/
theorem point_count_two :
    Nat.card (weierstrass curve11 (ZMod 2)).toAffine.Point = 5 :=
  (analysePrime_sound curve11 2 ⟨2, 5, -2⟩ curve11_at_two).2.2.1.symm

/-- The corresponding good Euler factor is 1 + 2T + 2T². -/
theorem trace_two :
    (2 : Int) + 1 - Nat.card (weierstrass curve11 (ZMod 2)).toAffine.Point = -2 :=
  (analysePrime_sound curve11 2 ⟨2, 5, -2⟩ curve11_at_two).2.2.2.symm

/-- The computed prime-power coefficients invert that exact Euler factor. -/
theorem euler_factor_two :
    (1 - PowerSeries.C (-2 : Int) * PowerSeries.X + PowerSeries.C (2 : Int) * PowerSeries.X ^ 2) *
      localSeries (-2) 2 = 1 := localSeries_inverse (-2) 2

end VerifiedLcalc.Certificates.Curve11Arithmetic
