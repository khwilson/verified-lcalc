module

public import VerifiedLcalc.EllipticCurve.Arithmetic
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open PowerSeries

/-- The coefficients really invert the quadratic Euler polynomial, not merely
satisfy an implementation-specific recurrence. q=0 also gives linear factors. -/
private theorem quadratic_mul_coefficient_series (a q : Int) :
    (1 - C a * X + C q * X ^ 2) * (PowerSeries.mk (localCoefficient a q)) = 1 := by
  have heq : (1 - C a * X + C q * X ^ 2) * (PowerSeries.mk (localCoefficient a q)) =
      (PowerSeries.mk (localCoefficient a q)) - C a * (X * (PowerSeries.mk (localCoefficient a q))) +
        C q * (X * (X * (PowerSeries.mk (localCoefficient a q)))) := by ring
  rw [heq]
  ext n
  cases n with
  | zero => simp [localCoefficient, localPair]
  | succ n =>
    cases n with
    | zero => simp [localCoefficient, localPair]
    | succ n =>
      simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, PowerSeries.coeff_mk,
        coeff_one, Nat.succ_ne_zero, ↓reduceIte]
      change localCoefficient a q (n + 2) - a * localCoefficient a q (n + 1) +
        q * localCoefficient a q n = 0
      rw [localCoefficient_recurrence a q n]
      ring

/-- The executable recurrence computes coefficients of Mathlib's canonical
inverse quadratic Euler polynomial. No separate inverse-series definition. -/
theorem localCoefficient_eq_coeff_invOfUnit (a q : Int) (n : Nat) :
    localCoefficient a q n = PowerSeries.coeff n
      (PowerSeries.invOfUnit (1 - C a * X + C q * X ^ 2) 1) := by
  have he : PowerSeries.mk (localCoefficient a q) =
      PowerSeries.invOfUnit (1 - C a * X + C q * X ^ 2) 1 :=
    (left_inv_eq_right_inv (a := 1 - C a * X + C q * X ^ 2)
      (PowerSeries.invOfUnit_mul _ 1 (by simp)) (quadratic_mul_coefficient_series a q)).symm
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) he

end VerifiedLcalc.EllipticCurve
