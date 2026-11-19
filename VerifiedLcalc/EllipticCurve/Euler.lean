module

public import VerifiedLcalc.EllipticCurve.Arithmetic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open PowerSeries

/-- Mathematical generating series of the executable local coefficient routine. -/
noncomputable def localSeries (a q : Int) : PowerSeries Int :=
  PowerSeries.mk (localCoefficient a q)

theorem localSeries_correct (a q : Int) (n : Nat) :
    PowerSeries.coeff n (localSeries a q) = localCoefficient a q n := by
  simp [localSeries]

/-- The coefficients really invert the quadratic Euler polynomial, not merely
satisfy an implementation-specific recurrence. q=0 also gives linear factors. -/
theorem localSeries_inverse (a q : Int) :
    (1 - C a * X + C q * X ^ 2) * localSeries a q = 1 := by
  have heq : (1 - C a * X + C q * X ^ 2) * localSeries a q =
      localSeries a q - C a * (X * localSeries a q) +
        C q * (X * (X * localSeries a q)) := by ring
  rw [heq]
  ext n
  cases n with
  | zero => simp [localSeries, localCoefficient, localPair]
  | succ n =>
    cases n with
    | zero => simp [localSeries, localCoefficient, localPair]
    | succ n =>
      simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, localSeries_correct,
        coeff_one, Nat.succ_ne_zero, ↓reduceIte]
      change localCoefficient a q (n + 2) - a * localCoefficient a q (n + 1) +
        q * localCoefficient a q n = 0
      rw [(localCoefficient_correct a q).2.2 n]
      ring

end VerifiedLcalc.EllipticCurve
