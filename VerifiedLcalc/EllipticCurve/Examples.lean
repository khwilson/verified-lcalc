module

public import VerifiedLcalc.EllipticCurve.Arithmetic

@[expose] public section

namespace VerifiedLcalc.EllipticCurve.Examples

def curve11 : Artifacts.CurveEquation := ⟨0, -1, 1, -10, -20⟩

-- Concrete computations of the curve's arithmetic, independent of its rank.
theorem curve11_discriminant : discriminant curve11 = -161051 := by decide

theorem curve11_at_two : analysePrime curve11 2 = some ⟨2, 5, -2⟩ := by decide
theorem curve11_at_three : analysePrime curve11 3 = some ⟨3, 5, -1⟩ := by decide
theorem curve11_at_five : analysePrime curve11 5 = some ⟨5, 5, 1⟩ := by decide
theorem curve11_at_seven : analysePrime curve11 7 = some ⟨7, 10, -2⟩ := by decide

-- A bad prime, composite, degenerate input, and characteristic edge cases.
example : analysePrime curve11 11 = none := by decide
example : analysePrime curve11 9 = none := by decide
example : analysePrime curve11 0 = none := by decide
example : analysePrime curve11 1 = none := by decide
example : analysePrime ⟨0, 0, 0, 0, 0⟩ 5 = none := by decide

-- a_(2^k) and a_(3^k) agree with the inverse good Euler factors.
example : (List.range 5).map (localCoefficient (-2) 2) = [1, -2, 2, 0, -4] := by decide
example : (List.range 4).map (localCoefficient (-1) 3) = [1, -1, -2, 5] := by decide
-- The same proved recurrence handles the three possible linear bad factors
-- once a future minimal-model backend has proved the local factor's type.
example : (List.range 4).map (localCoefficient 1 0) = [1, 1, 1, 1] := by decide
example : (List.range 4).map (localCoefficient (-1) 0) = [1, -1, 1, -1] := by decide
example : (List.range 4).map (localCoefficient 0 0) = [1, 0, 0, 0] := by decide

end VerifiedLcalc.EllipticCurve.Examples
