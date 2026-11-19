module

public import VerifiedLcalc.EllipticCurve.SemistableArithmetic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.ArithmeticExamples

def curve14 : Artifacts.CurveEquation := ⟨1, 0, 1, -11, 12⟩
def curve17 : Artifacts.CurveEquation := ⟨1, -1, 1, -6, -4⟩

/-- A bad prime in characteristic two: the actual linear Euler factor gives
coefficient a_4=1. This uses no modularity assumption. -/
theorem curve14_bad_two : goodReduction curve14 2 = false := by decide +kernel

theorem curve14_coefficient_four : (weierstrass curve14 ℚ).LFunction 4 = 1 := by
  have h := semistable_primePower curve14 (by decide +kernel) (by decide +kernel)
    2 (by decide) 2
  have hc : localCoefficient (modelFactor curve14 2).trace (modelFactor curve14 2).quadratic 2 = 1 := by
    decide +kernel
  simpa only [show 2 ^ 2 = (4 : ℕ) by decide, hc] using h

/-- A good prime with trace -1: the actual quadratic Euler factor gives
coefficient a_4=-1. The previous trace-size shortcut could not prove this. -/
theorem curve17_good_two : goodReduction curve17 2 = true := by decide +kernel

theorem curve17_coefficient_four : (weierstrass curve17 ℚ).LFunction 4 = -1 := by
  have h := semistable_primePower curve17 (by decide +kernel) (by decide +kernel)
    2 (by decide) 2
  have hc : localCoefficient (modelFactor curve17 2).trace (modelFactor curve17 2).quadratic 2 = -1 := by
    decide +kernel
  simpa only [show 2 ^ 2 = (4 : ℕ) by decide, hc] using h

end VerifiedLcalc.EllipticCurve.ArithmeticExamples
