module

public import VerifiedLcalc.EllipticCurve.TorsionBound
public import TauCeti.AlgebraicGeometry.EllipticCurve.WorkedExamples

/-! # Rational torsion of 37.a1 from two finite-field point counts -/

public section

namespace VerifiedLcalcTests.TorsionBound

open VerifiedLcalc.EllipticCurve
open TauCeti.WorkedExamples (curve37a1)

example : computePointCount curve37a1 3 = 7 := by decide +kernel

example : computePointCount curve37a1 5 = 8 := by decide +kernel

example : checkTorsionBound curve37a1 2 5 1 = false := by decide +kernel

example : checkTorsionBound curve37a1 3 37 1 = false := by decide +kernel

example : checkTorsionBound curve37a1 3 5 2 = false := by decide +kernel

/-- The subgroup of rational torsion points of 37.a1 contains exactly one point. -/
theorem card_torsion_curve37a1 :
    Nat.card (AddCommGroup.torsion (curve37a1.baseChange ℚ).toAffine.Point) = 1 :=
  card_torsion_eq_one_of_checkTorsionBound curve37a1 3 5 (by decide +kernel)

end VerifiedLcalcTests.TorsionBound
