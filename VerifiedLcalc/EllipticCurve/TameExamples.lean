module
public import VerifiedLcalc.EllipticCurve.TameArithmetic
@[expose] public section
namespace VerifiedLcalc.EllipticCurve.TameExamples
set_option maxRecDepth 100000

-- j=0 must not be classified as potentially multiplicative merely because
-- Nat.factorization assigns zero to the zero integer.
def jZero : Artifacts.CurveEquation := ⟨0, 0, 0, 0, 25⟩
theorem jZero_guard : potentiallyMultiplicative jZero 5 = false := by decide +kernel
theorem jZero_local : localConductorRoot? jZero 5 = some ⟨5, 2, -1⟩ := by decide +kernel
-- Wild additive cases are refused, even if a tame formula could return a number.
theorem wild_two : localConductorRoot? jZero 2 = none := by decide +kernel
theorem wild_three : localConductorRoot? jZero 3 = none := by decide +kernel
theorem composite : localConductorRoot? jZero 9 = none := by decide +kernel
-- Exercise both exceptional potentially-good residue classes and both signs.
theorem symbols : legendreValue 5 (-2) = -1 ∧ legendreValue 7 (-3) = 1 ∧
    legendreValue 7 (-1) = -1 ∧ legendreValue 7 0 = 0 := by decide +kernel
theorem additive_residue_classes :
    tameAdditiveRoot ⟨0, 0, 0, 7, 0⟩ 7 = -1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 0, 7⟩ 7 = -1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 0, 49⟩ 7 = 1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 49, 0⟩ 7 = -1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 343, 0⟩ 7 = -1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 0, 2401⟩ 7 = 1 ∧
    tameAdditiveRoot ⟨0, 0, 0, 0, 16807⟩ 7 = -1 := by decide +kernel

theorem negative_j : potentiallyMultiplicative ⟨0, 0, 0, -75, 875⟩ 5 = true ∧
    localConductorRoot? ⟨0, 0, 0, -75, 875⟩ 5 = some ⟨5, 2, 1⟩ := by decide +kernel

-- Global products recover the conductor and sign from the equation itself.
-- Wrong input metadata cannot satisfy these finite certificate obligations.
def curve49 : Artifacts.CurveEquation := ⟨1, -1, 0, -1822, 30393⟩
theorem curve49_products : tameLevelFast curve49 = 49 ∧ tameSignFast curve49 = 1 := by
  decide +kernel
theorem wrong_conductor_rejected : tameLevelFast curve49 ≠ 48 := by decide +kernel
theorem wrong_sign_rejected : tameSignFast curve49 ≠ -1 := by decide +kernel
end VerifiedLcalc.EllipticCurve.TameExamples
