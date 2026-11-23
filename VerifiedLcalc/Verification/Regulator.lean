module

public import VerifiedLcalc.Certificate.Support.Regulator
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

/-! # Rank-zero regulator verification -/

@[expose] public section

namespace VerifiedLcalc.Certification

/-- Check that a stored regulator and its explicit absolute error contain one.
When the error is absent, the report is treated as an exact value. -/
def rankZeroRegulatorValid (reported : Rat) (error : Option Rat) : Bool :=
  let bound := error.getD 0
  decide (0 ≤ bound ∧ |(1 : Rat) - reported| ≤ bound)

/-- A zero rank of the rational point module gives regulator one. -/
theorem regulator_eq_one_of_finrank_eq_zero (W : WeierstrassCurve ℚ)
    [W.toAffine.IsElliptic] (h : Module.finrank ℤ W.toAffine.Point = 0) :
    W.toAffine.regulator = 1 := by
  have hquot : Module.finrank ℤ
      (WeierstrassCurve.Affine.PointModTorsion W.toAffine) = 0 := by
    rw [finrank_quotient_eq_of_le_torsion le_rfl]
    exact h
  exact WeierstrassCurve.Affine.regulator_eq_one_of_finrank_eq_zero
    (W := W.toAffine) hquot

/-- A rational report check gives an enclosure of the actual regulator. -/
theorem regulator_within_error_of_valid (W : WeierstrassCurve ℚ)
    [W.toAffine.IsElliptic] (reported error : Rat)
    (hreg : W.toAffine.regulator = 1)
    (h : decide (0 ≤ error ∧ |(1 : Rat) - reported| ≤ error) = true) :
    |W.toAffine.regulator - (reported : ℝ)| ≤ (error : ℝ) := by
  rw [hreg]
  have h' : |(1 : Rat) - reported| ≤ error := (of_decide_eq_true h).2
  exact_mod_cast h'

/-- Construct regulator facts when the checked algebraic rank is zero. -/
def rankZeroRegulatorFacts (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic]
    (claim : RegulatorClaim) (hzero : Module.finrank ℤ W.toAffine.Point = 0)
    (hvalid : rankZeroRegulatorValid claim.reported claim.error = true) :
    RegulatorFacts W := by
  let error := claim.error.getD 0
  have hvalid' : decide (0 ≤ error ∧ |(1 : Rat) - claim.reported| ≤ error) = true := by
    simpa [rankZeroRegulatorValid, error] using hvalid
  have hcheck : 0 ≤ error ∧ |(1 : Rat) - claim.reported| ≤ error :=
    of_decide_eq_true hvalid'
  have hreg := regulator_eq_one_of_finrank_eq_zero W hzero
  refine ⟨claim.reported, error, hcheck.1, ?_, some ⟨1, hreg⟩⟩
  exact regulator_within_error_of_valid W claim.reported error hreg hvalid'

end VerifiedLcalc.Certification
