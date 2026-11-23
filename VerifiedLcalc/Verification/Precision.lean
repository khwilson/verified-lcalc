module

public import VerifiedLcalc.Assumptions.Precision
public import VerifiedLcalc.Verification.NumericalCertification
public import VerifiedLcalc.NumericalRankSeparation

/-!
# Conditional numerical rank certification

The results here combine checked derivative enclosures with explicit curve
hypotheses. A lower bound follows from the separated gap; exact rank also
requires the next derivative to be nonzero.
-/

@[expose] public section
open VerifiedLcalc.Certification
namespace VerifiedLcalc.Assumptions
open Modularity Certification

/-- Derivatives below the cutoff give a lower rank bound under the stated gap hypothesis. -/
theorem CurvePrecisionClaim.conditional_lower_bound (claim : CurvePrecisionClaim)
    (hn : claim.equation.Δ ≠ 0)
    (hypotheses : claim.Hypotheses hn)
    (small : NumericalRanks.SmallDerivatives (modularWitness claim.equation hn).formL 1
      claim.derivativeCount claim.policy.cutoff) :
    (claim.derivativeCount : ℕ∞) ≤
      analyticOrderAt (modularWitness claim.equation hn).formL 1 := by
  exact NumericalRanks.lowerBound_of_small_gap
    ((modularWitness claim.equation hn).formL_differentiable.analyticAt 1)
    small hypotheses.separated hypotheses.cutoff_lt_gap

/-- The derivative gap and a nonzero next derivative determine the exact analytic rank. -/
theorem CurvePrecisionClaim.conditional_rank (claim : CurvePrecisionClaim)
    (hn : claim.equation.Δ ≠ 0)
    (hypotheses : claim.Hypotheses hn)
    (small : NumericalRanks.SmallDerivatives (modularWitness claim.equation hn).formL 1
      claim.derivativeCount claim.policy.cutoff)
    (next_nonzero : iteratedDeriv claim.derivativeCount
      (modularWitness claim.equation hn).formL 1 ≠ 0) :
    analyticOrderAt (modularWitness claim.equation hn).formL 1 = claim.derivativeCount := by
  exact NumericalRanks.rank_eq_of_small_gap
    ((modularWitness claim.equation hn).formL_differentiable.analyticAt 1)
    small hypotheses.separated hypotheses.cutoff_lt_gap next_nonzero

/-- Build the claim identity from the actual saved numerical evidence, not from
an unrelated label or caller-supplied rank. The gap remains an explicit input. -/
def CurvePrecisionClaim.ofEvidence {expected : NumericalRanks.Request}
    {artifact : NumericalRanks.Artifact} (e : AssumedNumericalEvidence expected artifact)
    (gap : Rat) : CurvePrecisionClaim :=
  ⟨e.equation, expected.policy, artifact.numericalLowerBound, gap⟩

/-- The precision claim records the supplied equation, policy, derivative count and gap. -/
theorem CurvePrecisionClaim.ofEvidence_correct {expected : NumericalRanks.Request}
    {artifact : NumericalRanks.Artifact} (e : AssumedNumericalEvidence expected artifact)
    (gap : Rat) :
    (ofEvidence e gap).equation = e.equation ∧
    (ofEvidence e gap).policy = expected.policy ∧
    (ofEvidence e gap).derivativeCount = artifact.numericalLowerBound ∧
    (ofEvidence e gap).nonzeroGap = gap := ⟨rfl, rfl, rfl, rfl⟩

/-- Connect the explicit curve hypothesis record to a checked numerical artifact.
Actual derivative enclosures are still required by `AssumedNumericalEvidence`. -/
theorem check_numerical_with_curve_hypotheses {expected : NumericalRanks.Request}
    {artifact : NumericalRanks.Artifact} (e : AssumedNumericalEvidence expected artifact)
    (checked : NumericalRanks.check expected artifact = true) (gap : Rat)
    (hypotheses : (CurvePrecisionClaim.ofEvidence e gap).Hypotheses e.nonsingular) :
    (artifact.numericalLowerBound : ℕ∞) ≤
      analyticOrderAt (modularWitness e.equation e.nonsingular).formL 1 := by
  apply check_assumed_numerical_lowerBound e checked
  exact NumericalRanks.exactVanishing_of_gap hypotheses.separated hypotheses.cutoff_lt_gap

end VerifiedLcalc.Assumptions
