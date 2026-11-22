import VerifiedLcalc
import Lean

/-! # Default import isolation check -/

open Lean Elab Command

-- The default public import does not activate the temporary implication.
run_cmd do
  for name in [
      `VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank,
      `VerifiedLcalc.Certification.algebraic_finrank_of_conditional_analytic_rank,
      `VerifiedLcalc.Certification.algebraic_finrank_eq_zero_of_analytic_rank_zero,
      `VerifiedLcalc.Certification.algebraic_finrank_eq_one_of_analytic_rank_one] do
    if (← getEnv).contains name then
      throwError "Opt-in low-rank BSD declaration leaked into the default imports: {name}"
