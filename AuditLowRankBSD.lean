import VerifiedLcalc.Certification.LowRankBSD
import VerifiedLcalc.EllipticCurve.AlgebraicRank

set_option linter.hashCommand false

-- These conclusions depend on the one isolated forward implication assumption.
/-- info: 'VerifiedLcalc.Certification.algebraic_finrank_of_conditional_analytic_rank' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.algebraic_finrank_of_conditional_analytic_rank
/-- info: 'VerifiedLcalc.Certification.algebraic_finrank_eq_zero_of_analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.algebraic_finrank_eq_zero_of_analytic_rank_zero
/-- info: 'VerifiedLcalc.Certification.algebraic_finrank_eq_one_of_analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.algebraic_finrank_eq_one_of_analytic_rank_one

-- Independent finite rank proofs retain their standard-only audit.
/-- info: 'VerifiedLcalc.EllipticCurve.algebraic_finrank_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.algebraic_finrank_lower_bound
