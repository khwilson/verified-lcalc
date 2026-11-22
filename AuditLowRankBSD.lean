import VerifiedLcalc.Certification.LowRankBSD
import VerifiedLcalc.EllipticCurve.AlgebraicRank

-- These conclusions depend on the one isolated forward implication assumption.
#print axioms VerifiedLcalc.Certification.algebraic_finrank_of_conditional_analytic_rank
#print axioms VerifiedLcalc.Certification.algebraic_finrank_eq_zero_of_analytic_rank_zero
#print axioms VerifiedLcalc.Certification.algebraic_finrank_eq_one_of_analytic_rank_one

-- Independent finite rank proofs retain their standard-only audit.
#print axioms VerifiedLcalc.EllipticCurve.algebraic_finrank_lower_bound
