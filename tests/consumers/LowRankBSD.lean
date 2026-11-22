import VerifiedLcalc.Certification.LowRankBSD
import VerifiedLcalcTests.Fixtures.AssumedCurve11Central

open VerifiedLcalc
open VerifiedLcalc.EllipticCurve
open VerifiedLcalc.Modularity
open VerifiedLcalcTests.Fixtures

namespace LowRankBSDConsumer

noncomputable def curve11Realization : ArithmeticModularRealization
    VerifiedLcalc.EllipticCurve.Examples.curve11 :=
  arithmeticModularWitness VerifiedLcalc.EllipticCurve.Examples.curve11 (by decide)

/-- The exact central certificate supplies the analytic-order premise. -/
noncomputable def curve11RankFact : ConditionalAnalyticRank
    VerifiedLcalc.EllipticCurve.Examples.curve11 where
  val := 0
  correct := by
    intro m
    rw [m.toModularRealization.analyticOrder_eq AssumedCurve11.realization]
    exact AssumedCurve11Central.analytic_rank_zero

theorem curve11_algebraic_rank_zero :
    Module.finrank ℤ
        (VerifiedLcalc.EllipticCurve.Examples.curve11.baseChange ℚ).toAffine.Point = 0 :=
  Certification.algebraic_finrank_eq_zero_of_analytic_rank_zero
    (by decide) curve11RankFact curve11Realization rfl

/-- A rank-one exact analytic fact is consumed with a realization of the same
equation; raw catalog or interval data do not have this input type. -/
example {curve : WeierstrassCurve ℤ} (hn : curve.Δ ≠ 0)
    (m : ArithmeticModularRealization curve) (fact : ConditionalAnalyticRank curve)
    (h : fact.val = 1) :
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 1 :=
  Certification.algebraic_finrank_eq_one_of_analytic_rank_one hn fact m h

end LowRankBSDConsumer
