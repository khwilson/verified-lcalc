import VerifiedLcalc.Certification.LowRankBSD
import VerifiedLcalcTests.Fixtures.AssumedCurve11Central
import CertifiedCurves

/-! # Opt-in low-rank implication consumer -/

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

/-- An exact rank-one certificate from the checked LMFDB catalogue also feeds
the theorem only through its typed analytic-rank witness and same-curve
arithmetic realization. -/
noncomputable def curve112RankFact : ConditionalAnalyticRank Curve112.curve :=
  Curve112.certificate.analytic.rank.get (by decide)

noncomputable def curve112Realization : ArithmeticModularRealization Curve112.curve :=
  arithmeticModularWitness Curve112.curve Curve112.nonsingular

theorem curve112_algebraic_rank_one :
    Module.finrank ℤ (Curve112.curve.baseChange ℚ).toAffine.Point = 1 :=
  Certification.algebraic_finrank_eq_one_of_analytic_rank_one Curve112.nonsingular
    curve112RankFact curve112Realization (by decide)

/-- A rank-one exact analytic fact is consumed with a realization of the same
equation; raw catalog or interval data do not have this input type. -/
example {curve : WeierstrassCurve ℤ} (hn : curve.Δ ≠ 0)
    (m : ArithmeticModularRealization curve) (fact : ConditionalAnalyticRank curve)
    (h : fact.val = 1) :
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 1 :=
  Certification.algebraic_finrank_eq_one_of_analytic_rank_one hn fact m h

end LowRankBSDConsumer
