import VerifiedLcalc.Certificate.CheckedElliptic

/-! The backend compatibility theorem reconstructs the historical Boolean check. -/

example {curve : WeierstrassCurve ℤ} (facts : VerifiedLcalc.TorsionDivisorFacts curve) :
    VerifiedLcalc.EllipticCurve.checkTorsionBound curve facts.evidence.firstPrime
      facts.evidence.secondPrime facts.evidence.bound = true :=
  facts.checked
