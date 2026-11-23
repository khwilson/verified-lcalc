module

public import VerifiedLcalc.Verification.DegreeTwoIsogeny
public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Verification.CurveData
public import VerifiedLcalc.Verification.IntegralPointCount
public import VerifiedLcalc.Verification.TorsionBoundFacts
public import VerifiedLcalc.Certificate.ArithmeticFacts
public import VerifiedLcalc.Certificate.Witnesses.RationalInvariants
public import VerifiedLcalc.Certificate.Support.Points
public import VerifiedLcalc.Certificate.Support.Torsion
public import VerifiedLcalc.Verification.AbcQuality
public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.Certificate.Support.Regulator
public import VerifiedLcalc.Certificate.Support.AlgebraicRank
public import VerifiedLcalc.EllipticCurve.PointIndependence
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Data.Nat.Factors

/-!
# Checked data for one integral Weierstrass equation

An optional field is present when its corresponding evidence has been checked.
A membership certificate attests the supplied points. An algebraic rank bound
and a proof of independence carry their stated lower-bound conclusions.
-/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

/-- The integral Weierstrass equation indexing the whole certificate. -/
def EllipticCertificate.equation {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (_ : EllipticCertificate curve) : WeierstrassCurve ℤ :=
  curve

end VerifiedLcalc
