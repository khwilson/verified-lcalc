module

public import VerifiedLcalc.Certification.DegreeTwoIsogeny
public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Certification.CurveData
public import VerifiedLcalc.Certification.IntegralPointCount
public import VerifiedLcalc.Certification.TorsionBoundFacts
public import VerifiedLcalc.Certificate.ArithmeticFacts
public import VerifiedLcalc.Certificates.RationalInvariants
public import VerifiedLcalc.Certificates.PointFacts
public import VerifiedLcalc.Certificates.TorsionFacts
public import VerifiedLcalc.Certification.AbcQuality
public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.Certificates.Regulator
public import VerifiedLcalc.Certificates.AlgebraicRank
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
