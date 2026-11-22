/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.AlgebraicRank
public import VerifiedLcalc.Certificate.Witnesses.AnalyticEvidence
public import VerifiedLcalc.Certificate.Witnesses.AnalyticFacts
public import VerifiedLcalc.Certificate.Witnesses.AnalyticRank
public import VerifiedLcalc.Certificate.Witnesses.ArithmeticCompatibility
public import VerifiedLcalc.Certificate.Witnesses.ArithmeticFacts
public import VerifiedLcalc.Certificate.Witnesses.ArtifactChecked
public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Witnesses.CentralSeriesEvidence
public import VerifiedLcalc.Certificate.Witnesses.CurvePrecisionClaim
public import VerifiedLcalc.Certificate.Witnesses.CurveProofs
public import VerifiedLcalc.Certificate.Witnesses.DegreeTwoIsogeny
public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
public import VerifiedLcalc.Certificate.Witnesses.Enclosures
public import VerifiedLcalc.Certificate.Witnesses.IntegralPoints
public import VerifiedLcalc.Certificate.Witnesses.LocalClaims
public import VerifiedLcalc.Certificate.Witnesses.NumericalData
public import VerifiedLcalc.Certificate.Witnesses.NumericalRankChecked
public import VerifiedLcalc.Certificate.Witnesses.NumericalRankData
public import VerifiedLcalc.Certificate.Witnesses.PointFacts
public import VerifiedLcalc.Certificate.Witnesses.PointMembership
public import VerifiedLcalc.Certificate.Witnesses.PrecisionPolicy
public import VerifiedLcalc.Certificate.Witnesses.RationalInvariants
public import VerifiedLcalc.Certificate.Witnesses.Regulator
public import VerifiedLcalc.Certificate.Witnesses.Scan
public import VerifiedLcalc.Certificate.Witnesses.SpecialValue
public import VerifiedLcalc.Certificate.Witnesses.Torsion
public import VerifiedLcalc.Certificate.Witnesses.Transcripts

/-!
# Certificate witness structures

`VerifiedLcalc.EllipticWitness` is the input to `certify_ec` and
`VerifiedLcalc.EllipticCertificate` is the type of its checked output.
The optional witnesses that refer to the modularity axiom have separate imports.
-/
