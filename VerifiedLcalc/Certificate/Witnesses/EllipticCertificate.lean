/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
public import VerifiedLcalc.Certificate.Witnesses.RationalInvariants
public import VerifiedLcalc.Certificate.Witnesses.PointFacts
public import VerifiedLcalc.Certificate.PointAccessors
public import VerifiedLcalc.Certificate.Witnesses.ArithmeticFacts
public import VerifiedLcalc.Certificate.Witnesses.AnalyticFacts
public import VerifiedLcalc.Certificate.Witnesses.Torsion
public import VerifiedLcalc.Certificate.Witnesses.DegreeTwoIsogeny
public import VerifiedLcalc.Certificate.Witnesses.IntegralPoints
public import VerifiedLcalc.Certificate.Witnesses.AlgebraicRank
public import VerifiedLcalc.Certificate.Witnesses.Regulator

/-! # The public checked elliptic certificate structures -/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

/-- Checked point lists, individual orders and algebraic lower bounds. -/
structure AlgebraicFacts (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- Membership on the supplied integral equation. -/
  integralPoints : Option (AffineMembership curve) := none
  /-- Complete integral y-fibers at the specified integral x-coordinates. -/
  integralYFibers : Option (IntegralYFiberFacts curve) := none
  /-- Exhaustive finite set and exact cardinality of all affine integral points. -/
  completeIntegralPoints : Option (CompleteIntegralPointFacts curve) := none
  /-- Membership for the supplied rational generator coordinates. -/
  generators : Option (AffineMembership (curve.baseChange ℚ)) := none
  /-- The checked `ngens` count for the supplied generator coordinates. -/
  generatorCount : Option (GeneratorCountFacts
    (generators.getD (AffineMembership.empty (curve.baseChange ℚ))).coordinates) := none
  /-- Membership for the supplied rational torsion generator coordinates. -/
  torsionGenerators : Option (AffineMembership (curve.baseChange ℚ)) := none
  /-- Exact orders of the listed torsion generators, when supplied and checked. -/
  torsionGeneratorOrders : Option (TorsionGeneratorOrderFacts
    (torsionGenerators.getD (AffineMembership.empty (curve.baseChange ℚ)))) := none
  /-- The supplied indexed points checked for infinite order. -/
  infiniteOrderPoints : Option
    (List (InfiniteOrderPointFact (integralPoints.getD (AffineMembership.empty curve)))) := none
  /-- The supplied family checked for integer independence. -/
  independentPoints : Option
    (IndependentPointFacts (integralPoints.getD (AffineMembership.empty curve))) := none
  /-- A proved lower bound for the rational Mordell–Weil rank. -/
  rankLowerBound : Option { n : ℕ //
    n ≤ Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point } := none
  /-- A proved lower and upper bound for the actual rational point group rank. -/
  rankBounds : Option (AlgebraicRankBounds (curve.baseChange ℚ)) := none
  /-- An exact algebraic Mordell–Weil rank, when the checked interval is a singleton. -/
  rank : Option { n : ℕ //
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = n } := none
  /-- A stored regulator enclosure checked from an exact algebraic rank of zero. -/
  regulator : Option (RegulatorFacts (curve.baseChange ℚ)) := none
/-- The family-indexed certificate exported by the verification command. -/
structure EllipticCertificate (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Nonsingularity of the supplied integral equation. -/
  nonsingular : curve.Δ ≠ 0
  /-- Checked ring-valued invariants about the fixed equation. -/
  equationFacts : EllipticProofs curve
  /-- Checked integral or rational invariants. -/
  rational : RationalInvariantFacts curve
  /-- Checked points and algebraic lower bounds. -/
  algebraic : AlgebraicFacts curve
  /-- Checked arithmetic facts, including explicit-realization conditional facts. -/
  arithmetic : ArithmeticFacts curve
  /-- Checked numerical data and explicit-realization analytic results. -/
  analytic : AnalyticFacts curve
  /-- The checked full-group torsion facts. -/
  torsion : TorsionFacts curve
  /-- A checked oriented rational isogeny edge and its integral target. -/
  isogeny : Option (Σ target : WeierstrassCurve ℤ, DegreeTwoIsogenyFact curve target) := none

end VerifiedLcalc
