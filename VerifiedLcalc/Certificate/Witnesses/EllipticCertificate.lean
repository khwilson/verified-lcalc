/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes
public import VerifiedLcalc.Certificate.Witnesses.Invariants

/-! # Proof attachments and checked elliptic-curve certificates -/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve

/-- Lean proofs accepted alongside raw claims on an integral Weierstrass equation. -/
structure IntegralCurveProofs (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] extends EllipticProofs curve where
  /-- Proved endpoints of a Mordell–Weil rank interval on the rational curve. -/
  algebraicRank : Option (AlgebraicRankBounds (curve.baseChange ℚ)) := none
  /-- Exhaustive abscissa support for integral points on the supplied equation. -/
  integralXSupport : Option (IntegralXSupport curve) := none

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
