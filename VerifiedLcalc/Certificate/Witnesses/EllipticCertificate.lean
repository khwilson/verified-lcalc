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

/-! # Proof attachments and checked elliptic-curve certificates

* `IntegralCurveProofs` extends the equation invariant proofs with optional Mordell–Weil rank
  bounds over ℚ, exhaustive integral abscissa support, complete isogeny class evidence, and
  proofs of the real period, Tamagawa product, and analytic BSD quotient for the given equation.
* `EllipticCertificate` is the checked result indexed by the supplied integral equation and
  exported as `Name.certificate`. It carries nonsingularity, equation and rational invariants,
  algebraic, arithmetic, analytic, torsion and isogeny facts.
-/

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
  /-- Proof of the complete isogeny class and, optionally, its native LMFDB ordering. -/
  isogenyClass : Option (IsogenyClassEvidence curve) := none
  /-- Evidence of strict torsion growth in the field presented by the submitted polynomial. -/
  torsionGrowthField : Option (TorsionGrowthFieldFact curve) := none
  /-- A proved height enclosure indexed by its ordered rational point list. -/
  canonicalHeights : Option (Σ source : AffineMembership (curve.baseChange ℚ),
    CanonicalHeightFacts source) := none
  /-- Proved enclosure for the full minimal real period. -/
  realPeriod : Option (RealPeriodFact curve) := none
  /-- Proved product of all intrinsic finite-place Tamagawa numbers. -/
  tamagawaProduct : Option (TamagawaProductFact curve) := none
  /-- Proved enclosure for the analytic BSD quotient under explicit realizations. -/
  analyticSha : Option (AnalyticShaFact curve) := none

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
  /-- The checked field presentation and absolute degree for one torsion growth row. -/
  torsionGrowthField : Option (TorsionGrowthFieldFact curve) := none
  /-- A checked oriented rational isogeny edge and its integral target. -/
  isogeny : Option (Σ target : WeierstrassCurve ℤ, DegreeTwoIsogenyFact curve target) := none
  /-- The complete isogeny class with derived summaries and optional native LMFDB ordering. -/
  isogenyClass : Option (Σ facts : IsogenyClassFacts curve,
    Option (IsogenyClassOrdering facts.representatives)) := none
  /-- Checked full real period enclosure. -/
  realPeriod : Option (RealPeriodFact curve) := none
  /-- Checked product of the intrinsic finite-place Tamagawa numbers. -/
  tamagawaProduct : Option (TamagawaProductFact curve) := none
  /-- Checked analytic BSD quotient enclosure under explicit modular realizations. -/
  analyticSha : Option (AnalyticShaFact curve) := none
  /-- Checked rounded analytic quotient and any verified prime support. -/
  roundedAnalyticSha : Option (RoundedAnalyticShaFact curve) := none

end VerifiedLcalc
