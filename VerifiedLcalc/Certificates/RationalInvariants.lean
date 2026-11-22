/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.CurveWitness
public import Mathlib.RingTheory.Localization.Rat
public import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality

/-! # Mathematical rational invariants of an integral equation

These contracts state equalities and properties of Mathlib/TauCeti invariants.
The finite abc transcript checks and their soundness proofs live under
`Certification`.
-/

@[expose] public section

namespace VerifiedLcalc

/-- A factorization transcript and enclosure for the actual abc quality. -/
structure AbcQualityFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The submitted rational report and factor list. -/
  claim : AbcQualityClaim
  /-- The domain condition for TauCeti's abc quality. -/
  defined : (curve.baseChange ℚ).j ≠ 0 ∧ (curve.baseChange ℚ).j ≠ 1728
  /-- The supplied factors multiply to the reduced abc product of `j / 1728`. -/
  factorization :
    let t := (curve.baseChange ℚ).j / 1728
    let c : ℤ := t.den
    claim.factors.prod = (t.num * (c - t.num) * c).natAbs
  /-- Every supplied factor is prime. -/
  primeFactors : ∀ p ∈ claim.factors, p.Prime
  /-- The actual TauCeti quality lies within the claimed absolute error. -/
  within_error :
    |(curve.baseChange ℚ).abcQuality defined - (claim.reported : ℝ)| ≤
      (claim.error : ℝ)

/-- Rational invariant facts whose conclusions directly name mathematical objects. -/
structure RationalInvariantFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The sign of the integral equation's discriminant. -/
  discriminantSign : Option { s : ℤ // curve.Δ.sign = s } := none
  /-- The j-invariant of the rational curve. -/
  jInvariant : Option { j : ℚ // (curve.baseChange ℚ).j = j } := none
  /-- The truth value for integrality of the rational j-invariant. -/
  jIntegral : Option { b : Bool //
    IsLocalization.IsInteger ℤ (curve.baseChange ℚ).j ↔ b = true } := none
  /-- The checked abc-quality enclosure. -/
  abcQuality : Option (AbcQualityFacts curve) := none

end VerifiedLcalc
