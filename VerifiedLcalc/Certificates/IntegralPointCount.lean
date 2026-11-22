/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.IntegralXSupport
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

/-! # Complete integral-point count facts -/

@[expose] public section

namespace VerifiedLcalc

/-- Complete integral coordinates and their exact affine integral-point count. -/
structure CompleteIntegralPointFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Reusable evidence for exhaustive abscissa support on the same model. -/
  support : IntegralXSupport curve
  /-- The distinct integral solutions, excluding the point at infinity. -/
  coordinates : Finset (ℤ × ℤ)
  /-- Membership is equivalent to satisfying the integral equation. -/
  complete : ∀ p : ℤ × ℤ, p ∈ coordinates ↔ curve.toAffine.Equation p.1 p.2
  /-- The exact number of affine integral points. -/
  count : ℕ
  /-- The checked count is the cardinality of the finite coordinate set. -/
  coordinates_card : coordinates.card = count
  /-- The affine integral points form a finite set, including when the count is zero. -/
  finite : Finite curve.integralPoints
  /-- The checked count is the cardinality in the rational point group. -/
  integralPoints_card : Nat.card curve.integralPoints = count

end VerifiedLcalc
