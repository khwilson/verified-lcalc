/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-! # Regulator claim and enclosure data -/

@[expose] public section

namespace VerifiedLcalc

/-- A stored regulator decimal and optional explicit absolute-error evidence. -/
structure RegulatorClaim where
  /-- Exact rational interpretation of the stored decimal. -/
  reported : Rat
  /-- Explicit absolute error bound; absence means an exact-value claim. -/
  error : Option Rat := none

/-- A mathematically proved enclosure for an elliptic-curve regulator. -/
structure RegulatorFacts (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic] where
  /-- The center of the reported enclosure. -/
  reported : Rat
  /-- Its nonnegative absolute error radius. -/
  error : Rat
  /-- The error radius is nonnegative. -/
  error_nonneg : 0 ≤ error
  /-- TauCeti's regulator lies in the reported enclosure. -/
  within_error : |W.toAffine.regulator - (reported : ℝ)| ≤ (error : ℝ)
  /-- Optional exact rank-zero regulator value. -/
  exact_value : Option { value : ℝ // W.toAffine.regulator = value } := none

end VerifiedLcalc
