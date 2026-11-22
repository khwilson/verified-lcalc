/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree

/-! # Minimum-degree two-isogeny evidence -/

@[expose] public section

namespace VerifiedLcalc
open TauCeti

/-- A degree-two edge between the specified rational equations, with its minimum-degree proof. -/
structure DegreeTwoIsogenyFact (source target : WeierstrassCurve ℤ) where
  /-- Nonsingularity of the rational source curve. -/
  source_elliptic : (source.baseChange ℚ).IsElliptic
  /-- Nonsingularity of the rational target curve. -/
  target_elliptic : (target.baseChange ℚ).IsElliptic
  /-- Rational isogeny between the two supplied equations. -/
  isogeny : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine
  /-- The exhibited isogeny has degree two. -/
  degree_eq : isogeny.degree = 2
  /-- The rational kernel has both points and has cardinality two. -/
  kernel_card : letI := source_elliptic
    Nat.card isogeny.ker = 2
  /-- Every rational isogeny between these equations has degree at least two. -/
  degree_le : ∀ φ : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine,
    2 ≤ φ.degree

end VerifiedLcalc
