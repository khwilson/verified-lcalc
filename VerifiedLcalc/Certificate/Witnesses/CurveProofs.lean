/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Rat.Defs

/-! # Generic curve witness structures -/

@[expose] public section

namespace VerifiedLcalc

/-- A reported abc quality and evidence for its absolute error bound. -/
structure AbcQualityClaim where
  /-- Exact rational interpretation of the reported value. -/
  reported : Rat
  /-- Claimed maximum absolute error. -/
  error : Rat
  /-- All prime factors of the abc product, with multiplicity. -/
  factors : List Nat
/-- A discriminant value together with the equation and its exact proof. -/
structure DiscriminantWitness (R : Type*) [CommRing R] where
  /-- The equation whose discriminant is certified. -/
  curve : WeierstrassCurve R
  /-- The value of the discriminant. -/
  discriminant : R
  /-- The discriminant of the supplied equation equals the supplied value. -/
  discriminant_eq : curve.Δ = discriminant
/-- Optional proved facts about one fixed Weierstrass equation. -/
structure EllipticProofs {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- A discriminant value with a proof about the indexed equation. -/
  discriminant : Option { d : R // curve.Δ = d } := none
  /-- The ordered tuple of b₂, b₄, b₆ and b₈ with a proof about the equation. -/
  bInvariants : Option { b : R × R × R × R //
    (curve.b₂, curve.b₄, curve.b₆, curve.b₈) = b } := none
  /-- The ordered pair of c₄ and c₆ with a proof about the equation. -/
  cInvariants : Option { c : R × R // (curve.c₄, curve.c₆) = c } := none

end VerifiedLcalc
