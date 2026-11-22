/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Data.Rat.Defs
public import VerifiedLcalc.Certificate.Witnesses.CurveProofs

/-! # Generic curve-indexed proof-carrying data -/

@[expose] public section

namespace VerifiedLcalc

deriving instance Repr, DecidableEq for AbcQualityClaim

/-- Attach a standalone discriminant witness to its own equation. -/
def DiscriminantWitness.toProofs {R : Type*} [CommRing R] (w : DiscriminantWitness R) :
    EllipticProofs w.curve :=
  { discriminant := some ⟨w.discriminant, w.discriminant_eq⟩ }

end VerifiedLcalc
