/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! Representation and decidable equality for Mathlib's Weierstrass equation.

The pinned Mathlib definition provides neither instance. These derivations support raw records
that own a curve equation as data, including exact artifact subjects and certificate inputs.
-/

@[expose] public section

deriving instance Repr, DecidableEq for WeierstrassCurve
