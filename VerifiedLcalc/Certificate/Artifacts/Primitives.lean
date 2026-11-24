/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Non-record exact request discriminants and normalization data. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Normalization of the elliptic-curve L-function. -/
inductive Normalization
  | arithmetic
  | unitary
  deriving Repr, DecidableEq

/-- A demo target and an elliptic-curve target cannot share a certificate. -/
inductive Subject
  | monomial (degree : Nat)
  | ellipticCurve (equation : WeierstrassCurve ℤ) (normalization : Normalization)
  deriving Repr, DecidableEq

/-- Exact evaluation center determined by the subject and normalization. -/
def Subject.center : Subject → Rat
  | .monomial _ => 0
  | .ellipticCurve _ .arithmetic => 1
  | .ellipticCurve _ .unitary => 1 / 2

end VerifiedLcalc.Artifacts
