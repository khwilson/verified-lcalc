/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

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

/-- The center implementation agrees with the documented case distinction. -/
theorem Subject.center_correct (s : Subject) :
    s.center = match s with
      | .monomial _ => 0
      | .ellipticCurve _ .arithmetic => 1
      | .ellipticCurve _ .unitary => 1 / 2 := by
  cases s with
  | monomial => rfl
  | ellipticCurve e n => cases n <;> rfl

end VerifiedLcalc.Artifacts
