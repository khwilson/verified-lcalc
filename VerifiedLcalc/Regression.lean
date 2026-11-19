module

public import VerifiedLcalc.Certificate

@[expose] public section

namespace VerifiedLcalc.Regression

/-- Exact curve input, kept separate from the expected answer. Arithmetic center
is s=1; unitary lcalc normalization moves this to s=1/2. -/
structure CurveInput where
  label : String
  conductor : Nat
  equation : WeierstrassCurve ℤ
  deriving Repr, DecidableEq

structure Case where
  input : CurveInput
  expectedRank : Nat
  deriving Repr, DecidableEq

inductive Outcome
  | agree
  | mismatch (expected actual : Nat)
  | inconclusive
  deriving Repr, DecidableEq

/-- The backend sees only the curve, never the expected database answer. -/
def checkCase (backend : CurveInput → Option Nat) (c : Case) : Outcome :=
  match backend c.input with
  | none => .inconclusive
  | some n => if n = c.expectedRank then .agree else .mismatch c.expectedRank n

theorem checkCase_correct (backend : CurveInput → Option Nat) (c : Case) :
    checkCase backend c = .agree ↔ backend c.input = some c.expectedRank := by
  unfold checkCase
  split <;> rename_i h
  · simp [h]
  · split <;> rename_i hn
    · simp_all
    · simp_all

/-- Unimplemented backend: all curves remain explicitly inconclusive. This must
be replaced by a proved elliptic-curve analytic backend; no lookup is performed. -/
def pendingBackend (_input : CurveInput) : Option Nat := none

theorem pendingBackend_correct (c : CurveInput) : pendingBackend c = none := rfl

end VerifiedLcalc.Regression
