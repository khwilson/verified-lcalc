module

public import VerifiedLcalc.Certificate

@[expose] public section

namespace VerifiedLcalc.Regression

/-- Exact curve input, kept separate from the expected answer. Arithmetic center
is s=1; unitary lcalc normalization moves this to s=1/2. -/
structure CurveInput where
  label : String
  conductor : Nat
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a6 : Int
  deriving Repr, DecidableEq

/-- Only exact coefficients are passed to arithmetic, never the expected rank. -/
def CurveInput.equation (c : CurveInput) : Artifacts.CurveEquation :=
  ⟨c.a1, c.a2, c.a3, c.a4, c.a6⟩

theorem CurveInput.equation_correct (c : CurveInput) :
    c.equation.a1 = c.a1 ∧ c.equation.a2 = c.a2 ∧ c.equation.a3 = c.a3 ∧
      c.equation.a4 = c.a4 ∧ c.equation.a6 = c.a6 := ⟨rfl, rfl, rfl, rfl, rfl⟩

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
