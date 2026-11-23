/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Arithmetic
public import Mathlib.Data.Nat.PadicValNat

/-! Exact finite coefficient computation used by numerical payload contracts. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Executable coefficients of the inverse quadratic polynomial. Its
identification with Mathlib's actual local polynomial requires minimality;
no new mathematical Euler-factor type is introduced here. -/
def computePrimePowerCoefficient (e : WeierstrassCurve ℤ) (p : Nat) : Nat → Int :=
  let a := computeFrobeniusTrace e p
  let q := if goodReduction e p then (p : Int) else 0
  localCoefficient a q

/-- Cache each prime's integer coefficient evaluator once for the finite prefix. -/
def primePowerTable (e : WeierstrassCurve ℤ) (limit : Nat) : List (Nat × (Nat → Int)) :=
  ((List.range (limit + 1)).filter isPrime).map fun p => (p, computePrimePowerCoefficient e p)

def coefficientFromPrimePowers (table : List (Nat × (Nat → Int))) (n : Nat) : Int :=
  if n = 0 then 0 else
    (table.map fun f =>
      let k := padicValNat f.1 n
      if k = 0 then 1 else f.2 k).prod

/-- a₁ through a_limit, using shared prime-power evaluators. -/
def modelCoefficients (e : WeierstrassCurve ℤ) (limit : Nat) : List Int :=
  let table := primePowerTable e limit
  (List.range limit).map fun j => coefficientFromPrimePowers table (j + 1)

end VerifiedLcalc.EllipticCurve
