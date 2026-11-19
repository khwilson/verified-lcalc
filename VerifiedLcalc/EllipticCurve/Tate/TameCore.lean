module

public import VerifiedLcalc.EllipticCurve.BadPrimeCore
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Parity

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Mathlib's finite square decision procedure, reflected as a Boolean.
The zero modulus has no finite enumeration and is rejected explicitly. -/
def isSquareMod (p : Nat) (a : Int) : Bool :=
  if hp : p = 0 then false else
    letI : NeZero p := ⟨hp⟩
    decide (IsSquare (a : ZMod p))

/-- Executable Legendre symbol; correctness for odd primes is in TameArithmetic. -/
def legendreValue (p : Nat) (a : Int) : Int :=
  if a % (p : Int) = 0 then 0 else if isSquareMod p a then 1 else -1

/-- Negative j-valuation, guarding c4=0 rather than treating its valuation as zero. -/
def potentiallyMultiplicative (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  e.c₄ != 0 && decide (3 * padicValNat p (e.c₄).natAbs <
    padicValNat p (e.Δ).natAbs)

/-- The tame additive root formula. Callers must establish prime p>=5 and
minimality before interpreting this as the elliptic curve's local root number. -/
def tameAdditiveRoot (e : (WeierstrassCurve ℤ)) (p : Nat) : Int :=
  if potentiallyMultiplicative e p then legendreValue p (-1)
  else
    let v := padicValNat p (e.Δ).natAbs % 12
    if v == 3 || v == 9 then legendreValue p (-2)
    else if v == 4 || v == 8 then legendreValue p (-3)
    else legendreValue p (-1)

structure LocalConductorRoot where
  prime : Nat
  exponent : Nat
  root : Int
  deriving Repr, DecidableEq

/-- Good and multiplicative reduction work in every characteristic; additive
reduction is supported here only away from 2 and 3. -/
def localConductorRoot? (e : (WeierstrassCurve ℤ)) (p : Nat) : Option LocalConductorRoot :=
  if !isPrime p then none
  else match modelReduction e p with
    | .good => some ⟨p, 0, 1⟩
    | .multiplicative => some ⟨p, 1, -(singularTrace e p)⟩
    | .additive => if 3 < p then some ⟨p, 2, tameAdditiveRoot e p⟩ else none

/-- This guard excludes additive reduction at the two wild primes. It does not
assert minimality, which is supplied separately by checked arithmetic evidence. -/
def tameAtWild (e : (WeierstrassCurve ℤ)) : Bool :=
  modelReduction e 2 != .additive && modelReduction e 3 != .additive

/-- Candidate-only global aggregation. Completeness of the prime list and its
agreement with the mathematical product are checked in generated proofs. -/
def conductorRootFromPrimes? (e : (WeierstrassCurve ℤ)) (primes : List Nat) :
    Option (Nat × Int) := do
  let data ← primes.mapM (localConductorRoot? e)
  return ((data.map (fun d => d.prime ^ d.exponent)).prod, -((data.map (·.root)).prod))

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve
/-- Total executable values; interpretation requires the support guard. -/
def localExponent (e : (WeierstrassCurve ℤ)) (p : Nat) : Nat :=
  match modelReduction e p with
  | .good => 0
  | .multiplicative => 1
  | .additive => 2

def localRoot (e : (WeierstrassCurve ℤ)) (p : Nat) : Int :=
  match modelReduction e p with
  | .good => 1
  | .multiplicative => -(singularTrace e p)
  | .additive => tameAdditiveRoot e p
end VerifiedLcalc.EllipticCurve
