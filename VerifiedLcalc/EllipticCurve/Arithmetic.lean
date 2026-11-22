module

public import VerifiedLcalc.Certificates.WeierstrassInstances
public import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCountOdd
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-! # Finite point counts and Frobenius traces -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
/-- Use Euler's criterion at odd primes and the shared finite-ring enumeration
otherwise. Modulus zero retains the unsupported sentinel convention. -/
def computePointCount (e : WeierstrassCurve ℤ) (p : Nat) : Nat :=
  if hp : p = 0 then 1 else
    letI : NeZero p := ⟨hp⟩
    if hodd : Nat.Prime p ∧ p ≠ 2 then
      letI : Fact (Nat.Prime p) := ⟨hodd.1⟩
      (e.baseChange (ZMod p)).pointCountOddFinite
    else (e.baseChange (ZMod p)).pointCountFinite

/-- Evaluate the shared finite-ring trace. Correctness against TauCeti's
field-valued mathematical definition is proved for prime moduli. -/
def computeFrobeniusTrace (e : WeierstrassCurve ℤ) (p : Nat) : Int :=
  if _hp : p = 0 then 0 else
    (p : Int) + 1 - computePointCount e p

/-- Reflect Mathlib's decidable primality predicate into the executable API. -/
def isPrime (p : Nat) : Bool := decide (Nat.Prime p)

/-- This tests the given integral model's smooth reduction; it does not run
Tate's algorithm or assert that a singular model is minimal. -/
def goodReduction (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  decide (e.Δ % (p : Int) ≠ 0)

structure PrimeData where
  prime : Nat
  points : Nat
  trace : Int
  deriving Repr, DecidableEq

/-- Supported arithmetic backend: good primes only. Bad primes are unresolved,
not filled using an unproved minimal-model/reduction classification. -/
def analysePrime (e : (WeierstrassCurve ℤ)) (p : Nat) : Option PrimeData :=
  if isPrime p && goodReduction e p then
    some ⟨p, computePointCount e p, computeFrobeniusTrace e p⟩
  else none

theorem analysePrime_correct (e : (WeierstrassCurve ℤ)) (p : Nat) (d : PrimeData)
    (h : analysePrime e p = some d) :
    isPrime p = true ∧ goodReduction e p = true ∧
      d.prime = p ∧ d.points = computePointCount e p ∧ d.trace = computeFrobeniusTrace e p := by
  unfold analysePrime at h
  split at h <;> rename_i hc
  · cases h
    have hh : isPrime p = true ∧ goodReduction e p = true := by simpa using hc
    obtain ⟨hp, he⟩ := hh
    exact ⟨hp, he, rfl, rfl, rfl⟩
  · simp at h

/-- Linear-time recurrence state for the inverse quadratic Euler factor.
The second parameter is p at good primes and 0 for a proved linear factor. -/
def localPair (a q : Int) : Nat → Int × Int
  | 0 => (1, a)
  | n + 1 => let prev := localPair a q n; (prev.2, a * prev.2 - q * prev.1)

def localCoefficient (a q : Int) (k : Nat) : Int := (localPair a q k).1

/-- Operational recurrence for the executable evaluator. Its mathematical
specification is Mathlib's inverse polynomial in `Euler.lean`. -/
theorem localCoefficient_recurrence (a q : Int) (k : Nat) :
    localCoefficient a q (k + 2) =
      a * localCoefficient a q (k + 1) - q * localCoefficient a q k := by
  simp [localCoefficient, localPair]

end VerifiedLcalc.EllipticCurve
