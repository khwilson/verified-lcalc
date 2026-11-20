module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Artifacts

/-- Evaluate the shared finite-ring count. Modulus zero is an unsupported
sentinel, retaining the former empty enumeration plus infinity convention. -/
def computePointCount (e : WeierstrassCurve ℤ) (p : Nat) : Nat :=
  if hp : p = 0 then 1 else
    letI : NeZero p := ⟨hp⟩
    (e.baseChange (ZMod p)).pointCountFinite

/-- Evaluate the shared finite-ring trace. Correctness against TauCeti's
field-valued mathematical definition is proved for prime moduli. -/
def computeFrobeniusTrace (e : WeierstrassCurve ℤ) (p : Nat) : Int :=
  if hp : p = 0 then 0 else
    letI : NeZero p := ⟨hp⟩
    (e.baseChange (ZMod p)).frobeniusTraceFinite

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

theorem localPair_correct (a q : Int) (k : Nat) :
    localPair a q k = (localCoefficient a q k, localCoefficient a q (k + 1)) := by
  simp [localCoefficient, localPair]

/-- Specification of the coefficients of (1 - a T + q T²)⁻¹. -/
def InverseEulerCoefficients (a q : Int) (c : Nat → Int) : Prop :=
  c 0 = 1 ∧ c 1 = a ∧ ∀ k, c (k + 2) = a * c (k + 1) - q * c k

theorem localCoefficient_correct (a q : Int) :
    InverseEulerCoefficients a q (localCoefficient a q) := by
  refine ⟨rfl, rfl, ?_⟩
  intro k
  simp [localCoefficient, localPair]

/-- The recurrence characterizes the coefficients uniquely, not just a chosen
implementation of them. -/
theorem localCoefficient_unique (a q : Int) (c : Nat → Int)
    (h : InverseEulerCoefficients a q c) : c = localCoefficient a q := by
  funext k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => exact h.1
    | succ k =>
      cases k with
      | zero => exact h.2.1
      | succ k =>
        rw [h.2.2 k, ih (k + 1) (by omega), ih k (by omega)]
        exact (localCoefficient_correct a q).2.2 k |>.symm

end VerifiedLcalc.EllipticCurve
