module

public import VerifiedLcalc.Certificate
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Artifacts

/-- The equation's left side minus right side, over the integers. -/
def residual (e : (WeierstrassCurve ℤ)) (x y : Int) : Int :=
  y ^ 2 + e.a₁ * x * y + e.a₃ * y -
    (x ^ 3 + e.a₂ * x ^ 2 + e.a₄ * x + e.a₆)

/-- Exact modular membership, including characteristics 2 and 3. -/
def onCurve (e : (WeierstrassCurve ℤ)) (p : Nat) (xy : Fin p × Fin p) : Bool :=
  decide (residual e xy.1.val xy.2.val % (p : Int) = 0)

theorem onCurve_correct (e : (WeierstrassCurve ℤ)) (p : Nat) (xy : Fin p × Fin p) :
    onCurve e p xy = true ↔ residual e xy.1.val xy.2.val % (p : Int) = 0 := by
  simp [onCurve]

/-- Exhaustive enumeration without duplicates. Infinity is counted separately. -/
def affinePoints (e : (WeierstrassCurve ℤ)) (p : Nat) : List (Fin p × Fin p) :=
  ((List.finRange p).flatMap (fun x => (List.finRange p).map (fun y => (x, y)))).filter
    (onCurve e p)

theorem affinePoints_correct (e : (WeierstrassCurve ℤ)) (p : Nat) (xy : Fin p × Fin p) :
    xy ∈ affinePoints e p ↔ onCurve e p xy = true := by
  rcases xy with ⟨x, y⟩
  simp [affinePoints]

def affineCount (e : (WeierstrassCurve ℤ)) (p : Nat) : Nat := (affinePoints e p).length

/-- Executable enumeration of the reduced projective model, including singular
solutions. `computePointCount_eq_pointCount` identifies it with TauCeti’s
noncomputable `WeierstrassCurve.pointCount`. -/
def computePointCount (e : (WeierstrassCurve ℤ)) (p : Nat) : Nat := affineCount e p + 1

def frobeniusTrace (e : (WeierstrassCurve ℤ)) (p : Nat) : Int :=
  (p : Int) + 1 - (computePointCount e p : Int)

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
    some ⟨p, computePointCount e p, frobeniusTrace e p⟩
  else none

theorem analysePrime_correct (e : (WeierstrassCurve ℤ)) (p : Nat) (d : PrimeData)
    (h : analysePrime e p = some d) :
    isPrime p = true ∧ goodReduction e p = true ∧
      d.prime = p ∧ d.points = computePointCount e p ∧ d.trace = frobeniusTrace e p := by
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
