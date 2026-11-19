module

public import VerifiedLcalc.EllipticCurve.CoefficientCore
public import VerifiedLcalc.Numerics.RationalExpCore

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

def piLower : Rat := 314159265358979323846 / 100000000000000000000
def piUpper : Rat := 314159265358979323847 / 100000000000000000000

/-- Rational bounds for 2*pi/sqrt(N). Fixed 20-decimal pi bounds cap attainable
accuracy; the output interval records that error instead of hiding it. -/
def alphaBounds (conductor bits : Nat) : Rat × Rat :=
  let scale := 2 ^ bits
  let root := Nat.sqrt (conductor * scale ^ 2)
  (2 * piLower * scale / (root + 1 : Nat), 2 * piUpper * scale / root)

/-- Central-value summands: (1+w)*a_n/n * exp(-alpha*n). The index is stored
alongside each term so the semantic argument is unambiguous. -/
def centralTerms (coefficients : List Int) (rootNumber : Int) (alphaLo alphaHi : Rat) :
    List (Nat × RationalExpTerm) :=
  coefficients.zipIdx.map fun (a, j) =>
    (j + 1, ⟨((1 + rootNumber : Int) : Rat) * (a : Rat) / (j + 1 : Nat),
      -alphaHi * (j + 1 : Nat), -alphaLo * (j + 1 : Nat)⟩)

/-- Geometric ratio for the shifted square majorant. Past M,
((n+1)/n)^2 is at most ((M+2)/(M+1))^2. -/
def squareTailRatio (q : Rat) (limit : Nat) : Rat :=
  q * (((limit + 2 : Nat) : Rat) / (limit + 1 : Nat)) ^ 2

/-- Tail bound for sum_{n>M} n^2*q^n when the ratio test is strictly below 1. -/
def squareTailBound (q : Rat) (limit : Nat) : Option Rat :=
  let ratio := squareTailRatio q limit
  if 0 ≤ q ∧ ratio < 1 then
    some ((((limit + 1 : Nat) : Rat) ^ 2 * q ^ (limit + 1)) / (1 - ratio))
  else none

def centralBox (coefficients : List Int) (rootNumber : Int) (alphaLo alphaHi : Rat)
    (prec : Nat) (tail : Rat) : Box :=
  let bounds := rationalExpSumBounds prec
    ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)
  ⟨bounds.1 - tail, bounds.2 + tail, 0, 0⟩

theorem centralBox_correct (coefficients : List Int) (rootNumber : Int)
    (alphaLo alphaHi : Rat) (prec : Nat) (tail : Rat) :
    centralBox coefficients rootNumber alphaLo alphaHi prec tail =
      ⟨(rationalExpSumBounds prec ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)).1 - tail,
       (rationalExpSumBounds prec ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)).2 + tail,
       0, 0⟩ := rfl

structure CentralResult where
  equation : (WeierstrassCurve ℤ)
  conductor : Nat
  rootNumber : Int
  policy : PrecisionPolicy
  termLimit : Nat
  coefficients : List Int
  alphaLo : Rat
  alphaHi : Rat
  geometricUpper : Rat
  tail : Rat
  box : Box
  deriving Repr, DecidableEq

/-- Central expression evaluator. Success is a finite numerical payload;
the analytic theorem additionally requires the actual coefficient bound,
conductor/root-number identification and split-Mellin formula. -/
def evaluateCentral (equation : (WeierstrassCurve ℤ)) (conductor : Nat)
    (rootNumber : Int) (limit : Nat) (policy : PrecisionPolicy := globalPrecision) :
    Option CentralResult :=
  if 0 < conductor ∧ (rootNumber = 1 ∨ rootNumber = -1) then
    let alpha := alphaBounds conductor policy.precisionBits
    let q := (rationalExpBounds (-alpha.1) (-alpha.1) policy.precisionBits).2
    match squareTailBound q limit with
    | none => none
    | some remainder =>
      let coefficients := modelCoefficients equation limit
      let tail := ((1 + rootNumber : Int).natAbs : Rat) * remainder
      some ⟨equation, conductor, rootNumber, policy, limit, coefficients,
        alpha.1, alpha.2, q, tail,
        centralBox coefficients rootNumber alpha.1 alpha.2 policy.precisionBits tail⟩
  else none

theorem centralTerms_correct (coefficients : List Int) (rootNumber : Int)
    (alphaLo alphaHi : Rat) :
    centralTerms coefficients rootNumber alphaLo alphaHi =
      coefficients.zipIdx.map (fun (a, j) =>
        (j + 1, ⟨((1 + rootNumber : Int) : Rat) * (a : Rat) / (j + 1 : Nat),
          -alphaHi * (j + 1 : Nat), -alphaLo * (j + 1 : Nat)⟩)) := rfl

theorem squareTailRatio_correct (q : Rat) (limit : Nat) :
    squareTailRatio q limit = q * (((limit + 2 : Nat) : Rat) / (limit + 1 : Nat)) ^ 2 := rfl

theorem squareTailBound_correct {q : Rat} {limit : Nat} {tail : Rat}
    (h : squareTailBound q limit = some tail) :
    0 ≤ q ∧ squareTailRatio q limit < 1 ∧
      tail = (((limit + 1 : Nat) : Rat) ^ 2 * q ^ (limit + 1)) /
        (1 - squareTailRatio q limit) := by
  unfold squareTailBound at h
  dsimp only at h
  split at h <;> rename_i hc
  · cases h
    exact ⟨hc.1, hc.2, rfl⟩
  · simp at h

/-- Complete finite contract of a successful evaluator call. The values stored
in the payload cannot drift from the inputs, coefficient pipeline or policy. -/
def CentralPayloadCorrect (r : CentralResult) : Prop :=
  0 < r.conductor ∧ (r.rootNumber = 1 ∨ r.rootNumber = -1) ∧
  r.coefficients = modelCoefficients r.equation r.termLimit ∧
  r.alphaLo = (alphaBounds r.conductor r.policy.precisionBits).1 ∧
  r.alphaHi = (alphaBounds r.conductor r.policy.precisionBits).2 ∧
  r.geometricUpper =
    (rationalExpBounds (-r.alphaLo) (-r.alphaLo) r.policy.precisionBits).2 ∧
  ∃ remainder, squareTailBound r.geometricUpper r.termLimit = some remainder ∧
    r.tail = ((1 + r.rootNumber : Int).natAbs : Rat) * remainder ∧
    r.box = centralBox r.coefficients r.rootNumber r.alphaLo r.alphaHi
      r.policy.precisionBits r.tail

theorem evaluateCentral_correct {equation : (WeierstrassCurve ℤ)} {conductor : Nat}
    {rootNumber : Int} {limit : Nat} {policy : PrecisionPolicy} {r : CentralResult}
    (h : evaluateCentral equation conductor rootNumber limit policy = some r) :
    r.equation = equation ∧ r.conductor = conductor ∧ r.rootNumber = rootNumber ∧
      r.policy = policy ∧ r.termLimit = limit ∧ CentralPayloadCorrect r := by
  unfold evaluateCentral at h
  split at h <;> rename_i hc
  · dsimp only at h
    split at h <;> rename_i ht
    · simp at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, hc.1, hc.2, rfl, rfl, rfl, rfl,
        _, ht, rfl, rfl⟩
  · simp at h

end VerifiedLcalc.EllipticCurve
