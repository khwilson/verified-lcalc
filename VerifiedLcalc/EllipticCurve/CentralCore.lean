module

public import VerifiedLcalc.Certificate.Numerical.Outputs
public import VerifiedLcalc.EllipticCurve.CentralDefinitions
public import VerifiedLcalc.Certificate.Numerical.Payloads

/-! # Central-value numerical evaluator -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Construct a central-value payload from exact coefficient and tail bounds. -/
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
