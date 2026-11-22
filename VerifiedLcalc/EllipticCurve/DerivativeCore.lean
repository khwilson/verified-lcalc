module
public import VerifiedLcalc.EllipticCurve.CentralCore
public import VerifiedLcalc.EllipticCurve.DerivativeDefinitions
public import VerifiedLcalc.Certificates.NumericalContracts

/-! # First-derivative numerical evaluator -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Evaluate the finite derivative enclosure and tail certificate. -/
def evaluateDerivative (equation : (WeierstrassCurve ℤ)) (conductor limit steps cutoff : Nat)
    (policy : PrecisionPolicy := globalPrecision) : Option DerivativeResult := do
  if conductor = 0 ∨ steps = 0 ∨ cutoff ≤ 1 then none else do
    let a := alphaBounds conductor policy.precisionBits
    let cs := modelCoefficients equation limit
    let tail ← derivativeInfiniteTail a.1 policy.precisionBits cutoff
    let finite ← derivativeFiniteBounds cs a.1 a.2 policy.precisionBits steps cutoff
    return ⟨equation,conductor,policy,limit,steps,cutoff,cs,a.1,a.2,finite,tail,
      ⟨finite.1-tail,finite.2+tail,0,0⟩⟩

theorem evaluateDerivative_correct {e : (WeierstrassCurve ℤ)} {N M steps cutoff : Nat}
    {policy : PrecisionPolicy} {r : DerivativeResult}
    (h : evaluateDerivative e N M steps cutoff policy = some r) :
    r.equation = e ∧ r.conductor = N ∧ r.policy = policy ∧ r.termLimit = M ∧
      r.stepsPerUnit = steps ∧ r.cutoff = cutoff ∧ DerivativePayloadCorrect r := by
  unfold evaluateDerivative at h
  split at h
  · simp at h
  · next hn =>
    have hn' : 0 < N ∧ 0 < steps ∧ 1 < cutoff := by omega
    cases ht : derivativeInfiniteTail (alphaBounds N policy.precisionBits).1
        policy.precisionBits cutoff with
    | none => simp [ht] at h
    | some tail =>
      cases hf : derivativeFiniteBounds (modelCoefficients e M)
          (alphaBounds N policy.precisionBits).1 (alphaBounds N policy.precisionBits).2
          policy.precisionBits steps cutoff with
      | none => simp [ht, hf] at h
      | some finite =>
        have h' : r = ⟨e, N, policy, M, steps, cutoff, modelCoefficients e M,
            (alphaBounds N policy.precisionBits).1,
            (alphaBounds N policy.precisionBits).2, finite, tail,
            ⟨finite.1 - tail, finite.2 + tail, 0, 0⟩⟩ := by
          apply Option.some.inj
          simpa [ht, hf] using h.symm
        cases h'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hn'.1, hn'.2.1, hn'.2.2, rfl, rfl,
          rfl, ht, hf, rfl⟩
end VerifiedLcalc.EllipticCurve
