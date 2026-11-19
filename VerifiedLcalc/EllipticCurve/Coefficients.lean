module

public import VerifiedLcalc.EllipticCurve.CoefficientCore
public import VerifiedLcalc.EllipticCurve.Correctness
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Finite Euler-product coefficient, specified by mathematical prime
factorization rather than the implementation's repeated-division loop. -/
theorem coefficientFromFactors_correct (factors : List ModelEulerFactor) (n : Nat)
    (hn : n ≠ 0) (hf : ∀ f ∈ factors, f.prime.Prime) :
    coefficientFromFactors factors n =
      (factors.map fun f => localCoefficient f.trace f.quadratic (n.factorization f.prime)).prod := by
  simp only [coefficientFromFactors, ite_eq_right hn]
  congr 1
  apply List.map_congr_left
  intro f hm
  rw [Nat.padicValNat_def, Nat.multiplicity_eq_factorization (hf f hm)]
  split <;> rename_i h
  · simp [h, localCoefficient, localPair]
  · rfl

theorem modelFactors_prime (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    ∀ f ∈ modelFactors e limit, f.prime.Prime := by
  intro f hm
  obtain ⟨p, _, hp, rfl⟩ := (modelFactors_correct e limit f).mp hm
  exact (isPrime_correct p).mp hp

/-- Every produced coefficient is the prime-power product of the model's
computed local factors. Minimality and the global L-function identification are
additional obligations, not consequences of this finite arithmetic theorem. -/
theorem modelCoefficients_euler (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    modelCoefficients e limit = (List.range limit).map (fun j =>
      ((modelFactors e limit).map fun f =>
        localCoefficient f.trace f.quadratic ((j + 1).factorization f.prime)).prod) := by
  unfold modelCoefficients
  apply List.map_congr_left
  intro j _
  exact coefficientFromFactors_correct _ _ (by omega) (modelFactors_prime e limit)

end VerifiedLcalc.EllipticCurve
