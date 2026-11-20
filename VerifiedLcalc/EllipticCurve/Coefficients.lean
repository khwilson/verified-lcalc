module

public import VerifiedLcalc.EllipticCurve.CoefficientCore
public import VerifiedLcalc.EllipticCurve.Correctness
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Finite Euler-product coefficient, specified by mathematical prime
factorization rather than the implementation's repeated-division loop. -/
theorem coefficientFromPrimePowers_correct (factors : List (Nat × (Nat → Int))) (n : Nat)
    (hn : n ≠ 0) (hf : ∀ f ∈ factors, f.1.Prime)
    (hzero : ∀ f ∈ factors, f.2 0 = 1) :
    coefficientFromPrimePowers factors n =
      (factors.map fun f => f.2 (n.factorization f.1)).prod := by
  simp only [coefficientFromPrimePowers, ite_eq_right hn]
  congr 1
  apply List.map_congr_left
  intro f hm
  rw [Nat.padicValNat_def, Nat.multiplicity_eq_factorization (hf f hm)]
  split <;> rename_i h
  · simp [h, hzero f hm]
  · rfl

theorem primePowerTable_prime (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    ∀ f ∈ primePowerTable e limit, f.1.Prime := by
  intro f hm
  obtain ⟨p, _, hp, rfl⟩ := (primePowerTable_correct e limit f).mp hm
  exact (isPrime_correct p).mp hp

/-- Every produced coefficient is the prime-power product of the model's
computed local factors. Minimality and the global L-function identification are
additional obligations, not consequences of this finite arithmetic theorem. -/
theorem modelCoefficients_euler (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    modelCoefficients e limit = (List.range limit).map (fun j =>
      ((primePowerTable e limit).map fun f =>
        f.2 ((j + 1).factorization f.1)).prod) := by
  unfold modelCoefficients
  apply List.map_congr_left
  intro j _
  apply coefficientFromPrimePowers_correct _ _ (by omega) (primePowerTable_prime e limit)
  intro f hf
  obtain ⟨p, _, _, rfl⟩ := (primePowerTable_correct e limit f).mp hf
  rfl

end VerifiedLcalc.EllipticCurve
