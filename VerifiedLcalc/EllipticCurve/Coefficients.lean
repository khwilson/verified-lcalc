module

public import VerifiedLcalc.EllipticCurve.CoefficientCore
public import VerifiedLcalc.EllipticCurve.Correctness
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

theorem valuationFuel_correct {p n fuel : Nat} (hp : p.Prime) (hn : 0 < n)
    (hf : n ≤ fuel) : valuationFuel p fuel n = n.factorization p := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    by_cases hd : p ∣ n
    · have hdiv : n / p < n := Nat.div_lt_self hn hp.one_lt
      have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      have hi := ih hpos (by omega : n / p ≤ fuel)
      rw [valuationFuel, ite_eq_left ⟨hp.two_le, hn, Nat.mod_eq_zero_of_dvd hd⟩, hi]
      rw [Nat.factorization_div hd, Finsupp.tsub_apply, hp.factorization_self]
      have := hp.factorization_pos_of_dvd hn.ne' hd
      omega
    · rw [valuationFuel, ite_eq_right (by
        intro h
        exact hd (Nat.dvd_of_mod_eq_zero h.2.2))]
      exact (Nat.factorization_eq_zero_of_not_dvd hd).symm

theorem primeExponent_correct {p n : Nat} (hp : p.Prime) :
    primeExponent p n = n.factorization p := by
  cases n with
  | zero => simp [primeExponent, valuationFuel]
  | succ n => exact valuationFuel_correct hp (by omega) (by rfl)

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
  rw [primeExponent_correct (hf f hm)]
  split <;> rename_i h
  · simp [h, localCoefficient, localPair]
  · rfl

theorem modelFactors_prime (e : Artifacts.CurveEquation) (limit : Nat) :
    ∀ f ∈ modelFactors e limit, f.prime.Prime := by
  intro f hm
  obtain ⟨p, _, hp, rfl⟩ := (modelFactors_correct e limit f).mp hm
  exact (isPrime_correct p).mp hp

/-- Every produced coefficient is the prime-power product of the model's
computed local factors. Minimality and the global L-function identification are
additional obligations, not consequences of this finite arithmetic theorem. -/
theorem modelCoefficients_euler (e : Artifacts.CurveEquation) (limit : Nat) :
    modelCoefficients e limit = (List.range limit).map (fun j =>
      ((modelFactors e limit).map fun f =>
        localCoefficient f.trace f.quadratic ((j + 1).factorization f.prime)).prod) := by
  unfold modelCoefficients
  apply List.map_congr_left
  intro j _
  exact coefficientFromFactors_correct _ _ (by omega) (modelFactors_prime e limit)

end VerifiedLcalc.EllipticCurve
