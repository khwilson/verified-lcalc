module

public import VerifiedLcalc.EllipticCurve.Coefficients
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Inherit the shared evaluator's elementary bound for the tail majorant. -/
theorem computeFrobeniusTrace_abs_le_square (e : WeierstrassCurve ℤ) (p : Nat)
    (hp : 1 ≤ p) : |computeFrobeniusTrace e p| ≤ (p : Int) ^ 2 := by
  letI : NeZero p := ⟨by omega⟩
  simpa only [computeFrobeniusTrace, dif_neg (NeZero.ne p), ZMod.card] using
    (e.baseChange (ZMod p)).frobeniusTraceFinite_abs_le_square

/-- A safe weak prime-power coefficient bound. It uses elementary trace bounds
and the recurrence, not the Weil conjectures or a modularity assumption. -/
theorem localCoefficient_abs_le_cube_power (p : Nat) (hp : 2 ≤ p) (a q : Int)
    (ha : |a| ≤ (p : Int) ^ 2) (hq : |q| ≤ (p : Int)) (k : Nat) :
    |localCoefficient a q k| ≤ (p : Int) ^ (3 * k) := by
  have hp2 : (2 : Int) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : Int) ≤ p := by omega
  have hp0 : (0 : Int) ≤ p := by omega
  have hp5 : (p : Int) ≤ (p : Int) ^ 5 := le_self_pow₀ hp1 (by decide)
  have hpoly : (p : Int) ^ 5 + p ≤ (p : Int) ^ 6 := by
    calc
      _ ≤ (p : Int) ^ 5 + (p : Int) ^ 5 := add_le_add le_rfl hp5
      _ = 2 * (p : Int) ^ 5 := by ring
      _ ≤ (p : Int) * (p : Int) ^ 5 :=
        mul_le_mul_of_nonneg_right hp2 (pow_nonneg hp0 _)
      _ = (p : Int) ^ 6 := by ring
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simp [localCoefficient, localPair]
    | succ k =>
      cases k with
      | zero =>
        simpa [localCoefficient, localPair] using
          ha.trans (pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3))
      | succ k =>
        have hprev := ih k (by omega)
        have hnext := ih (k + 1) (by omega)
        rw [(localCoefficient_correct a q).2.2 k]
        calc
          _ ≤ |a * localCoefficient a q (k + 1)| + |q * localCoefficient a q k| :=
            by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (a * localCoefficient a q (k + 1)) (0 : Int)
              (q * localCoefficient a q k))
          _ = |a| * |localCoefficient a q (k + 1)| +
              |q| * |localCoefficient a q k| := by rw [abs_mul, abs_mul]
          _ ≤ (p : Int) ^ 2 * (p : Int) ^ (3 * (k + 1)) +
              (p : Int) * (p : Int) ^ (3 * k) :=
            add_le_add (mul_le_mul ha hnext (abs_nonneg _) (pow_nonneg hp0 _))
              (mul_le_mul hq hprev (abs_nonneg _) hp0)
          _ = ((p : Int) ^ 5 + p) * (p : Int) ^ (3 * k) := by
            rw [show 3 * (k + 1) = 3 * k + 3 by omega, pow_add]
            ring
          _ ≤ (p : Int) ^ 6 * (p : Int) ^ (3 * k) :=
            mul_le_mul_of_nonneg_right hpoly (pow_nonneg hp0 _)
          _ = (p : Int) ^ (3 * (k + 2)) := by
            rw [show 3 * (k + 2) = 6 + 3 * k by omega, pow_add]

theorem modelFactor_bounds (e : (WeierstrassCurve ℤ)) (p : Nat) (hp : p.Prime) :
    |(modelFactor e p).trace| ≤ (p : Int) ^ 2 ∧
      |(modelFactor e p).quadratic| ≤ (p : Int) := by
  constructor
  · exact computeFrobeniusTrace_abs_le_square e p hp.one_lt.le
  · unfold modelFactor
    split <;> simp

/-- Canonical mathematical coefficient attached to a family of local factors.
The finite executable prefix is separately related to this specification. -/
noncomputable def eulerCoefficient (factor : Nat → ModelEulerFactor) (n : Nat) : Int :=
  if n = 0 then 0 else n.factorization.prod fun p k =>
    localCoefficient (factor p).trace (factor p).quadratic k

/-- The executable prime table contains every prime that can divide the
requested index. Extra primes contribute the constant coefficient one. -/
theorem coefficientFromFactors_model_eq_euler (e : (WeierstrassCurve ℤ))
    (limit n : Nat) (hn : n ≠ 0) (hlimit : n ≤ limit) :
    coefficientFromFactors (modelFactors e limit) n =
      eulerCoefficient (modelFactor e) n := by
  let primes := (List.range (limit + 1)).filter isPrime
  have hs : n.factorization.support ⊆ primes.toFinset := by
    intro p hp
    have hp' : p ∈ n.primeFactors := hp
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hle := (Nat.le_of_mem_primeFactors hp').trans hlimit
    simp only [List.mem_toFinset, primes, List.mem_filter, List.mem_range]
    exact ⟨by omega, (isPrime_correct p).mpr hprime⟩
  rw [coefficientFromFactors_correct _ _ hn (modelFactors_prime e limit)]
  rw [eulerCoefficient, ite_eq_right hn,
    Finsupp.prod_of_support_subset _ hs _ (by
      intro p _
      simp [localCoefficient, localPair]),
    List.prod_toFinset _ (List.nodup_range.filter _)]
  simp [modelFactors, List.map_map, Function.comp_def, modelFactor]

/-- Every element of the executable table agrees with the canonical infinite
Euler-factor specification at the same index. -/
theorem modelCoefficients_eq_euler (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => eulerCoefficient (modelFactor e) (j + 1)) := by
  unfold modelCoefficients
  apply List.map_congr_left
  intro j hj
  exact coefficientFromFactors_model_eq_euler e limit (j + 1) (by omega)
    (by have := List.mem_range.mp hj; omega)

theorem eulerCoefficient_abs_le_cube (factor : Nat → ModelEulerFactor)
    (hb : ∀ p : Nat, p.Prime → |(factor p).trace| ≤ (p : Int) ^ 2 ∧
      |(factor p).quadratic| ≤ (p : Int)) (n : Nat) :
    |eulerCoefficient factor n| ≤ (n : Int) ^ 3 := by
  by_cases hn : n = 0
  · simp [eulerCoefficient, hn]
  rw [eulerCoefficient, ite_eq_right hn, Finsupp.prod, Finset.abs_prod]
  calc
    _ ≤ ∏ p ∈ n.factorization.support, (p : Int) ^ (3 * n.factorization p) := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact localCoefficient_abs_le_cube_power p hprime.two_le _ _
        (hb p hprime).1 (hb p hprime).2 _
    _ = (n : Int) ^ 3 := by
      simp_rw [Nat.mul_comm 3, pow_mul]
      rw [Finset.prod_pow]
      have hprod : (∏ p ∈ n.factorization.support, (p : Int) ^ n.factorization p) = n := by
        exact_mod_cast Nat.prod_factorization_pow_eq_self hn
      rw [hprod]

theorem model_eulerCoefficient_abs_le_cube (e : (WeierstrassCurve ℤ)) (n : Nat) :
    |eulerCoefficient (modelFactor e) n| ≤ (n : Int) ^ 3 :=
  eulerCoefficient_abs_le_cube _ (modelFactor_bounds e) n

end VerifiedLcalc.EllipticCurve
