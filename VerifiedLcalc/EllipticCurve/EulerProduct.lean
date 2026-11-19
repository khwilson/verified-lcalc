module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.Data.Nat.GCD.Basic

@[expose] public section
namespace VerifiedLcalc.EulerProduct
open ArithmeticFunction Filter

/-- An Euler factor contributes only its constant term at indices coprime to
its base. This includes the degenerate-base convention in mathlib. -/
theorem ofPowerSeries_apply_of_coprime {R : Type*} [CommRing R]
    (q d : ℕ) (f : PowerSeries R) (hf : f.constantCoeff = 1) (hcop : q.Coprime d) :
    ofPowerSeries q f d = (1 : ArithmeticFunction R) d := by
  by_cases hq : 1 < q
  · by_cases hd : d = 1
    · subst d
      simp [hf]
    · rw [ofPowerSeries_apply hq, Function.extend_apply', Pi.zero_apply, one_apply_ne hd]
      rintro ⟨k, hk⟩
      have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; exact hd hk.symm
      have hqd : q ∣ d := hk ▸ dvd_pow_self q hk0
      exact hq.ne' (hcop.eq_one_of_dvd hqd)
  · simp [ofPowerSeries, hq, hf]

/-- Dirichlet convolution at n only uses values at divisors of n. -/
theorem mul_apply_congr_right {R : Type*} [CommSemiring R]
    (f g h : ArithmeticFunction R) (n : ℕ) (he : ∀ d, d ∣ n → g d = h d) :
    (f * g) n = (f * h) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [he x.2 (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))]

/-- A product of factors that are the identity on divisors of n is still the
identity on those divisors. -/
theorem prod_apply_eq_one_on_divisors {ι R : Type*} [CommSemiring R]
    (f : ι → ArithmeticFunction R) (s : Finset ι) (n : ℕ)
    (hf : ∀ i ∈ s, ∀ d, d ∣ n → f i d = (1 : ArithmeticFunction R) d) :
    ∀ d, d ∣ n → (∏ i ∈ s, f i) d = (1 : ArithmeticFunction R) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro d hd
    rw [Finset.prod_insert hi]
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [mul_apply_congr_right _ _ 1 d (fun k hk => hs k (dvd_trans hk hd)), mul_one]
    exact hf i (Finset.mem_insert_self i s) d hd

/-- For pairwise coprime bases, a prime-power coefficient of an Euler product
comes entirely from its own local factor. Stabilization is supplied by
mathlib's Northcott Euler-product theorem, not an analytic convergence claim. -/
theorem apply_prime_pow {ι R : Type*} [CommRing R]
    (q : ι → ℕ) [Northcott q] (f : ι → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 1) (i₀ : ι) (hp : (q i₀).Prime)
    (hc : ∀ i, i ≠ i₀ → (q i).Coprime (q i₀)) (k : ℕ) :
    eulerProduct (fun i => ofPowerSeries (q i) (f i)) (q i₀ ^ k) =
      PowerSeries.coeff k (f i₀) := by
  classical
  have hconv := tendsTo_eulerProduct_ofPowerSeries q f hf (q i₀ ^ k)
  have hmem : ∀ᶠ s : Finset ι in atTop, i₀ ∈ s := by
    filter_upwards [eventually_ge_atTop ({i₀} : Finset ι)] with s hs
    exact hs (Finset.mem_singleton_self i₀)
  obtain ⟨s, hs, hi⟩ := (hconv.and hmem).exists
  rw [← hs, ← Finset.mul_prod_erase s (fun i => ofPowerSeries (q i) (f i)) hi]
  have hrest := prod_apply_eq_one_on_divisors (fun i => ofPowerSeries (q i) (f i))
    (s.erase i₀) (q i₀ ^ k) (by
      intro i hi d hd
      have hcop := (hc i (Finset.mem_erase.mp hi).1).pow_right k
      exact ofPowerSeries_apply_of_coprime (q i) d (f i) (hf i)
        (hcop.of_dvd_right hd))
  rw [mul_apply_congr_right _ _ 1 _ hrest, mul_one,
    ofPowerSeries_apply_pow hp.one_lt]

end VerifiedLcalc.EulerProduct
