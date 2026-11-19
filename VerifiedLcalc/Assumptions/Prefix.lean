module

public import VerifiedLcalc.Assumptions.ModularityStatement
public import VerifiedLcalc.EllipticCurve.GlobalBounds
public import VerifiedLcalc.EllipticCurve.PrefixCore

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

theorem prefixSupported_correct (e : Artifacts.CurveEquation) (limit : ℕ) :
    prefixSupported e limit = true ↔ ∀ p : ℕ, p ≤ limit → p.Prime →
      goodReduction e p = true ∧ (p ^ 2 ≤ limit → 1 < (frobeniusTrace e p).natAbs) := by
  simp only [prefixSupported, List.all_eq_true, List.mem_filter, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h p hp hprime
    obtain ⟨hg, hb⟩ := h p ⟨by omega, (isPrime_correct p).mpr hprime⟩
    exact ⟨hg, fun hpow => by rcases hb with hb | hb <;> omega⟩
  · intro h p hp
    obtain ⟨hg, hb⟩ := h p (by omega) ((isPrime_correct p).mp hp.2)
    exact ⟨hg, by by_cases hpow : p ^ 2 ≤ limit; exact Or.inr (hb hpow); exact Or.inl (by omega)⟩

theorem ModularRealization.prime_coefficient {e : Artifacts.CurveEquation}
    (m : ModularRealization e) (p : ℕ) (hp : p.Prime) (hg : goodReduction e p = true) :
    (weierstrass e ℚ).LFunction p = frobeniusTrace e p := by
  have h := m.goodPrimeCoefficients p hp hg
  rw [m.coefficients] at h
  exact_mod_cast h

/-- One theorem certifies every supported finite prefix; generated certificates
only check the finite eligibility predicate and instantiate this result. -/
theorem ModularRealization.coefficient_of_prefixSupported {e : Artifacts.CurveEquation}
    (m : ModularRealization e) (limit : ℕ) (hs : prefixSupported e limit = true)
    (n : ℕ) (hn : n ≠ 0) (hlim : n ≤ limit) :
    (weierstrass e ℚ).LFunction n = eulerCoefficient (modelFactor e) n := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (weierstrass e ℚ).isMultiplicative_LFunction hn, eulerCoefficient, ite_eq_right hn]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hle := (Nat.le_of_mem_primeFactors hp).trans hlim
  obtain ⟨hg, hb⟩ := (prefixSupported_correct e limit).mp hs p hle hprime
  have ha := m.prime_coefficient p hprime hg
  change (weierstrass e ℚ).LFunction (p ^ n.factorization p) = _
  by_cases hk0 : n.factorization p = 0
  · simp [hk0, localCoefficient, localPair]
  by_cases hk1 : n.factorization p = 1
  · simp [hk1, ha, modelFactor, localCoefficient, localPair]
  have hk2 : 2 ≤ n.factorization p := by omega
  have hp2 : p ^ 2 ≤ limit :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((hprime.pow_dvd_iff_le_factorization hn).mpr hk2)).trans hlim
  have hlarge : (1 : ℤ) < |frobeniusTrace e p| := by
    have h : (1 : ℤ) < ((frobeniusTrace e p).natAbs : ℤ) := by exact_mod_cast hb hp2
    simpa only [Int.natCast_natAbs] using h
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨q, hq, _, _, hr, hbad⟩ := LFunction_primePower_recurrence (weierstrass e ℚ) p
  have hqp : q = p := by
    rcases hq with hq | hq
    · exact hq
    · have h := hbad hq
      rw [ha] at h
      omega
  rw [hr, hqp, ha]
  simp [modelFactor, hg]

theorem ModularRealization.prefix_of_supported {e : Artifacts.CurveEquation}
    (m : ModularRealization e) (limit : ℕ) (hs : prefixSupported e limit = true) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (weierstrass e ℚ).LFunction (j + 1)) := by
  rw [modelCoefficients_eq_euler]
  apply List.map_congr_left
  intro j hj
  exact (m.coefficient_of_prefixSupported limit hs (j + 1) (by omega)
    (by have := List.mem_range.mp hj; omega)).symm

end VerifiedLcalc.Assumptions
