module

public import VerifiedLcalc.EllipticCurve.GlobalCoefficients

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The elementary model-count bound also applies to mathlib's chosen minimal
reductions, without identifying them with a particular input equation. -/
theorem trace_abs_le_square_of_card {F : Type*} [Field F] [Finite F]
    (W : WeierstrassCurve F) (p : ℕ) (hp : 1 ≤ p) (hc : Nat.card F = p) :
    |W.frobeniusTrace| ≤ (p : ℤ) ^ 2 := by
  have hs : Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≤ p ^ 2 := by
    have h := Nat.card_le_card_of_injective
      (fun xy : {xy : F × F // W.toAffine.Equation xy.1 xy.2} => xy.1) Subtype.val_injective
    simpa [Nat.card_prod, hc, pow_two] using h
  have hs' : (Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} : ℤ) ≤ (p : ℤ) ^ 2 := by
    exact_mod_cast hs
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hpp : (p : ℤ) ≤ (p : ℤ) ^ 2 := le_self_pow₀ hp' (by decide)
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.pointCount_def, hc]
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith [Int.natCast_nonneg (Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2})]

section Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [Finite (IsLocalRing.ResidueField R)]

/-- At bad reduction, the first local coefficient has absolute value at most
one. This is proved from mathlib's three bad Euler polynomials. -/
theorem bad_reduction_trace_abs_le_one (W : WeierstrassCurve K)
    (hg : ¬ (W.minimal R).HasGoodReduction R) :
    |((W.minimal R).reduction R).frobeniusTrace| ≤ 1 := by
  have h := W.localPolynomial_eq_of_not_hasGoodReduction R hg
  unfold WeierstrassCurve.localPolynomial at h
  rw [ite_eq_right hg] at h
  split_ifs at h <;>
    have he := congrArg (fun P : Polynomial ℤ => P.coeff 1) h <;>
    simp at he <;> simp only [abs_le, WeierstrassCurve.frobeniusTrace_def,
      WeierstrassCurve.pointCount_def] <;> push_cast at * <;> omega

end Local

/-- Every rational curve coefficient at prime powers satisfies the actual local
recurrence. The quadratic coefficient is p at good reduction and zero at bad
reduction; no supplied equation is assumed minimal. -/
theorem LFunction_primePower_recurrence (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] :
    ∃ q : ℤ, (q = p ∨ q = 0) ∧ |q| ≤ p ∧
      |W.LFunction p| ≤ (p : ℤ) ^ 2 ∧
      (∀ k : ℕ, W.LFunction (p ^ k) = localCoefficient (W.LFunction p) q k) ∧
      (q = 0 → |W.LFunction p| ≤ 1) := by
  classical
  let v := rationalPlace p
  let R := v.adicCompletionIntegers ℚ
  let Wv := W.baseChange (v.adicCompletion ℚ)
  let a := ((Wv.minimal R).reduction R).frobeniusTrace
  let q : ℤ := if (Wv.minimal R).HasGoodReduction R then p else 0
  have hc : Nat.card (IsLocalRing.ResidueField R) = p := by
    rw [completion_residue_card, rationalPlace_norm]
  have hpoly : Wv.localPolynomial R =
      1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 := by
    dsimp [q]
    split_ifs with hg
    · rw [Wv.localPolynomial_eq_of_hasGoodReduction R hg, hc]
    · rw [Wv.localPolynomial_eq_of_not_hasGoodReduction R hg]
      simp [a]
  have hr (k : ℕ) : W.LFunction (p ^ k) = localCoefficient a q k := by
    rw [LFunction_apply_prime_pow, localPowerSeries_eq_localSeries Wv a q hpoly]
    exact localSeries_correct a q k
  have ha : W.LFunction p = a := by simpa [localCoefficient, localPair] using hr 1
  have hab : |a| ≤ (p : ℤ) ^ 2 :=
    trace_abs_le_square_of_card _ p (Fact.out : p.Prime).one_lt.le hc
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [q]; split <;> simp
  · dsimp [q]; split <;> simp
  · rwa [ha]
  · intro k; simpa only [ha] using hr k
  · intro hq
    have hg : ¬ (Wv.minimal R).HasGoodReduction R := by
      intro hg
      have : (p : ℤ) = 0 := by simpa [q, hg] using hq
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
    rw [ha]
    exact bad_reduction_trace_abs_le_one Wv hg

/-- A global bound on actual rational-curve coefficients. It uses the real
Euler product, chosen minimal reductions and elementary counting, with no
modularity axiom or input-model compatibility hypothesis. -/
theorem LFunction_abs_le_cube (W : WeierstrassCurve ℚ) (n : ℕ) :
    |W.LFunction n| ≤ (n : ℤ) ^ 3 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ W.isMultiplicative_LFunction hn]
  unfold Finsupp.prod
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ p ∈ n.factorization.support, (p : ℤ) ^ (3 * n.factorization p) := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      let : Fact p.Prime := ⟨hp'⟩
      obtain ⟨q, _, hq, ha, hr, _⟩ := LFunction_primePower_recurrence W p
      change |W.LFunction (p ^ n.factorization p)| ≤ _
      rw [hr]
      exact localCoefficient_abs_le_cube_power p hp'.two_le _ _ ha hq _
    _ = (n : ℤ) ^ 3 := by
      simp_rw [Nat.mul_comm 3, pow_mul]
      rw [Finset.prod_pow]
      have he : (∏ p ∈ n.factorization.support, (p : ℤ) ^ n.factorization p) = n := by
        exact_mod_cast Nat.prod_factorization_pow_eq_self hn
      rw [he]

end VerifiedLcalc.EllipticCurve
