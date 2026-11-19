module

public import VerifiedLcalc.EllipticCurve.Tate.TwoAdicMinimality
public import VerifiedLcalc.EllipticCurve.Tate.InvariantMinimality

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- Every successful executable local minimality check proves local minimality. -/
private theorem baseMinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (h : (discriminantMinimalAt e p || twoAdicC4MinimalAt e p) = true) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact minimal_at_of_discriminant_not_dvd e p ((discriminantMinimalAt_correct e p).mp h)
  · have hc : p = 2 ∧ e.c₄ % 64 = 0 ∧ e.c₄ % 128 ≠ 0 := by
      simpa only [twoAdicC4MinimalAt, decide_eq_true_eq] using h
    obtain ⟨rfl, h6, h7⟩ := hc
    apply minimal_at_two_of_c4 e
    · simpa only [Int.reducePow, Int.dvd_iff_emod_eq_zero] using h6
    · simpa only [Int.reducePow, Int.dvd_iff_emod_eq_zero] using h7

/-- Soundness of every executable sufficient criterion in the dispatcher. -/
theorem modelMinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (h : modelMinimalAt e p = true) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact baseMinimalAt_correct e p h
  · exact invariantMinimalAt_correct e p h

/-- Standalone correctness theorem for the executable 2-adic c4 check. -/
theorem twoAdicC4MinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (h : twoAdicC4MinimalAt e p = true) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  apply modelMinimalAt_correct e p
  simp only [modelMinimalAt, h, Bool.or_true, Bool.true_or]

private theorem prime_eq_member_of_dvd_prod (p : ℕ) (hp : p.Prime)
    (xs : List ℕ) (hx : xs.all isPrime = true) (hd : p ∣ xs.prod) : p ∈ xs := by
  induction xs with
  | nil => simpa using hp.not_dvd_one hd
  | cons a xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hx
    rcases hp.dvd_mul.mp hd with h | h
    · have heq : p = a := ((Nat.dvd_prime ((isPrime_correct a).mp hx.1)).mp h).resolve_left hp.ne_one
      exact List.mem_cons.mpr (Or.inl heq)
    · exact List.mem_cons_of_mem a (ih hx.2 h)

/-- A checked finite factorization certifies minimality at every finite place,
including additive primes in characteristics two and three. -/
theorem minimal_of_witness (e : (WeierstrassCurve ℤ)) (w : MinimalityWitness)
    (hw : w.Valid e) (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  by_cases hpd : (p : ℤ) ∣ e.Δ
  · apply modelMinimalAt_correct e p
    have hall : w.primes.all isPrime = true := by
      rw [List.all_eq_true]
      intro q hq
      exact Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hw.1) q hq) |>.1
    have hmem : p ∈ w.primes := prime_eq_member_of_dvd_prod p Fact.out w.primes hall
      (by rw [hw.2]; exact Int.natCast_dvd.mp hpd)
    exact Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hw.1) p hmem) |>.2
  · apply minimal_at_of_discriminant_not_dvd e p
    intro hd
    exact hpd (dvd_trans (dvd_pow_self (p : ℤ) (by decide : 12 ≠ 0)) hd)

end VerifiedLcalc.EllipticCurve
