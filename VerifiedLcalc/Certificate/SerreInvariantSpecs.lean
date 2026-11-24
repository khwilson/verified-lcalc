/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.List.Sort

/-!
# The semistable Serre recipe

For a globally minimal semistable model with good reduction at two, Serre's local
rules compute the weight and prime-to-ℓ conductor of the residual representation
from the valuations of the absolute minimal discriminant. See Serre,
*Sur les représentations modulaires de degré 2 de Gal(Q̄/Q)*, Proposition 5
and §§4.1.11–12, DOI 10.1215/S0012-7094-87-05413-5.

This module proves completeness of the finite enumeration for those formulas.
The general comparison with intrinsic Galois-theoretic invariants is external.
-/

@[expose] public section

namespace VerifiedLcalc

/-- The usual pair of weight and conductor for the semistable recipe. -/
def usualSerrePair (d : ℕ) : ℕ × ℕ :=
  (2, d.primeFactors.prod id)

/-- Serre's semistable formulas in terms of the absolute minimal discriminant. -/
def semistableSerrePair (d p : ℕ) : ℕ × ℕ :=
  (if p ∣ d.factorization p then 2 else p + 1,
    (d.primeFactors.filter fun q => q ≠ p ∧ ¬ p ∣ d.factorization q).prod id)

/-- Primes of bad reduction and prime divisors of their discriminant valuations. -/
def serreCandidatePrimes (d : ℕ) : List ℕ :=
  (d.primeFactorsList ++ d.primeFactorsList.flatMap fun q =>
    (d.factorization q).primeFactorsList).eraseDups

private theorem mem_serreCandidatePrimes {d p : ℕ} :
    p ∈ serreCandidatePrimes d ↔
      p ∈ d.primeFactors ∨ ∃ q ∈ d.primeFactors,
        p ∈ (d.factorization q).primeFactors := by
  simp [serreCandidatePrimes]

/-- Outside the finite candidate set the semistable recipe returns the usual pair. -/
theorem semistableSerrePair_eq_usual_of_notMem (d : ℕ) {p : ℕ} (hp : p.Prime)
    (h : p ∉ serreCandidatePrimes d) : semistableSerrePair d p = usualSerrePair d := by
  have hp' : p ∉ d.primeFactors := fun hm =>
    h (mem_serreCandidatePrimes.mpr (Or.inl hm))
  have hval : d.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa using hp'
  have hfilter :
      (d.primeFactors.filter fun q => q ≠ p ∧ ¬ p ∣ d.factorization q) =
        d.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    have hqval : d.factorization q ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      simpa using hq
    refine ⟨fun he => hp' (he ▸ hq), fun hd => h ?_⟩
    exact mem_serreCandidatePrimes.mpr
      (Or.inr ⟨q, hq, Nat.mem_primeFactors.mpr ⟨hp, hd, hqval⟩⟩)
  simp [semistableSerrePair, usualSerrePair, hval, hfilter]

/-- The entire list of exceptional triples in increasing order of prime. -/
def semistableSerreInvariants (d : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((serreCandidatePrimes d).filter fun p =>
    decide (semistableSerrePair d p ≠ usualSerrePair d)).insertionSort (· ≤ ·) |>.map
      fun p => (p, semistableSerrePair d p)

/-- The enumeration contains precisely every prime and its exceptional pair. -/
theorem mem_semistableSerreInvariants_iff (d p k n : ℕ) :
    (p, k, n) ∈ semistableSerreInvariants d ↔
      p.Prime ∧ (k, n) = semistableSerrePair d p ∧ (k, n) ≠ usualSerrePair d := by
  unfold semistableSerreInvariants
  simp only [List.mem_map, List.mem_insertionSort, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, ⟨hq, he⟩, h⟩
    have hprime : q.Prime := by
      rcases mem_serreCandidatePrimes.mp hq with hq | ⟨_, _, hq⟩
      · exact Nat.prime_of_mem_primeFactors hq
      · exact Nat.prime_of_mem_primeFactors hq
    obtain ⟨rfl, hpair⟩ := Prod.mk.inj h
    exact ⟨hprime, hpair.symm, hpair ▸ he⟩
  · rintro ⟨hp, hpair, he⟩
    have hne : semistableSerrePair d p ≠ usualSerrePair d := hpair ▸ he
    refine ⟨p, ⟨?_, hne⟩, congrArg (fun pair => (p, pair)) hpair.symm⟩
    by_contra hn
    exact hne (semistableSerrePair_eq_usual_of_notMem d hp hn)

end VerifiedLcalc
