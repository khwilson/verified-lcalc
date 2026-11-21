module

public import VerifiedLcalc.Certification.WildCertification

/-! Bridges from exact stored invariant checks to existing Mathlib/TauCeti
objects. Only the conductor and root-number bridges use the authorized
modularity/arithmetic-compatibility assumption. -/

@[expose] public section
namespace VerifiedLcalc.Certification
open EllipticCurve Modularity NumberField

/-- Mathlib's actual j-invariant, evaluated by an exact rational formula. -/
theorem j_invariant_of_exact_formula (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (q : Rat)
    (h : (e.c₄ : Rat) ^ 3 / (e.Δ : Rat) = q) : (e.baseChange ℚ).j = q := by
  rw [WeierstrassCurve.j_eq]
  simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄,
    WeierstrassCurve.map_Δ, eq_intCast, map_intCast, div_eq_mul_inv, mul_comm] using h

/-- An absD claim includes actual global minimality, not just agreement with
the discriminant of an arbitrary supplied equation. -/
theorem minimal_discriminant_abs_of_witness (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (m : MinimalityWitness) (hm : m.Valid e)
    (d : Nat) (h : e.Δ.natAbs = d) :
    WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) ∧ e.Δ.natAbs = d :=
  ⟨globalMinimal_of_witness e m hm, h⟩

/-- Stored coefficients are the actual arithmetic-function coefficients of
the curve, with no modularity assumption. The list starts at n=1. -/
theorem coefficients_of_minimal_witness (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    (m : MinimalityWitness) (hm : m.Valid e) (values : List Int)
    (h : modelCoefficients e values.length = values) :
    (List.range values.length).map (fun n => (e.baseChange ℚ).LFunction (n + 1)) = values := by
  rw [← minimal_prefix e hn (minimal_of_witness e m hm)]
  exact h

/-- The supplied complete factorization identifies exactly the prime divisors
of the discriminant, including primes omitted from an incorrect database list. -/
theorem minimal_prime_mem_iff (e : WeierstrassCurve ℤ) (m : MinimalityWitness)
    (hm : m.Valid e) (p : Nat) : p ∈ m.primes ↔ p.Prime ∧ (p : Int) ∣ e.Δ := by
  have hp : ∀ q ∈ m.primes, q.Prime := by
    intro q hq
    exact (isPrime_correct q).mp (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hm.1 q hq)).1
  constructor
  · intro h
    exact ⟨hp p h, Int.natCast_dvd.mpr (by rw [← hm.2]; exact List.dvd_prod h)⟩
  · rintro ⟨hprime, hdiv⟩
    exact mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hprime)
      (fun q hq => Nat.prime_iff.mp (hp q hq)) (by rw [hm.2]; exact Int.natCast_dvd.mp hdiv)

theorem minimal_primes_toFinset (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    (m : MinimalityWitness) (hm : m.Valid e) : m.primes.toFinset = e.Δ.natAbs.primeFactors := by
  have hz : e.Δ.natAbs ≠ 0 := by simpa using hn
  ext p
  rw [List.mem_toFinset]
  constructor
  · intro h
    obtain ⟨hp, hd⟩ := (minimal_prime_mem_iff e m hm p).mp h
    exact Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hd, hz⟩
  · intro h
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp h
    exact (minimal_prime_mem_iff e m hm p).mpr ⟨hp, Int.natCast_dvd.mpr hd⟩

/-- Bad reduction is expressed using Mathlib's ellipticity of the actual
finite-field reduction of the checked minimal equation. -/
theorem bad_reduction_prime_iff (e : WeierstrassCurve ℤ) (values : List Nat)
    (h : ∀ p, p ∈ values ↔ p.Prime ∧ (p : Int) ∣ e.Δ) (p : Nat) [Fact p.Prime] :
    p ∈ values ↔ ¬ (e.baseChange (ZMod p)).IsElliptic := by
  have hp : p.Prime := Fact.out
  simpa only [hp, true_and, WeierstrassCurve.isElliptic_iff,
    isUnit_iff_ne_zero, not_not, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ,
    eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] using h p

/-- Standalone level identification, with the same explicit temporary
assumption boundary as analytic-rank certification. No numerical evaluator is needed. -/
theorem conductor_of_arithmetic_witness (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    [(e.baseChange ℚ).IsElliptic] (m : MinimalityWitness) (hm : m.Valid e)
    (d : WildData) (hd : d.Valid e) (N : Nat) (h : wildLevelFast e d = N) :
    (modularWitness e hn).level = N := by
  exact ((arithmeticModularWitness e hn).wildLevel_eq
    (globalMinimal_of_witness e m hm) d hd).trans ((wildLevel_eq_fast e d).trans h)

/-- Standalone Fricke/root-number identification under the authorized
arithmetic compatibility assumption. -/
theorem root_number_of_arithmetic_witness (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    [(e.baseChange ℚ).IsElliptic] (m : MinimalityWitness) (hm : m.Valid e)
    (d : WildData) (hd : d.Valid e) (w : Int) (h : wildSignFast e d = w) :
    (modularWitness e hn).rootNumber = w := by
  exact ((arithmeticModularWitness e hn).wildSign_eq
    (globalMinimal_of_witness e m hm) d hd).trans ((wildSign_eq_fast e d hd).trans h)

end VerifiedLcalc.Certification
