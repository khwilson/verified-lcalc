module

public import VerifiedLcalc.Certification.WildCertification
public import VerifiedLcalc.Certificate.LocalReductionSpecs
public import VerifiedLcalc.Certificate.LocalInvariantSpecs
public import VerifiedLcalc.EllipticCurve.Tate.Tamagawa
public import VerifiedLcalc.EllipticCurve.Tate.Kodaira
public import VerifiedLcalc.EllipticCurve.Tate.PotentialGoodReduction
public import VerifiedLcalc.Certificate.EllipticWitness
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.Localization.Rat

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

/-- Compute whether the reduced denominator of the rational j-invariant is one. -/
def jDenominatorIsOne (e : WeierstrassCurve ℤ) : Bool :=
  (((e.c₄ : ℚ) ^ 3 / (e.Δ : ℚ)).den == 1)

/-- A check on the reduced denominator certifies whether the rational j-invariant is an integer. -/
theorem j_integral_iff_of_check (e : WeierstrassCurve ℤ) [(e.baseChange ℚ).IsElliptic]
    (claimed : Bool) (h : jDenominatorIsOne e = claimed) :
    IsLocalization.IsInteger ℤ (e.baseChange ℚ).j ↔ claimed = true := by
  rw [← h, jDenominatorIsOne, beq_iff_eq, ← j_invariant_of_exact_formula e _ rfl,
    Rat.isLocalizationIsInteger_iff]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact Rat.den_intCast z
  · intro hj
    exact ⟨_, (Rat.den_eq_one_iff _).mp hj⟩

/-- The same finite check also certifies potential good reduction at all rational primes. -/
theorem potential_good_reduction_iff_of_check (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (claimed : Bool) (h : jDenominatorIsOne e = claimed) :
    HasEverywherePotentialGoodReduction (e.baseChange ℚ) ↔ claimed = true := by
  rw [hasEverywherePotentialGoodReduction_iff_j_den_eq_one, ← h, jDenominatorIsOne,
    beq_iff_eq, j_invariant_of_exact_formula e _ rfl]

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

/-- Repeated factors in the checked factorization detect squarefreeness of
the absolute minimal discriminant. -/
theorem squarefree_discriminant_iff_nodup (e : WeierstrassCurve ℤ)
    (m : MinimalityWitness) (hm : m.Valid e) : Squarefree e.Δ.natAbs ↔ m.primes.Nodup := by
  have hprime (p : ℕ) (hp : p ∈ m.primes) : p.Prime :=
    (isPrime_correct p).mp (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm.1 p hp)).1
  have hz : e.Δ.natAbs ≠ 0 := by
    rw [← hm.2]
    exact (List.prod_pos_iff_forall_pos_nat.mpr fun p hp => (hprime p hp).pos).ne'
  rw [Nat.squarefree_iff_nodup_primeFactorsList hz]
  exact (Nat.primeFactorsList_unique hm.2 hprime).nodup_iff.symm

/-- Standalone level identification, with the same explicit temporary
assumption boundary as analytic-rank certification. No numerical evaluator is needed. -/
theorem conductor_of_arithmetic_witness (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    [(e.baseChange ℚ).IsElliptic] (m : MinimalityWitness) (hm : m.Valid e)
    (d : WildData) (hd : d.Valid e) (N : Nat) (h : wildLevelFast e d = N) :
    (modularWitness e hn).level = N := by
  exact ((arithmeticModularWitness e hn).wildLevel_eq
    (globalMinimal_of_witness e m hm) d hd).trans ((wildLevel_eq_fast e d).trans h)

/-- A checked prime exponent of a natural number is its Mathlib factorization multiplicity. -/
theorem factorization_of_prime_exponent_check (p N exponent : Nat)
    (h : (isPrime p && padicValNat p N == exponent) = true) :
    p.Prime ∧ N.factorization p = exponent := by
  obtain ⟨hp, he⟩ := Bool.and_eq_true_iff.mp h
  have hp' := (isPrime_correct p).mp hp
  exact ⟨hp', by
    simpa only [beq_iff_eq, Nat.padicValNat_def, Nat.multiplicity_eq_factorization hp'] using he⟩

/-- Standalone Fricke/root-number identification under the authorized
arithmetic compatibility assumption. -/
theorem root_number_of_arithmetic_witness (e : WeierstrassCurve ℤ) (hn : e.Δ ≠ 0)
    [(e.baseChange ℚ).IsElliptic] (m : MinimalityWitness) (hm : m.Valid e)
    (d : WildData) (hd : d.Valid e) (w : Int) (h : wildSignFast e d = w) :
    (modularWitness e hn).rootNumber = w := by
  exact ((arithmeticModularWitness e hn).wildSign_eq
    (globalMinimal_of_witness e m hm) d hd).trans ((wildSign_eq_fast e d hd).trans h)

end VerifiedLcalc.Certification

namespace VerifiedLcalc
open EllipticCurve NumberField WeierstrassCurve

/-- Optional claims agree when any two supplied values are equal. -/
def OptionalValuesAgree {α : Type*} (a b : Option α) : Prop :=
  match a, b with
  | some x, some y => x = y
  | _, _ => True

instance {α : Type*} [DecidableEq α] (a b : Option α) :
    Decidable (OptionalValuesAgree a b) := by
  cases a <;> cases b <;> dsimp [OptionalValuesAgree] <;> infer_instance

/-- Single-valued local invariants supplied for the same prime must agree. -/
def LocalReductionClaim.Compatible (a b : LocalReductionClaim) : Prop :=
  a.prime = b.prime →
    OptionalValuesAgree a.discriminantValuation b.discriminantValuation ∧
    OptionalValuesAgree a.jDenominatorValuation b.jDenominatorValuation ∧
    OptionalValuesAgree a.reductionType b.reductionType ∧
    OptionalValuesAgree a.tamagawaNumber b.tamagawaNumber ∧
    OptionalValuesAgree a.kodairaSymbol b.kodairaSymbol ∧
    OptionalValuesAgree a.conductorValuation b.conductorValuation

instance (a b : LocalReductionClaim) : Decidable (a.Compatible b) := by
  unfold LocalReductionClaim.Compatible
  infer_instance

/-- Verify compatibility across every pair of supplied local rows. -/
def localReductionClaimsAgree (rows : List LocalReductionClaim) : Bool :=
  rows.all fun a => rows.all fun b => decide (a.Compatible b)

/-- The compatibility check gives agreement for every pair of input rows. -/
theorem localReductionClaimsAgree_correct (rows : List LocalReductionClaim)
    (h : localReductionClaimsAgree rows = true) :
    ∀ a ∈ rows, ∀ b ∈ rows, a.Compatible b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb)

/-- Finite checks use the actual integral equation and the reduced rational
formula for j. A reduction code is meaningful only at a bad prime.
The conductor exponent is checked separately against the checked modular level. -/
def LocalReductionClaim.check (row : LocalReductionClaim) (e : WeierstrassCurve ℤ) : Bool :=
  isPrime row.prime &&
    row.discriminantValuation.all (fun n => padicValNat row.prime e.Δ.natAbs == n) &&
    row.jDenominatorValuation.all (fun n =>
      padicValNat row.prime (((e.c₄ : Rat) ^ 3 / (e.Δ : Rat)).den) == n) &&
    row.reductionType.all (fun code =>
      !goodReduction e row.prime && singularTrace e row.prime == code) &&
    row.kodairaSymbol.all (checkKodairaCode e row.prime)

/-- Successful finite checks imply the claimed valuations and local reduction predicates. -/
theorem LocalReductionClaim.check_correct (row : LocalReductionClaim) (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (hm : IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ))
    (h : row.check e = true) : row.Spec e := by
  simp only [check, Bool.and_eq_true, Option.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hp, hd⟩, hj⟩, hr⟩, _⟩ := h
  have hp := (isPrime_correct _).mp hp
  let : Fact row.prime.Prime := ⟨hp⟩
  let hmin := hm.isMinimal (rationalPlace row.prime)
  have hpad (n : Nat) : padicValNat row.prime n = n.factorization row.prime := by
    simp only [Nat.padicValNat_def, Nat.multiplicity_eq_factorization hp]
  have hjFormula := Certification.j_invariant_of_exact_formula e
    ((e.c₄ : Rat) ^ 3 / (e.Δ : Rat)) rfl
  refine ⟨hp, hmin, ?_, ?_, ?_⟩
  · simpa only [hpad] using hd
  · simpa only [hpad, hjFormula] using hj
  · intro k hk
    obtain ⟨hg, ht⟩ := hr k hk
    have hbad : (row.prime : Int) ∣ e.Δ := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      simpa only [goodReduction, decide_eq_false_iff_not, not_not] using hg
    have htrace : (e.baseChange (ZMod row.prime)).frobeniusTrace = k :=
      (computeFrobeniusTrace_correct e row.prime).symm.trans
        ((singularTrace_correct e row.prime hg).symm.trans ht)
    refine ⟨?_, htrace⟩
    by_cases hc : (row.prime : Int) ∣ e.c₄
    · exact Or.inl ⟨(hasAdditiveReduction_at_iff e row.prime).mpr ⟨hbad, hc⟩,
        ht.symm.trans (by simp [singularTrace, Int.dvd_iff_emod_eq_zero.mp hc])⟩
    · have hc' : (e.baseChange (ZMod row.prime)).c₄ ≠ 0 := by
        simpa only [WeierstrassCurve.baseChange, map_c₄, eq_intCast, ne_eq,
          ZMod.intCast_zmod_eq_zero_iff_dvd] using hc
      have hs := hasNodeRoot_iff_splits e row.prime hc'
      have he : singularTrace e row.prime = (if hasNodeRoot e row.prime then 1 else -1) := by
        simp only [singularTrace, Int.dvd_iff_emod_eq_zero.not.mp hc, ite_false]
      have hmul := (hasMultiplicativeReduction_at_iff e row.prime).mpr ⟨hbad, hc⟩
      have hsplit := (hasSplitMultiplicativeReduction_at_iff e row.prime hmul).trans hs.symm
      refine Or.inr ⟨hmul, ?_⟩
      by_cases hroot : hasNodeRoot e row.prime = true
      · exact Or.inl ⟨ht.symm.trans (he.trans (ite_eq_left hroot)), hsplit.mpr hroot⟩
      · exact Or.inr ⟨ht.symm.trans (he.trans (ite_eq_right hroot)), mt hsplit.mp hroot⟩

/-- Check supplied local Tamagawa values whose reduction type is supported. -/
def LocalReductionClaim.checkTamagawa (row : LocalReductionClaim) (e : WeierstrassCurve ℤ) :
    Bool :=
  row.tamagawaNumber.all fun n =>
    isPrime row.prime && (n != 0) && (!supportsTamagawaOne e row.prime || n == 1)

/-- Successful local checks certify the completed-field Tamagawa factor at supported primes. -/
theorem LocalReductionClaim.tamagawa_correct (row : LocalReductionClaim) (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (h : row.checkTamagawa e = true) : row.TamagawaSpec e := by
  intro n hn
  simp only [checkTamagawa, hn, Option.all_some, Bool.and_eq_true, isPrime_correct] at h
  obtain ⟨⟨hp, _⟩, hval⟩ := h
  let : Fact row.prime.Prime := ⟨hp⟩
  refine ⟨hp, fun hs => ?_⟩
  have heq : n = 1 := by
    simpa only [hs, Bool.not_true, Bool.false_or, beq_iff_eq] using hval
  exact (supportsTamagawaOne_correct e row.prime hs).trans heq.symm

/-- Whether any supplied Tamagawa code falls outside the supported reduction scope. -/
def hasUnsupportedTamagawaClaim (e : WeierstrassCurve ℤ) (rows : List LocalReductionClaim) : Bool :=
  rows.any fun row => row.tamagawaNumber.isSome && !supportsTamagawaOne e row.prime

/-- Whether any supplied local valuation or reduction type requires a checked minimal model. -/
def hasMinimalityDependentLocalClaim (rows : List LocalReductionClaim) : Bool :=
  rows.any fun row => row.discriminantValuation.isSome || row.jDenominatorValuation.isSome ||
    row.reductionType.isSome || row.kodairaSymbol.isSome

/-- Whether any row requests a specific additive Kodaira code. -/
def hasAdditiveKodairaClaim (rows : List LocalReductionClaim) : Bool :=
  rows.any fun row => row.kodairaSymbol.any fun code => (kodairaIIndex code).isNone

/-- Successful finite local checks certify the supported Kodaira statement. -/
theorem LocalReductionClaim.kodaira_correct (row : LocalReductionClaim) (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (hn : e.Δ ≠ 0)
    (hm : IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)) (h : row.check e = true) :
    row.KodairaSpec e := by
  obtain ⟨hp, _⟩ := row.check_correct e hm h
  let : Fact row.prime.Prime := ⟨hp⟩
  let := hm.isMinimal (rationalPlace row.prime)
  refine ⟨hp, fun code hc => ?_⟩
  have hkod := (Bool.and_eq_true_iff.mp h).2
  rw [hc] at hkod
  exact checkKodairaCode_correct e row.prime hn code hkod

end VerifiedLcalc
