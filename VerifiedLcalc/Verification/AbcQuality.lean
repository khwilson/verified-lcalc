/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Verification.StoredInvariants
public import VerifiedLcalc.Numerics.RealInterval
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log
public import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality
public import VerifiedLcalc.Certificate.Witnesses.Invariants

/-!
# Certified error bounds for elliptic-curve abc quality

The witness factors the integer product from the reduced abc triple of j/1728.
Mathlib's dyadic logarithm gives a certified error interval about the reported value.
-/

@[expose] public section

namespace VerifiedLcalc.Certification

open EllipticCurve Numerics Inclusion.IntervalDyadicReal UniqueFactorizationMonoid

/-- The rational j-invariant evaluated using only the supplied coefficients. -/
def abcJ (e : WeierstrassCurve ℤ) : ℚ := (e.c₄ : ℚ) ^ 3 / (e.Δ : ℚ)

/-- The largest absolute component of the abc triple of j/1728. -/
def abcMaximum (j : ℚ) : ℕ :=
  let t := j / 1728
  let c : ℤ := t.den
  max (max t.num.natAbs (c - t.num).natAbs) c.natAbs

/-- The absolute product of the abc triple of j/1728. -/
def abcProduct (j : ℚ) : ℕ :=
  let t := j / 1728
  let c : ℤ := t.den
  (t.num * (c - t.num) * c).natAbs

/-- Logarithm bounds for a natural number using exact dyadic range reduction. -/
def logNatBounds (n : ℕ) : RealInterval :=
  let lo := (lowerLog ((n : ℤ) : Dyadic) 64).toRat
  (lo, lo + (Dyadic.step 64).toRat)

/-- The directed bounds contain the actual logarithm. -/
theorem logNatBounds_sound (n : ℕ) : (logNatBounds n).Contains (Real.log n) := by
  simpa [logNatBounds, RealInterval.Contains] using lowerLog_spec ((n : ℤ) : Dyadic) 64

/-- Check an error bound on a quotient enclosed by two rational intervals. -/
def ratioErrorValid (num den : RealInterval) (reported error : ℚ) : Bool :=
  let lo := reported - error
  let hi := reported + error
  decide (0 ≤ error ∧ 0 < den.1 ∧
    (intervalMul (lo, lo) den).2 ≤ num.1 ∧
    num.2 ≤ (intervalMul (hi, hi) den).1)

/-- A successful interval check proves the requested error bound on the real quotient. -/
theorem ratioErrorValid_sound {num den : RealInterval} {n d : ℝ}
    (hn : num.Contains n) (hd : den.Contains d) {reported error : ℚ}
    (h : ratioErrorValid num den reported error = true) :
    |n / d - (reported : ℝ)| ≤ (error : ℝ) := by
  let lo := reported - error
  let hi := reported + error
  simp only [ratioErrorValid, decide_eq_true_eq] at h
  have hd₀ : (0 : ℝ) < (den.1 : ℝ) := by exact_mod_cast h.2.1
  have hdpos : 0 < d := hd₀.trans_le hd.1
  have hl := intervalMul_sound (lo, lo) den (lo : ℝ) d ⟨le_rfl, le_rfl⟩ hd
  have hu := intervalMul_sound (hi, hi) den (hi : ℝ) d ⟨le_rfl, le_rfl⟩ hd
  have hleft : ((intervalMul (lo, lo) den).2 : ℝ) ≤ (num.1 : ℝ) := by
    exact_mod_cast h.2.2.1
  have hright : (num.2 : ℝ) ≤ ((intervalMul (hi, hi) den).1 : ℝ) := by
    exact_mod_cast h.2.2.2
  have left := (le_div_iff₀ hdpos).mpr (hl.2.trans (hleft.trans hn.1))
  have right := (div_le_iff₀ hdpos).mpr (hn.2.trans (hright.trans hu.1))
  simp only [lo, hi, Rat.cast_sub, Rat.cast_add] at left right
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Check the factorization and error bound with integer and rational arithmetic. -/
def abcQualityValid (e : WeierstrassCurve ℤ) (claim : AbcQualityClaim) : Bool :=
  let j := abcJ e
  let radical := claim.factors.toFinset.prod id
  decide (j ≠ 0 ∧ j ≠ 1728 ∧ claim.factors.prod = abcProduct j ∧
    claim.factors.all isPrime = true ∧
    ratioErrorValid (logNatBounds (abcMaximum j)) (logNatBounds radical)
      claim.reported claim.error = true)

/-- The exact abc quality is defined for every accepted witness. -/
theorem abc_quality_defined_of_check (e : WeierstrassCurve ℤ) [(e.baseChange ℚ).IsElliptic]
    (claim : AbcQualityClaim) (h : abcQualityValid e claim = true) :
    (e.baseChange ℚ).j ≠ 0 ∧ (e.baseChange ℚ).j ≠ 1728 := by
  simp only [abcQualityValid, decide_eq_true_eq] at h
  rw [j_invariant_of_exact_formula e (abcJ e) rfl]
  exact ⟨h.1, h.2.1⟩

/-- An accepted witness proves an absolute error bound on TauCeti's actual abc quality. -/
theorem abc_quality_of_check (e : WeierstrassCurve ℤ) [(e.baseChange ℚ).IsElliptic]
    (claim : AbcQualityClaim) (h : abcQualityValid e claim = true)
    (hdefined : (e.baseChange ℚ).j ≠ 0 ∧ (e.baseChange ℚ).j ≠ 1728) :
    |(e.baseChange ℚ).abcQuality hdefined - (claim.reported : ℝ)| ≤ (claim.error : ℝ) := by
  simp only [abcQualityValid, decide_eq_true_eq] at h
  have hperm := Nat.primeFactorsList_unique h.2.2.1 fun p hp =>
    (isPrime_correct p).mp (List.all_eq_true.mp h.2.2.2.1 p hp)
  have hrad : claim.factors.toFinset.prod id = radical (abcProduct (abcJ e)) := by
    rw [Nat.radical_eq_prod_primeFactors]
    congr 1
    ext p
    simpa only [← Nat.toFinset_factors, List.mem_toFinset] using hperm.mem_iff (a := p)
  have hb := ratioErrorValid_sound (logNatBounds_sound (abcMaximum (abcJ e)))
    (logNatBounds_sound (claim.factors.toFinset.prod id)) h.2.2.2.2
  rw [hrad] at hb
  rw [(e.baseChange ℚ).abcQuality_def hdefined, j_invariant_of_exact_formula e (abcJ e) rfl]
  simpa only [abcMaximum, abcProduct, Nat.cast_max] using hb

/-- A successful backend check retains its Boolean audit and projects to the
mathematical rational-invariant contract. -/
structure CheckedAbcQualityFacts (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] where
  /-- The corresponding mathematical statement about TauCeti's quality. -/
  facts : AbcQualityFacts e
  /-- The checker result remains available to compatibility consumers. -/
  valid : abcQualityValid e facts.claim = true

/-- Convert checked transcript evidence into the public mathematical contract. -/
def abcQualityFactsOfCheck (e : WeierstrassCurve ℤ) [(e.baseChange ℚ).IsElliptic]
    (claim : AbcQualityClaim) (h : abcQualityValid e claim = true) :
    CheckedAbcQualityFacts e := by
  have hdefined := abc_quality_defined_of_check e claim h
  have hfactor : claim.factors.prod =
      let t := (e.baseChange ℚ).j / 1728
      let c : ℤ := t.den
      (t.num * (c - t.num) * c).natAbs := by
    simp only [abcQualityValid, decide_eq_true_eq] at h
    simpa [abcJ, abcProduct, j_invariant_of_exact_formula e (abcJ e) rfl] using h.2.2.1
  have hprime : ∀ p ∈ claim.factors, p.Prime := by
    simp only [abcQualityValid, decide_eq_true_eq] at h
    exact fun p hp => (isPrime_correct p).mp (List.all_eq_true.mp h.2.2.2.1 p hp)
  have herr := abc_quality_of_check e claim h hdefined
  exact ⟨⟨claim, hdefined, hfactor, hprime, herr⟩, h⟩

end VerifiedLcalc.Certification
