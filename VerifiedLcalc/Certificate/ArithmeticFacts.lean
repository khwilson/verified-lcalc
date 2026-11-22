/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certification.StoredInvariants

/-! # Proof-carrying arithmetic data of one rational curve

Finite checks retain their actual mathematical types. The conductor, sign and
level exponents take an explicit arithmetic modular realization as input.
-/

public section

namespace VerifiedLcalc

open EllipticCurve NumberField WeierstrassCurve

/-- Arithmetic facts conditional on an explicit modular realization of the curve. -/
structure ModularArithmeticFacts (curve : WeierstrassCurve ℤ) where
  /-- The checked level of the modular realization. -/
  conductor : Option { n : ℕ //
    ∀ M : Modularity.ArithmeticModularRealization curve, M.level = n } := none
  /-- The checked root number of the modular realization. -/
  rootNumber : Option { w : ℤ //
    ∀ M : Modularity.ArithmeticModularRealization curve, M.rootNumber = w } := none
  /-- Checked prime-power exponents of the level, for the supplied primes only. -/
  conductorValuations : Option { rows : List (ℕ × ℕ) //
    ∀ M : Modularity.ArithmeticModularRealization curve,
      ∀ row ∈ rows, row.1.Prime ∧ M.level.factorization row.1 = row.2 } := none

/-- Arithmetic facts about a verified globally minimal integral model of the curve. -/
structure MinimalModelArithmeticFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The checked factorization and the resulting global minimality theorem. -/
  minimality : { m : MinimalityWitness //
    m.Valid curve ∧ IsGlobalMinimal (𝓞 ℚ) (curve.baseChange ℚ) }
  /-- The supplied absolute minimal discriminant. -/
  minimalDiscriminantAbs : Option { d : ℕ //
    IsGlobalMinimal (𝓞 ℚ) (curve.baseChange ℚ) ∧ curve.Δ.natAbs = d } := none
  /-- Whether the rational curve has semistable reduction. -/
  semistable : Option { b : Bool //
    IsSemistable (𝓞 ℚ) (curve.baseChange ℚ) ↔ b = true } := none
  /-- Whether the absolute minimal discriminant is squarefree. -/
  squarefreeDiscriminant : Option { b : Bool // Squarefree curve.Δ.natAbs ↔ b = true } := none
  /-- The complete, duplicate-free list of bad primes. -/
  badPrimes : Option { ps : List ℕ //
    ps.Nodup ∧
      (∀ p : ℕ, p ∈ ps ↔ p.Prime ∧ (p : ℤ) ∣ curve.Δ) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∈ ps ↔ ¬ (curve.baseChange (ZMod p)).IsElliptic } := none
  /-- The number of primes dividing the checked minimal discriminant. -/
  numBadPrimes : Option { n : ℕ // curve.Δ.natAbs.primeFactors.card = n } := none
  /-- Checked local rows. Level exponents belong to the modular subrecord. -/
  localRows : Option { rows : List LocalReductionClaim // ∀ row ∈ rows,
    row.conductorValuation = none ∧ row.Spec curve } := none

/-- Optional arithmetic facts indexed by the same nonsingular integral equation. -/
structure ArithmeticFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The global minimality proof and all facts that refer to this minimal model. -/
  minimalModel : Option (MinimalModelArithmeticFacts curve) := none
  /-- Validity of the supplied finite arithmetic transcripts. -/
  localData : Option { d : WildData // d.Valid curve } := none
  /-- Whether the curve has potential good reduction at every rational prime. -/
  potentialGoodReduction : Option { b : Bool //
    HasEverywherePotentialGoodReduction (curve.baseChange ℚ) ↔ b = true } := none
  /-- The supplied prime-indexed coefficients of the actual rational L-function. -/
  primeCoefficients : Option { rows : List (ℕ × ℤ) //
    ∀ (p : ℕ) (a : ℤ), (p, a) ∈ rows → (curve.baseChange ℚ).LFunction p = a } := none
  /-- The supplied consecutive coefficients of the rational L-function. -/
  dirichletCoefficients : Option { values : List ℤ //
    (List.range values.length).map (fun n => (curve.baseChange ℚ).LFunction (n + 1)) =
      values } := none
  /-- Conditional level and sign facts requiring an explicit realization. -/
  modular : ModularArithmeticFacts curve := {}

end VerifiedLcalc
