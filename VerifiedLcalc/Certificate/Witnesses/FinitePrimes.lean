/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Invariants
public import VerifiedLcalc.Certificate.LocalReductionSpecs
public import VerifiedLcalc.EllipticCurve.Tate.PotentialGoodReductionSpec
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-! # Reduction at finite primes and arithmetic coefficients

* `LocalTamagawaFact` identifies the intrinsic Tamagawa number at a specified rational prime.
  `LocalKodairaFact` gives the exact `Iₙ` index or excludes the entire `Iₙ` family.
* `MinimalModelArithmeticFacts` starts with checked global minimality and collects
  discriminant, bad-prime, semistability, and local reduction data on that model.
* `ArithmeticFacts` collects optional minimal-model facts, intrinsic Tamagawa factors,
  finite transcript validity, potential good reduction, and prime-indexed and consecutive
  L-function coefficients. Its modular facts require an explicit arithmetic realization.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve NumberField WeierstrassCurve

/-- An intrinsic local Tamagawa factor with its completed-field equality. -/
structure LocalTamagawaFact (curve : WeierstrassCurve ℤ) where
  /-- The prime at which the factor was checked. -/
  prime : Nat.Primes
  /-- The verified local factor. -/
  value : ℕ
  /-- The factor agrees with the intrinsic local invariant of this curve. -/
  correct :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    (curve.baseChange ℚ).tamagawaNumberAt (rationalPlace (prime : ℕ)) = value

/-- An exact multiplicative-family index, or a proof of additive reduction at this prime. -/
structure LocalKodairaFact (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- The prime at which the reduction symbol was checked. -/
  prime : Nat.Primes
  /-- The index of `Iₙ`, with `none` denoting the additive family. -/
  index : Option ℕ
  /-- An equality for the exact index, or exclusion of every `Iₙ`. -/
  correct :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    match index with
    | some n => (curve.baseChange ℚ).reductionSymbol (RationalLocalRing (prime : ℕ)) = .I n
    | none => ∀ n, (curve.baseChange ℚ).reductionSymbol (RationalLocalRing (prime : ℕ)) ≠ .I n

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
    row.conductorValuation = none ∧ row.kodairaSymbol = none ∧
      row.tamagawaNumber = none ∧ row.Spec curve } := none
  /-- Checked canonical Kodaira facts at the supplied primes. -/
  kodaira : List (LocalKodairaFact curve) := []

/-- Optional arithmetic facts indexed by the same nonsingular integral equation. -/
structure ArithmeticFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The global minimality proof and all facts that refer to this minimal model. -/
  minimalModel : Option (MinimalModelArithmeticFacts curve) := none
  /-- Supplied and checked intrinsic local factors, independent of global minimality. -/
  tamagawa : List (LocalTamagawaFact curve) := []
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
