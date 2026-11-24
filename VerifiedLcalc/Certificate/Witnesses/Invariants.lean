/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.InvariantSpecs
public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealizationData
public import TauCeti.AlgebraicGeometry.EllipticCurve.AbcQuality
public import Mathlib.RingTheory.Localization.Rat
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-! # Global invariants of an elliptic curve

* `DiscriminantWitness` packages an equation with its exact discriminant.
  `EllipticProofs` provides optional proofs of discriminant, b-invariants and c-invariants for
  an indexed equation over a commutative ring.
* `RationalInvariantFacts` records discriminant sign, rational j-invariant and its
  integrality, and abc quality. `AbcQualityFacts` supplies a factorization and quality
  enclosure for j distinct from 0 and 1728.
* `ModifiedSzpiroRatioFacts` bounds the error in the reported modified Szpiro ratio of a
  globally minimal equation, using the norm of TauCeti's algorithmic conductor.
* `ModularArithmeticFacts` records conductor, root number, and conductor exponents at supplied
  primes, conditional on an explicit arithmetic modular realization.
  `Certification.ArithmeticCompatibility` pairs one realization with its conductor and
  root number equalities.
-/

@[expose] public section

/-! ## Weierstrass invariants and abc quality -/

namespace VerifiedLcalc

open EllipticCurve

/-- A discriminant value together with the equation and its exact proof. -/
structure DiscriminantWitness (R : Type*) [CommRing R] where
  /-- The equation whose discriminant is certified. -/
  curve : WeierstrassCurve R
  /-- The value of the discriminant. -/
  discriminant : R
  /-- The discriminant of the supplied equation equals the supplied value. -/
  discriminant_eq : curve.Δ = discriminant

/-- Optional proved facts about one fixed Weierstrass equation. -/
structure EllipticProofs {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- A discriminant value with a proof about the indexed equation. -/
  discriminant : Option { d : R // curve.Δ = d } := none
  /-- The ordered tuple of b₂, b₄, b₆ and b₈ with a proof about the equation. -/
  bInvariants : Option { b : R × R × R × R //
    (curve.b₂, curve.b₄, curve.b₆, curve.b₈) = b } := none
  /-- The ordered pair of c₄ and c₆ with a proof about the equation. -/
  cInvariants : Option { c : R × R // (curve.c₄, curve.c₆) = c } := none

/-- A factorization transcript and enclosure for the actual abc quality. -/
structure AbcQualityFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The submitted rational report and factor list. -/
  claim : AbcQualityClaim
  /-- The domain condition for TauCeti's abc quality. -/
  defined : (curve.baseChange ℚ).j ≠ 0 ∧ (curve.baseChange ℚ).j ≠ 1728
  /-- The supplied factors multiply to the reduced abc product of `j / 1728`. -/
  factorization : claim.factors.prod = Certification.abcProduct (curve.baseChange ℚ).j
  /-- Every supplied factor is prime. -/
  primeFactors : ∀ p ∈ claim.factors, p.Prime
  /-- The actual TauCeti quality lies within the claimed absolute error. -/
  within_error :
    |(curve.baseChange ℚ).abcQuality defined - (claim.reported : ℝ)| ≤
      (claim.error : ℝ)

/-- Rational invariant facts whose conclusions directly name mathematical objects. -/
structure RationalInvariantFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The sign of the integral equation's discriminant. -/
  discriminantSign : Option { s : ℤ // curve.Δ.sign = s } := none
  /-- The j-invariant of the rational curve. -/
  jInvariant : Option { j : ℚ // (curve.baseChange ℚ).j = j } := none
  /-- The truth value for integrality of the rational j-invariant. -/
  jIntegral : Option { b : Bool //
    IsLocalization.IsInteger ℤ (curve.baseChange ℚ).j ↔ b = true } := none
  /-- The checked abc-quality enclosure. -/
  abcQuality : Option (AbcQualityFacts curve) := none

/-! ## Conductor and root number -/

/-- Arithmetic evidence fixing the numerator model and denominator for the modified Szpiro
ratio. The conductor identification uses TauCeti's algorithmic conductor ideal. -/
structure ModifiedSzpiroRatioEvidence (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The supplied equation is globally minimal over the integers. -/
  minimal : WeierstrassCurve.IsGlobalMinimal ℤ (curve.baseChange ℚ)
  /-- The natural-number conductor used in the denominator. -/
  conductor : ℕ
  /-- Identification of the conductor with the norm of TauCeti's conductor ideal. -/
  conductor_eq : Ideal.absNorm ((curve.baseChange ℚ).algorithmicConductor ℤ) = conductor


/-- An enclosure for the LMFDB modified Szpiro ratio. The numerator uses the minimal
equation's c-invariants and the denominator uses the algorithmic conductor. -/
structure ModifiedSzpiroRatioFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] extends ModifiedSzpiroRatioEvidence curve where
  /-- The logarithm of the conductor is positive. -/
  one_lt_conductor : 1 < conductor
  /-- Rational center of the reported enclosure. -/
  reported : ℚ
  /-- Absolute error radius for the report. -/
  error : ℚ
  /-- The radius is nonnegative. -/
  error_nonneg : 0 ≤ error
  /-- The logarithmic ratio of the larger minimal c-invariant power to the conductor
  lies within the stated error of the report. -/
  within_error :
    |Real.log (max (curve.c₄.natAbs ^ 3) (curve.c₆.natAbs ^ 2) : ℕ) /
      Real.log conductor - (reported : ℝ)| ≤ (error : ℝ)

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

end VerifiedLcalc

namespace VerifiedLcalc.Certification

open VerifiedLcalc.Modularity

/-- Proof-carrying conductor/sign compatibility for a modular realization. -/
structure ArithmeticCompatibility (e : WeierstrassCurve ℤ) (N : Nat) (w : Int) where
  /-- Modular realization whose arithmetic data is being matched. -/
  realization : ModularRealization e
  /-- The realization has the supplied conductor. -/
  conductor_eq : realization.level = N
  /-- The realization has the supplied root number. -/
  rootNumber_eq : realization.rootNumber = w

end VerifiedLcalc.Certification
