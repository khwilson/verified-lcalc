/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Invariants
public import VerifiedLcalc.Certificate.LocalReductionSpecs
public import VerifiedLcalc.EllipticCurve.Tate.ArithmeticSpecs
public import VerifiedLcalc.EllipticCurve.Tate.PotentialGoodReductionSpec
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-! # Local reduction, arithmetic coefficients, and Galois images

* `LocalTamagawaFact` identifies the intrinsic Tamagawa number at a specified rational prime.
  `LocalKodairaFact` gives the exact `Iₙ` index or excludes the entire `Iₙ` family.
  `LocalKodairaSymbolFact` identifies the full Tate-algorithm symbol.
  `LocalRootNumberFact` identifies the arithmetic sign of a valid transcript.
* `MinimalModelArithmeticFacts` starts with checked global minimality and collects
  discriminant, bad-prime, semistability, and local reduction data on that model.
* `ArithmeticFacts` collects optional minimal-model facts, intrinsic Tamagawa factors,
  finite transcript validity, potential good reduction, and prime-indexed and consecutive
  L-function coefficients. Its modular facts require an explicit arithmetic realization.
* `FiniteGaloisImageFact` and `PadicGaloisImageFact` give exact images in supplied bases.
* `AdelicGaloisImageClaim`, `PrimeGaloisImageClaim`, `SerreInvariantClaim` and
  `GaloisImageClaims` hold producer data whose interpretation needs further comparison theorems.
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

/-- The full canonical reduction symbol defined by Tate's algorithm over the rational
local ring. The equality applies to the rational curve independently of the input model. -/
structure LocalKodairaSymbolFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The prime at which the symbol was checked. -/
  prime : Nat.Primes
  /-- The full canonical Tate reduction symbol, including additive types. -/
  symbol : TauCeti.ReductionSymbol
  /-- The terminal symbol on a minimal equation over this prime's local ring. -/
  correct :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    (curve.baseChange ℚ).reductionSymbol (RationalLocalRing (prime : ℕ)) = symbol

/-- A local sign from the tame formula or validated wild data on a minimal local equation.
The equality concerns the arithmetic formula; intrinsic local epsilon-factor compatibility
requires a separate comparison theorem. -/
structure LocalRootNumberFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The prime at which the sign was checked. -/
  prime : Nat.Primes
  /-- The given integral equation is minimal at this prime. -/
  minimal :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    IsMinimal (RationalLocalRing (prime : ℕ)) (curve.baseChange ℚ)
  /-- The supplied transcripts for wild reduction. -/
  transcripts : WildData
  /-- Validity of the tame fallback and any required wild transcripts. -/
  valid : transcripts.Valid curve
  /-- The signed value produced by the local arithmetic formula. -/
  value : ℤ
  /-- The value belongs to the set of local signs. -/
  isSign : value = 1 ∨ value = -1
  /-- Equality with the arithmetic formula at this prime. -/
  correct :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    wildLocalRootSpec curve transcripts (prime : ℕ) = value

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

open scoped Classical Matrix

/-- A finite image of the absolute Galois group on the full geometric torsion of a
nonsingular rational curve. The choice of torsion basis specifies the conjugate in which the
matrix generators are given. -/
structure FiniteGaloisImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The torsion modulus. -/
  modulus : ℕ+
  /-- The ordered basis of the geometric torsion over the residue ring. -/
  basis : Module.Basis (Fin 2) (ZMod (modulus : ℕ))
    (AddSubgroup.torsionBy ((curve.baseChange ℚ).baseChange (AlgebraicClosure ℚ)).toAffine.Point
      ((modulus : ℕ) : ℤ))
  /-- Invertible matrices generating the image in the supplied basis. -/
  generators : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod (modulus : ℕ)))
  /-- Membership is equivalent to acting on the geometric torsion as a rational Galois
  automorphism in the supplied basis. -/
  correct : ∀ g, g ∈ Subgroup.closure {g | g ∈ generators} ↔
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ P,
      basis.equivFun
          (Multiplicative.toAdd
            ((curve.baseChange ℚ).torsionGaloisAction ((modulus : ℕ) : ℤ) σ) P) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod (modulus : ℕ))) *ᵥ basis.equivFun P

/-- The exact image on the full Tate module over the algebraic closure of the rationals.
The subgroup carries the entire prime-adic conclusion. -/
structure PadicGaloisImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (prime : Nat.Primes) where
  /-- The ordered integral basis of the Tate module. -/
  basis :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    Module.Basis (Fin 2) ℤ_[(prime : ℕ)]
      (TauCeti.TateModule (prime : ℕ)
        ((curve.baseChange ℚ).baseChange (AlgebraicClosure ℚ)).toAffine.Point)
  /-- The exact image subgroup in the given basis. -/
  image :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℤ_[(prime : ℕ)])
  /-- Membership is equivalent to acting on the Tate module as a rational Galois
  automorphism in the supplied basis. -/
  correct :
    letI : Fact (prime : ℕ).Prime := ⟨prime.property⟩
    ∀ g, g ∈ image ↔ ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ t,
      basis.equivFun ((curve.baseChange ℚ).tateModuleGaloisRepresentation (prime : ℕ) σ t) =
        (g : Matrix (Fin 2) (Fin 2) ℤ_[(prime : ℕ)]) *ᵥ basis.equivFun t

/-- Claimed adelic row, whose database prime sentinel is zero. The generator modulus is
explicit even when the producer's adelic level has yet to be justified. -/
structure AdelicGaloisImageClaim (curve : WeierstrassCurve ℤ) where
  /-- The producer's adelic image label, if supplied. -/
  adelicImage : Option String := none
  /-- The producer's matrices over the stated positive modulus. -/
  adelicGenerators : Option ((m : ℕ+) × List (Matrix.GeneralLinearGroup (Fin 2) (ZMod (m : ℕ))))
    := none

/-- Claimed labels of a local Galois image row at an actual rational prime. -/
structure PrimeGaloisImageClaim (curve : WeierstrassCurve ℤ) where
  /-- The local prime as a checked prime number. -/
  prime : Nat.Primes
  /-- The producer's mod-prime image label, when present. -/
  modPrimeImage : Option String := none
  /-- The producer's prime-adic image label, when present. -/
  padicImage : Option String := none

/-- A producer's claimed Serre weight and conductor for an exceptional residual prime. -/
structure SerreInvariantClaim (curve : WeierstrassCurve ℤ) where
  /-- The characteristic of the residual representation. -/
  prime : Nat.Primes
  /-- The supplied Serre weight. -/
  weight : ℕ+
  /-- The supplied Serre conductor. -/
  conductor : ℕ+

/-- The producer's image metadata. The labels, genus, adelic level and adelic index need
database and modular-curve comparison theorems. Exceptional primes and Serre invariants
also need their producer conventions and intrinsic comparisons. -/
structure GaloisImageClaims (curve : WeierstrassCurve ℤ) where
  /-- The adelic row (the producer's prime-zero row), when supplied. -/
  adelic : Option (AdelicGaloisImageClaim curve) := none
  /-- The producer's local rows, each indexed by an actual prime. -/
  localRows : List (PrimeGaloisImageClaim curve) := []
  /-- The claimed adelic image level. -/
  adelicLevel : Option ℕ+ := none
  /-- The claimed adelic image index. -/
  adelicIndex : Option ℕ+ := none
  /-- The claimed genus of the associated modular curve. -/
  adelicGenus : Option ℕ := none
  /-- The producer's curve-level mod-prime image labels. -/
  modPrimeImages : Option (List String) := none
  /-- The producer's curve-level prime-adic image labels. -/
  padicImages : Option (List String) := none
  /-- The producer's curve-level composite-modulus image labels. -/
  modmImages : Option (List String) := none
  /-- The producer's exceptional primes under its convention for the curve. -/
  nonmaxPrimes : Option (List Nat.Primes) := none
  /-- The claimed product of the distinct exceptional primes. -/
  nonmaxRadical : Option ℕ+ := none
  /-- The producer's list of exceptional-prime Serre triples. -/
  serreInvariants : Option (List (SerreInvariantClaim curve)) := none

end VerifiedLcalc
