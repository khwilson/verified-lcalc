/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Invariants
public import VerifiedLcalc.Certificate.AdelicImageSpecs
public import VerifiedLcalc.Certificate.ImageCatalogue
public import VerifiedLcalc.Certificate.LocalReductionSpecs
public import VerifiedLcalc.Certificate.ResidualImageLabels
public import VerifiedLcalc.Certificate.SerreInvariantSpecs
public import VerifiedLcalc.EllipticCurve.LmfdbTraceHash
public import VerifiedLcalc.EllipticCurve.Tate.ArithmeticSpecs
public import VerifiedLcalc.EllipticCurve.Tate.KodairaSpecs
public import VerifiedLcalc.EllipticCurve.Tate.PotentialGoodReductionSpec
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic

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
* `TraceHashCoefficients` proves the full prime coefficient vector, and `TraceHashFact`
  identifies its published weighted fingerprint.
* `FiniteGaloisImageFact` and `PadicGaloisImageFact` give exact images in supplied bases.
* `ModPrimeImageFact` identifies the exact residual image up to conjugacy. A checked
  `ModPrimeImageListFact` can also carry exhaustive non-CM `ModPrimeImageCoverage`.
* `NonmaxPrimeSupportFact` proves complete non-CM exceptional support for the integral
  Tate-module images and determines the radical as the product of those primes.
* `AdelicImageFact` identifies the simultaneous integral Tate-module image and supports
  checked level, index, and coarse modular-curve genus. `AdelicImageCertificate` also records
  a verified partial label when the producer leaves the class suffix unspecified.
* `AdelicGaloisImageClaim`, `PrimeGaloisImageClaim`, `SerreInvariantClaim` and
  `GaloisImageClaims` hold producer data whose interpretation needs further comparison theorems.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve NumberField WeierstrassCurve

/-- Exact arithmetic coefficients for all prime indices of the published trace hash. -/
structure TraceHashCoefficients (curve : WeierstrassCurve ℤ) where
  /-- Coefficients in the fixed ascending prime order of the source. -/
  coefficients : List ℤ
  /-- The full vector is exactly the prescribed sequence of actual curve coefficients. -/
  correct : coefficients = lmfdbTraceHashPrimes.map (fun p => (curve.baseChange ℚ).LFunction p)

/-- An exact checked trace fingerprint of the submitted equation. -/
structure TraceHashFact (curve : WeierstrassCurve ℤ) where
  /-- Full coefficient vector and its mathematical proof. -/
  evidence : TraceHashCoefficients curve
  /-- The reported canonical residue. -/
  value : ℤ
  /-- The hash of the actual rational L-function coefficients equals the reported residue. -/
  correct : lmfdbTraceHash (curve.baseChange ℚ) = value

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
    KodairaIndexSpec (curve.baseChange ℚ) (prime : ℕ) index

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
  /-- Checked local valuations and reduction types. -/
  localRows : Option { rows : List LocalReductionClaim // ∀ row ∈ rows,
    row.conductorValuation = none ∧ row.kodairaSymbol = none ∧
      row.tamagawaNumber = none ∧ row.rootNumber = none ∧ row.Spec curve } := none
  /-- Checked canonical Kodaira facts at the supplied primes. -/
  kodaira : List (LocalKodairaFact curve) := []
  /-- Checked arithmetic local signs at the supplied primes on this minimal model. -/
  localRootNumbers : List (LocalRootNumberFact curve) := []

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

open scoped Matrix

/-- A finite image of the absolute Galois group on the full geometric torsion of a
nonsingular rational curve. The choice of torsion basis specifies the conjugate in which the
matrix generators are given. -/
structure FiniteGaloisImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The torsion modulus. -/
  modulus : ℕ+
  /-- Invertible matrices generating the image in the supplied basis. -/
  generators : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod (modulus : ℕ)))
  /-- In an ordered basis over the residue ring, membership is equivalent to acting
  on the full geometric torsion as a rational Galois automorphism. -/
  correct : ∃ basis : Module.Basis (Fin 2) (ZMod (modulus : ℕ))
      (AddSubgroup.torsionBy ((curve.baseChange ℚ).baseChange (AlgebraicClosure ℚ)).toAffine.Point
        ((modulus : ℕ) : ℤ)),
    ∀ g, g ∈ Subgroup.closure {g | g ∈ generators} ↔
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ P,
        basis.equivFun
            (Multiplicative.toAdd
              ((curve.baseChange ℚ).torsionGaloisAction ((modulus : ℕ) : ℤ) σ) P) =
          (g : Matrix (Fin 2) (Fin 2) (ZMod (modulus : ℕ))) *ᵥ basis.equivFun P

/-- An exact residual Galois image identified with a supported Sutherland conjugacy class. -/
structure ModPrimeImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The full geometric torsion image in an ordered basis. -/
  finiteImage : FiniteGaloisImageFact curve
  /-- The torsion modulus is a rational prime. -/
  prime : Nat.Prime (finiteImage.modulus : ℕ)
  /-- The Sutherland label of the image. -/
  label : String
  /-- The generated image is a conjugate of the reference subgroup for the label. -/
  conjugate : ∃ rows,
    residualImageLabelGenerators label = some ((finiteImage.modulus : ℕ), rows) ∧
      ∃ c : Matrix.GeneralLinearGroup (Fin 2) (ZMod (finiteImage.modulus : ℕ)),
        Subgroup.closure {g | g ∈ finiteImage.generators} =
          (residualImageReferenceGroup (finiteImage.modulus : ℕ) rows).map
            (MulAut.conj c).toMonoidHom

/-- Exhaustiveness of a residual image list under the non-CM reporting convention. -/
structure ModPrimeImageCoverage (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)]
    (images : List (ModPrimeImageFact curve)) : Prop where
  /-- The curve has no geometric complex multiplication. -/
  nonCM : ¬ (curve.baseChange ℚ).HasGeometricCM
  /-- The primes appearing in the list are precisely the primes with proper residual image. -/
  complete : ∀ p : Nat.Primes, ∃ image : FiniteGaloisImageFact curve,
    (image.modulus : ℕ) = (p : ℕ) ∧
      ((∃ entry ∈ images, (entry.finiteImage.modulus : ℕ) = (p : ℕ)) ↔
        Subgroup.closure {g | g ∈ image.generators} ≠ ⊤)

/-- Verified entries of the submitted curve-level list, with optional non-CM exhaustiveness. -/
structure ModPrimeImageListFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- One exact conjugacy-class identification per listed label, in report order. -/
  images : List (ModPrimeImageFact curve)
  /-- Optional evidence that the list covers all and only the exceptional residual primes. -/
  coverage : Option (PLift (ModPrimeImageCoverage curve images)) := none

/-- The exact image on the full Tate module over the algebraic closure of the rationals.
The subgroup carries the entire prime-adic conclusion. -/
structure PadicGaloisImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] (prime : Nat.Primes) where
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

/-- A native prime-adic label identified with the exact integral Tate-module image. -/
structure PadicImageLabelFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The prime of the representation. -/
  prime : Nat.Primes
  /-- The exact prime-adic image, including the ordered Tate basis. -/
  exactImage : PadicGaloisImageFact curve prime
  /-- The Rouse–Sutherland–Zureick-Brown label. -/
  label : String
  /-- The entire local image is conjugate to the full inverse image of the reference subgroup. -/
  correct :
    letI : Fact prime.val.Prime := ⟨prime.property⟩
    ∃ depth rows, padicImageReference label = some (prime.val, depth, rows) ∧
      ∃ c : Matrix.GeneralLinearGroup (Fin 2) (AdelicLocalRing prime),
        exactImage.image = ((residualImageReferenceGroup (prime.val ^ depth) rows).comap
          (localImageReduction prime depth)).map (MulAut.conj c).toMonoidHom

/-- A genus certificate on the actual coarse modular curve associated to an adelic image. -/
structure AdelicGenusFact (H : Subgroup AdelicGL) where
  /-- A modulus defining the open subgroup. This modulus need not be minimal. -/
  modulus : ℕ+
  /-- The subgroup is the full inverse image of its reduction at this modulus. -/
  kernel : (adelicReduction modulus).ker ≤ H
  /-- The integral pullback has finite index in the determinant-one group. -/
  finiteIndex : (adelicCongruenceSubgroup H).FiniteIndex
  /-- The compactified effective quotient has finite CW type. -/
  finiteCW : TauCeti.FiniteCWType (adelicProjectiveSubgroup H).CompactifiedQuotient
  /-- The genus of this compactified quotient. -/
  genus : ℕ
  /-- The quotient's Euler characteristic gives the genus without truncation. -/
  correct :
    letI := finiteCW
    TauCeti.eulerChar (adelicProjectiveSubgroup H).CompactifiedQuotient = 2 - 2 * (genus : ℤ)

/-- The exact simultaneous integral Tate-module image and its optional invariants. -/
structure AdelicImageFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The image inside the product of the integral local matrix groups. -/
  image : Subgroup AdelicGL
  /-- One family of ordered Tate bases. A single Galois automorphism acts on every component
  of each image element, so this condition preserves entanglement between primes. -/
  correct :
    ∃ basis : (p : Nat.Primes) →
        Module.Basis (Fin 2) (AdelicLocalRing p)
          (TauCeti.TateModule p.val
            (((curve.baseChange ℚ).baseChange (AlgebraicClosure ℚ)).toAffine.Point)),
      ∀ g : AdelicGL, g ∈ image ↔
        ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ (p : Nat.Primes) t,
          letI : Fact p.val.Prime := ⟨p.property⟩
          (basis p).equivFun ((curve.baseChange ℚ).tateModuleGaloisRepresentation p.val σ t) =
            (g p : Matrix (Fin 2) (Fin 2) (AdelicLocalRing p)) *ᵥ (basis p).equivFun t
  /-- The least positive modulus whose full adelic reduction kernel lies in the image. -/
  level : Option { N : ℕ+ // IsLeast { M | (adelicReduction M).ker ≤ image } N } := none
  /-- The finite index of this subgroup in the full integral adelic matrix group. -/
  index : Option { i : ℕ+ // image.index = (i : ℕ) } := none
  /-- The genus of the actual compactified effective modular quotient for this image. -/
  genus : Option (AdelicGenusFact image) := none

/-- The proved adelic invariants and optional formatting proof for a submitted partial label. -/
structure AdelicImageCertificate (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- Simultaneous adelic image with the supplied invariant proofs. -/
  facts : AdelicImageFact curve
  /-- A matching incomplete producer label, with its class suffix unspecified. -/
  partialLabel : Option { label : String //
    formatPartialAdelicImageOf (facts.level.map fun n => (n.val : ℕ))
      (facts.index.map fun i => (i.val : ℕ)) (facts.genus.map AdelicGenusFact.genus) =
        some label } := none

/-- An exact finite image identified by a native modular-curve label or its proved prefix. -/
structure ModulusImageLabelFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The exact Galois action on the full geometric torsion of the label's level. -/
  exactImage : FiniteGaloisImageFact curve
  /-- The reported modular-curve label, possibly with an unspecified class suffix. -/
  label : String
  /-- A defined label identifies the finite subgroup up to conjugacy. An incomplete label
  identifies the level, full index and coarse genus of its adelic inverse image. -/
  correct :
    let group := Subgroup.closure {g | g ∈ exactImage.generators}
    let reduction := adelicReduction exactImage.modulus
    let lift := group.comap reduction
    (∃ rows, finiteImageReference label = some ((exactImage.modulus : ℕ), rows) ∧
      ∃ c, group = (residualImageReferenceGroup (exactImage.modulus : ℕ) rows).map
        (MulAut.conj c).toMonoidHom) ∨
    ∃ (index : ℕ+) (genus : AdelicGenusFact lift),
      IsLeast {N | (adelicReduction N).ker ≤ lift} exactImage.modulus ∧
      group.index = (index : ℕ) ∧
      formatPartialAdelicImage (exactImage.modulus : ℕ) (index : ℕ) genus.genus = label

/-- A source list of finite image labels with evidence on an ordered sublist. -/
structure ModulusImageListFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The complete submitted list of raw labels. -/
  reported : List String
  /-- The verified entries in source order. -/
  entries : List (ModulusImageLabelFact curve)
  /-- Evidence for a sublist certifies only the corresponding source entries. -/
  sublist : (entries.map ModulusImageLabelFact.label).Sublist reported
  /-- A nonempty source list requires at least one genuinely verified entry. -/
  hasEvidence : reported = [] ∨ entries ≠ []
  /-- Optional evidence that every reported entry was checked, in source order. -/
  allEntries : Option (PLift ((entries.map ModulusImageLabelFact.label) = reported)) := none

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

/-- Complete exceptional list for Serre's semistable recipe with good reduction at two. -/
structure SemistableSerreRecipeFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The input integral equation is globally minimal. -/
  minimal : WeierstrassCurve.IsGlobalMinimal (NumberField.RingOfIntegers ℚ) (curve.baseChange ℚ)
  /-- The curve has only good or multiplicative reduction. -/
  semistable : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ) (curve.baseChange ℚ)
  /-- The minimal discriminant is a unit at two. -/
  goodAtTwo : ¬ 2 ∣ curve.Δ.natAbs
  /-- The submitted exceptional primes, weights and conductors. -/
  rows : List (ℕ × ℕ × ℕ)
  /-- The submitted list agrees with the complete arithmetic recipe. -/
  exactRows : rows = semistableSerreInvariants curve.Δ.natAbs

/-- Complete non-CM exceptional support for the local integral Tate-module images. -/
structure NonmaxPrimeSupportFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The geometric endomorphism ring consists of the integer multiplications. -/
  nonCM : ¬ (curve.baseChange ℚ).HasGeometricCM
  /-- The complete finite set of exceptional primes. -/
  primes : Finset Nat.Primes
  /-- At each rational prime, the actual integral Tate-module image in a supplied basis
  is proper precisely when the prime belongs to the finite set. -/
  complete :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    ∀ p : Nat.Primes, ∃ image : PadicGaloisImageFact curve p, p ∈ primes ↔ image.image ≠ ⊤

/-- Proved local labels with optional coverage of all exceptional primes for non-CM curves. -/
structure PadicImageListFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)] where
  /-- The checked labels in source order. -/
  entries : List (PadicImageLabelFact curve)
  /-- Optional proof that the listed primes are precisely the nonmaximal integral primes. -/
  coverage : Option { support : NonmaxPrimeSupportFact curve //
    support.primes = (entries.map PadicImageLabelFact.prime).toFinset } := none

end VerifiedLcalc
