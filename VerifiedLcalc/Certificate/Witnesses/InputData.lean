/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! # Shared input records for elliptic-curve certificates

* `CatalogueMetadata` holds optional LMFDB and Cremona identifiers and the trace fingerprint
  supplied for an equation.
* `AbcQualityClaim`, `IsogenyEdgeClaim`, and `RegulatorClaim` describe submitted abc
  approximations, directed isogeny degrees, and regulator values. `IntegralXSupport` proves
  coverage of all integral abscissae. `TorsionBoundWitness` proposes two good primes
  and a point-count gcd.
* `LocalReductionClaim` holds optional entries for a single prime.
  `EllipticCurve.MinimalityWitness` supplies discriminant factors,
  `EllipticCurve.TateWitness` supplies a local Tate transcript, and `EllipticCurve.WildData`
  bundles the optional transcripts at 2 and 3.
* `Box` records a rational rectangle, `PrecisionPolicy` fixes binary precision, and
  `SpecialLValueClaim` reports a Taylor leading coefficient and absolute error radius.
  `EllipticCurve.CentralResult` and `EllipticCurve.DerivativeResult` carry the finite central
  and first-derivative evaluator outputs. `Assumptions.CurvePrecisionClaim` specifies
  the curve, cutoff policy, derivative prefix, and proposed nonzero gap for an exact upgrade.
-/

@[expose] public section

/-! ## Equation and rational-point inputs -/

namespace VerifiedLcalc

/-- A finite generator report from the prime-zero Galois row. -/
structure AdelicGeneratorsClaim where
  /-- Reported reduction modulus, obtained from the source image level. -/
  modulus : ℕ
  /-- Row-major quadruples of least nonnegative matrix entries. -/
  rows : List (ℕ × ℕ × ℕ × ℕ)
  deriving Repr, DecidableEq

/-- Catalogue references supplied for an integral equation. These fields record provenance. -/
structure CatalogueMetadata (curve : WeierstrassCurve ℤ) where
  /-- LMFDB curve label (`lmfdb_label`). -/
  lmfdbLabel : Option String := none
  /-- LMFDB isogeny-class label (`lmfdb_iso`). -/
  lmfdbIso : Option String := none
  /-- Position of the curve in the LMFDB class ordering (`lmfdb_number`). -/
  lmfdbNumber : Option ℕ := none
  /-- Numerical encoding of the LMFDB class label (`iso_nlabel`). -/
  isoNlabel : Option ℕ := none
  /-- Cremona curve label (`Clabel`). -/
  cremonaLabel : Option String := none
  /-- Cremona isogeny-class label (`Ciso`). -/
  cremonaIso : Option String := none
  /-- Position of the curve in the Cremona class ordering (`Cnumber`). -/
  cremonaNumber : Option ℕ := none
  /-- Catalogue fingerprint for the traces of this curve's isogeny class (`trace_hash`). -/
  traceHash : Option ℕ := none

/-- A reported abc quality and evidence for its absolute error bound. -/
structure AbcQualityClaim where
  /-- Exact rational interpretation of the reported value. -/
  reported : Rat
  /-- Claimed maximum absolute error. -/
  error : Rat
  /-- All prime factors of the abc product, with multiplicity. -/
  factors : List Nat
  deriving Repr, DecidableEq

/-- A single oriented edge claim with an exact integral target equation. -/
structure IsogenyEdgeClaim where
  /-- Target equation for the rational map. -/
  target : WeierstrassCurve ℤ
  /-- Claimed minimum degree in this direction. -/
  degree : Nat
  /-- Optional x-coordinate of a kernel point with y=0. -/
  kernelX : Option Rat := none
  deriving Repr, DecidableEq

/-- The field presentation and absolute degree from one `ec_torsion_growth` row. -/
structure TorsionGrowthFieldClaim where
  /-- Integral coefficients in ascending order. -/
  coefficients : List ℤ
  /-- The claimed absolute field degree. -/
  degree : ℕ
  deriving Repr, DecidableEq

/-- The decimal heights from `ec_mwbsd`, ordered by the accompanying `gens`. -/
structure CanonicalHeightsClaim where
  /-- The decoded height centers in generator order. -/
  reported : List ℚ
  /-- Optional absolute error radii in the same order. -/
  errors : Option (List ℚ) := none
  deriving Repr, DecidableEq

/-- A stored regulator decimal and optional explicit absolute-error evidence. -/
structure RegulatorClaim where
  /-- Exact rational interpretation of the stored decimal. -/
  reported : Rat
  /-- Explicit absolute error bound; absence means an exact-value claim. -/
  error : Option Rat := none
  deriving Repr, DecidableEq

/-- One submitted p-adic ball for the regulator of the input equation. -/
structure PadicRegulatorClaim where
  /-- Reported prime. -/
  p : ℕ
  /-- Absolute precision exponent. -/
  prec : ℤ
  /-- Signed valuation of the reported ball. -/
  val : ℤ
  /-- Proposed least nonnegative residue of the unit factor modulo `p^(prec - val)`. -/
  unit : ℤ
  deriving Repr, DecidableEq

/-- A reported decimal from an archimedean invariant or analytic quotient. -/
structure DecimalEnclosureClaim where
  /-- Exact rational interpretation of the reported decimal. -/
  reported : Rat
  /-- Explicit absolute error radius, if supplied with the report. -/
  error : Option Rat := none
  deriving Repr, DecidableEq

/-- A finite list containing the abscissa of every affine integral solution. -/
structure IntegralXSupport (curve : WeierstrassCurve ℤ) where
  /-- The supplied abscissae. -/
  xs : List ℤ
  /-- Every affine integral solution has its abscissa on the list. -/
  covers : ∀ x y : ℤ, curve.toAffine.Equation x y → x ∈ xs

/-- Two proposed odd primes and the gcd of the corresponding finite-field point counts. -/
structure TorsionBoundWitness where
  /-- First proposed prime of good reduction. -/
  firstPrime : Nat
  /-- Second proposed prime of good reduction. -/
  secondPrime : Nat
  /-- Claimed positive gcd of the two reduced point counts. -/
  bound : Nat
  deriving Repr, DecidableEq

/-! ## Finite-prime rows and Tate transcripts -/

/-- Exact integral coordinates of a unit-scale change of variables for a type III witness. -/
structure TamagawaTypeIIIShift where
  /-- Change in the x-coordinate. -/
  r : Int
  /-- Slope of the change in the y-coordinate. -/
  s : Int
  /-- Translation in the y-coordinate. -/
  t : Int
  deriving Repr, DecidableEq

/-- Supplied residue evidence for the type IV component-group factor. -/
inductive TypeIVTamagawaResidue where
  /-- A specific residue representative at which the terminal quadratic vanishes. -/
  | root (value : Nat)
  /-- The supplied Euler-power value certifying the quadratic is nonsplit at an odd prime. -/
  | nonsplitEulerPower (value : Nat)
  deriving Repr, DecidableEq

/-- Exact unit-scale translation and residue evidence for a type IV Tamagawa claim.
The verifier checks these supplied values and performs no search. -/
structure TamagawaTypeIVEvidence where
  /-- Change in the x-coordinate. -/
  r : Int
  /-- Slope of the change in the y-coordinate. -/
  s : Int
  /-- Translation in the y-coordinate. -/
  t : Int
  /-- Positive-root or nonsplit Euler evidence for the terminal quadratic. -/
  residue : TypeIVTamagawaResidue
  deriving Repr, DecidableEq

/-- Optional claims from an LMFDB local row. The reduction codes are 0 for
additive, 1 for split multiplicative and -1 for nonsplit multiplicative. -/
structure LocalReductionClaim where
  /-- Rational prime at which the local claims are made. -/
  prime : Nat
  /-- Exponent of this prime in the absolute minimal discriminant. -/
  discriminantValuation : Option Nat := none
  /-- Exponent of this prime in the checked modular conductor. -/
  conductorValuation : Option Nat := none
  /-- Exponent of this prime in the reduced denominator of the rational j-invariant. -/
  jDenominatorValuation : Option Nat := none
  /-- Signed Frobenius trace code for bad reduction. -/
  reductionType : Option Int := none
  /-- Claimed intrinsic local component-group order. -/
  tamagawaNumber : Option Nat := none
  /-- Claimed PARI Kodaira code. Additive codes request a family check. -/
  kodairaSymbol : Option Int := none
  /-- Claimed arithmetic local sign at this prime. -/
  rootNumber : Option Int := none
  /-- Submitted unit-scale change for the intrinsic tame type III local factor. -/
  tamagawaTypeIIIShift : Option TamagawaTypeIIIShift := none
  /-- Submitted change and residue evidence for a type IV local factor. -/
  tamagawaTypeIVEvidence : Option TamagawaTypeIVEvidence := none
  deriving Repr, DecidableEq

end VerifiedLcalc

namespace VerifiedLcalc.EllipticCurve

/-- A finite, explicit factorization witness. Primes outside this list are good.
Both the factorization and the minimality checks are rechecked in the kernel. -/
structure MinimalityWitness where
  /-- Prime factors, with multiplicity, of the equation discriminant. -/
  primes : List Nat
  deriving Repr, DecidableEq

/-- A finite Tate reduction transcript. Codes: II=2, III=3, IV=4,
I0*=-1, IV*=-4, III*=-3, II*=-2, I_n*=-(4+n). -/
structure TateWitness where
  /-- Initial horizontal translation. -/
  r : Int
  /-- Initial shear in the y-coordinate. -/
  s : Int
  /-- Initial vertical translation. -/
  t : Int
  /-- Vertical translation parameter at the start of the starred cases. -/
  starT : Int := 0
  /-- Candidate repeated root of the cubic. -/
  cubicRoot : Int := 0
  /-- Candidate repeated root of the quadratic. -/
  quadraticRoot : Int := 0
  /-- Repeated roots checked in the starred blow-up sequence. -/
  chain : List Int := []
  /-- Integer code for the proposed Kodaira symbol. -/
  kodaira : Int
  deriving Repr, DecidableEq

/-- Finite transcripts for the only primes requiring wild root-number data. -/
structure WildData where
  /-- Transcript at residue characteristic two, when additive reduction occurs. -/
  atTwo : Option TateWitness
  /-- Transcript at residue characteristic three, when additive reduction occurs. -/
  atThree : Option TateWitness
  deriving Repr, DecidableEq

end VerifiedLcalc.EllipticCurve

/-! ## Numerical reports and precision -/

namespace VerifiedLcalc

/-- Closed rational rectangle in the real and imaginary coordinates. -/
structure Box where
  /-- Lower real endpoint. -/
  reLo : Rat
  /-- Upper real endpoint. -/
  reHi : Rat
  /-- Lower imaginary endpoint. -/
  imLo : Rat
  /-- Upper imaginary endpoint. -/
  imHi : Rat
  deriving Repr, DecidableEq

/-- Immutable precision settings recorded in numerical evidence. -/
structure PrecisionPolicy where
  /-- Number of binary precision bits requested by the exact evaluator. -/
  precisionBits : Nat
  deriving Repr, DecidableEq

/-- An exact rational interpretation of a reported Taylor leading coefficient
and its explicit absolute-error radius. -/
structure SpecialLValueClaim where
  /-- Decimal or rational value as reported by the input. -/
  reported : Rat
  /-- Explicit claimed maximum absolute error. -/
  error : Rat
  deriving Repr, DecidableEq

end VerifiedLcalc

namespace VerifiedLcalc.EllipticCurve

/-- Finite central-value output. Its numerical interpretation is recorded
separately by `CentralPayloadCorrect`. -/
structure CentralResult where
  /-- The integral Weierstrass equation whose coefficients are enclosed. -/
  equation : WeierstrassCurve ℤ
  /-- The positive conductor used to set the Mellin scale. -/
  conductor : Nat
  /-- Root number in the arithmetic normalization; accepted values are `±1`. -/
  rootNumber : Int
  /-- Precision settings retained with this payload. -/
  policy : PrecisionPolicy
  /-- Number of initial Dirichlet coefficients included. -/
  termLimit : Nat
  /-- Exact initial coefficient list used by the enclosure. -/
  coefficients : List Int
  /-- Lower and upper rational bounds for the Mellin scale. -/
  alphaLo : Rat
  /-- Upper rational bound for the Mellin scale. -/
  alphaHi : Rat
  /-- Exact rational upper bound for the exponential ratio. -/
  geometricUpper : Rat
  /-- Exact rational bound for the omitted series tail. -/
  tail : Rat
  /-- Rational rectangle enclosing the central value in real coordinates. -/
  box : Box
  deriving Repr, DecidableEq

/-- Finite first-derivative output. Its numerical interpretation is recorded
separately by `DerivativePayloadCorrect`. -/
structure DerivativeResult where
  /-- The integral Weierstrass equation whose coefficients are enclosed. -/
  equation : WeierstrassCurve ℤ
  /-- The positive conductor used to set the Mellin scale. -/
  conductor : Nat
  /-- Precision settings retained with this payload. -/
  policy : PrecisionPolicy
  /-- Number of initial Dirichlet coefficients included. -/
  termLimit : Nat
  /-- Number of rational quadrature cells per unit interval. -/
  stepsPerUnit : Nat
  /-- End of the finite quadrature interval. -/
  cutoff : Nat
  /-- Exact initial coefficient list used by the enclosure. -/
  coefficients : List Int
  /-- Lower and upper rational bounds for the Mellin scale. -/
  alphaLo : Rat
  /-- Upper rational bound for the Mellin scale. -/
  alphaHi : Rat
  /-- Enclosure of the normalized derivative integral over `[1, cutoff]`. -/
  finite : Rat × Rat
  /-- Bound on the omitted normalized integral from `cutoff` to infinity. -/
  tail : Rat
  /-- Rational rectangle enclosing the normalized derivative integral. -/
  box : Box
  deriving Repr, DecidableEq

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.Assumptions

/-- Identity of a proposed curve-specific numerical-to-exact upgrade.
The convention is fixed: raw iterated derivatives of the arithmetic L-function
at 1, coordinatewise cutoff, with no factorial or period normalization. -/
structure CurvePrecisionClaim where
  /-- Integral equation whose arithmetic L-function is under consideration. -/
  equation : WeierstrassCurve ℤ
  /-- Exact cutoff policy used for the derivative coordinates. -/
  policy : PrecisionPolicy
  /-- Number of consecutive derivatives classified by the claim. -/
  derivativeCount : Nat
  /-- Strict lower bound separating the first nonzero derivative from cutoff. -/
  nonzeroGap : Rat
  deriving Repr, DecidableEq

end VerifiedLcalc.Assumptions
