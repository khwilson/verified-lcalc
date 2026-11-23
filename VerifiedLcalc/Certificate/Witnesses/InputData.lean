/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # Shared input records for elliptic-curve certificates -/

@[expose] public section

/-! ## Equation and rational-point inputs -/

namespace VerifiedLcalc

/-- A reported abc quality and evidence for its absolute error bound. -/
structure AbcQualityClaim where
  /-- Exact rational interpretation of the reported value. -/
  reported : Rat
  /-- Claimed maximum absolute error. -/
  error : Rat
  /-- All prime factors of the abc product, with multiplicity. -/
  factors : List Nat

/-- A single oriented edge claim with an exact integral target equation. -/
structure IsogenyEdgeClaim where
  /-- Target equation for the rational map. -/
  target : WeierstrassCurve ℤ
  /-- Claimed minimum degree in this direction. -/
  degree : Nat
  /-- Optional x-coordinate of a kernel point with y=0. -/
  kernelX : Option Rat := none

/-- A stored regulator decimal and optional explicit absolute-error evidence. -/
structure RegulatorClaim where
  /-- Exact rational interpretation of the stored decimal. -/
  reported : Rat
  /-- Explicit absolute error bound; absence means an exact-value claim. -/
  error : Option Rat := none

/-- A finite list containing the abscissa of every affine integral solution. -/
structure IntegralXSupport (curve : WeierstrassCurve ℤ) where
  /-- The supplied abscissae. -/
  xs : List ℤ
  /-- Every affine integral solution has its abscissa on the list. -/
  covers : ∀ x y : ℤ, curve.toAffine.Equation x y → x ∈ xs

/-- Membership of every supplied coordinate pair on the given equation. -/
structure AffineMembership {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- The coordinates in the order supplied to the certifier. -/
  coordinates : List (R × R)
  /-- Each member of the list satisfies the equation. -/
  onCurve : ∀ x y, (x, y) ∈ coordinates → curve.toAffine.Equation x y

/-- Two proposed odd primes and the gcd of the corresponding finite-field point counts. -/
structure TorsionBoundWitness where
  /-- First proposed prime of good reduction. -/
  firstPrime : Nat
  /-- Second proposed prime of good reduction. -/
  secondPrime : Nat
  /-- Claimed positive gcd of the two reduced point counts. -/
  bound : Nat

/-! ## Finite-prime rows and Tate transcripts -/

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

end VerifiedLcalc

namespace VerifiedLcalc.EllipticCurve

/-- A finite, explicit factorization witness. Primes outside this list are good.
Both the factorization and the minimality checks are rechecked in the kernel. -/
structure MinimalityWitness where
  /-- Prime factors, with multiplicity, of the equation discriminant. -/
  primes : List Nat

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

/-- Finite transcripts for the only primes requiring wild root-number data. -/
structure WildData where
  /-- Transcript at residue characteristic two, when additive reduction occurs. -/
  atTwo : Option TateWitness
  /-- Transcript at residue characteristic three, when additive reduction occurs. -/
  atThree : Option TateWitness

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

/-- Immutable precision settings recorded in numerical evidence. -/
structure PrecisionPolicy where
  /-- Number of binary precision bits requested by the exact evaluator. -/
  precisionBits : Nat

/-- An exact rational interpretation of a reported Taylor leading coefficient
and its explicit absolute-error radius. -/
structure SpecialLValueClaim where
  /-- Decimal or rational value as reported by the input. -/
  reported : Rat
  /-- Explicit claimed maximum absolute error. -/
  error : Rat

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

end VerifiedLcalc.Assumptions
