/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData

/-! # The input record for certify_ec

`EllipticWitness` is the common submission record for Lean and JSON inputs. It contains the
integral Weierstrass equation and optional claims and finite witnesses for the verifier.
An absent list omits a check, while a submitted empty list asks the verifier to check that list.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve

/-- The single input record for elliptic-curve certification. `none` means that
no data of that kind was supplied; `some []` is an explicitly supplied empty
list, not a claim of completeness. Numerical results are rank candidates;
analytic certification additionally needs checked minimality and local data.
This record asserts no mathematical validity. -/
structure EllipticWitness where
  /-- Integral Weierstrass equation representing the input curve. -/
  equation : WeierstrassCurve ℤ
  /-- A stored Taylor leading coefficient with explicit absolute-error evidence. -/
  specialLValue : Option SpecialLValueClaim := none
  /-- LMFDB analytic rank to compare with an independently checked analytic payload. -/
  catalogueAnalyticRank : Option Nat := none
  /-- A supplied minimum-degree rational isogeny edge. -/
  isogenyEdge : Option IsogenyEdgeClaim := none
  /-- The claimed number of rational isomorphism classes. -/
  classSize : Option Nat := none
  /-- The claimed maximum of the minimum isogeny degrees between representatives. -/
  classDegree : Option Nat := none
  /-- The claimed minimum isogeny degrees in native LMFDB class index order. -/
  isogenyMatrix : Option (List (List Nat)) := none
  /-- The claimed distinct minimum isogeny degrees from the input curve's row. -/
  isogenyDegrees : Option (List Nat) := none
  /-- Reported one-based index within the LMFDB isogeny class. -/
  lmfdbNumber : Option Nat := none
  /-- Reported zero-based index among isogeny classes of this conductor. -/
  isoNlabel : Option Nat := none
  /-- Reported conductor and alphabetic isogeny class code. -/
  lmfdbIso : Option String := none
  /-- Reported conductor, isogeny class code, and curve number. -/
  lmfdbLabel : Option String := none
  /-- The reported complete exceptional-prime list. -/
  nonmaxPrimes : Option (List Nat) := none
  /-- The reported product of the exceptional primes. -/
  nonmaxRadical : Option Nat := none
  /-- The matrix generators reported for the adelic image reduced at its stated modulus. -/
  adelicGenerators : Option AdelicGeneratorsClaim := none
  /-- Claims for the ordered tuple of b₂, b₄, b₆ and b₈. -/
  bInvariants : Option (Int × Int × Int × Int) := none
  /-- Claims for the ordered pair of c₄ and c₆. -/
  cInvariants : Option (Int × Int) := none
  /-- Claimed discriminant of the supplied equation. -/
  discriminant : Option Int := none
  /-- Claimed exact rational j-invariant. -/
  jInvariant : Option Rat := none
  /-- An error bound on the reported abc quality. -/
  abcQuality : Option AbcQualityClaim := none
  /-- Catalogue code for the geometric endomorphism ring. -/
  complexMultiplication : Option Int := none
  /-- Claimed integral model of a minimum-conductor quadratic twist. -/
  minimumTwistEquation : Option (WeierstrassCurve ℤ) := none
  /-- Claimed fundamental discriminant of a minimum-conductor quadratic twist. -/
  minimumTwistDiscriminant : Option Int := none
  /-- Reported modified Szpiro ratio and optional absolute error radius. -/
  modifiedSzpiroRatio : Option DecimalEnclosureClaim := none
  /-- The field and degree from one torsion growth row. -/
  torsionGrowthField : Option TorsionGrowthFieldClaim := none
  /-- Reported canonical heights in the order of `generatorCoordinates`. -/
  canonicalHeights : Option CanonicalHeightsClaim := none
  /-- Stored regulator value and any explicit error evidence. -/
  regulator : Option RegulatorClaim := none
  /-- A p-adic regulator ball proposed for the supplied equation. -/
  padicRegulator : Option PadicRegulatorClaim := none
  /-- Reported full real period and optional absolute error radius. -/
  realPeriod : Option DecimalEnclosureClaim := none
  /-- Reported product of finite-place Tamagawa numbers. -/
  tamagawaProduct : Option Nat := none
  /-- Reported analytic BSD quotient and optional absolute error radius. -/
  analyticSha : Option DecimalEnclosureClaim := none
  /-- Reported rounded analytic BSD quotient. -/
  sha : Option Nat := none
  /-- Reported distinct prime divisors of the rounded analytic BSD quotient. -/
  shaPrimes : Option (List Nat) := none
  /-- Whether the rational j-invariant belongs to the image of ℤ. -/
  jIntegral : Option Bool := none
  /-- Whether the curve has potential good reduction at every rational prime. -/
  potentialGoodReduction : Option Bool := none
  /-- Claimed sign of the discriminant. -/
  discriminantSign : Option Int := none
  /-- LMFDB absD; certification needs a checked globally minimal model. -/
  minimalDiscriminantAbs : Option Nat := none
  /-- Identification with the modular level uses the authorized modularity axiom. -/
  conductor : Option Nat := none
  /-- Claimed global root number of the curve. -/
  rootNumber : Option Int := none
  /-- Consecutive a_n values starting at n=1; JSON anlist also carries a_0=0. -/
  dirichletCoefficients : Option (List Int) := none
  /-- Claimed complete list of primes of bad reduction. -/
  badPrimes : Option (List Nat) := none
  /-- Claimed number of primes of bad reduction. -/
  numBadPrimes : Option Nat := none
  /-- Claimed truth value of semistability of the curve. -/
  semistable : Option Bool := none
  /-- Claimed squarefreeness of the absolute minimal discriminant. -/
  squarefreeDiscriminant : Option Bool := none
  /-- Local reduction claims at the supplied primes. -/
  localInvariants : Option (List LocalReductionClaim) := none
  /-- Reduction evidence bounding the order of the full rational torsion subgroup. -/
  torsionBound : Option TorsionBoundWitness := none
  /-- Claimed exact order of the full rational torsion subgroup. -/
  torsion : Option Nat := none
  /-- Claims for individual prime-indexed L-function coefficients. -/
  primeCoefficients : Option (List (Nat × Int)) := none
  /-- Claimed integral point coordinates on the supplied equation. -/
  integralCoordinates : Option (List (Int × Int)) := none
  /-- One candidate integral root for each supplied x-coordinate whose fiber is certified. -/
  integralFiberRoots : Option (List (Int × Int)) := none
  /-- Claimed number of distinct affine integral points on this equation. -/
  numIntegralPoints : Option Nat := none
  /-- Rational affine coordinates for the LMFDB generator list, checked for membership. -/
  generatorCoordinates : Option (List (Rat × Rat)) := none
  /-- Claimed length of the supplied generator coordinate list. -/
  generatorCount : Option Nat := none
  /-- Claimed Mordell–Weil rank, distinct from a numerical analytic-rank candidate. -/
  algebraicRank : Option Nat := none
  /-- Supplied lower and upper bounds on the Mordell–Weil rank. -/
  algebraicRankBounds : Option (Nat × Nat) := none
  /-- Rational affine coordinates for the LMFDB torsion generator list, checked for membership. -/
  torsionGeneratorCoordinates : Option (List (Rat × Rat)) := none
  /-- Claimed exact additive orders, in the same order as the torsion coordinates. -/
  torsionGeneratorOrders : Option (List Nat) := none
  /-- Claimed invariant factors of rational torsion. -/
  torsionStructure : Option (List Nat) := none
  /-- Claimed distinct prime divisors of the exact rational torsion order. -/
  torsionPrimes : Option (List Nat) := none
  /-- Indices into the supplied integral-coordinate list. -/
  infiniteOrderPoints : Option (List Nat) := none
  /-- Indices into integral coordinates for a supplied independence proof. -/
  independentPoints : Option (List Nat) := none
  /-- Indices into rational generator coordinates for a supplied independence proof. -/
  independentGeneratorPoints : Option (List Nat) := none
  /-- Numerical witness for a central-value enclosure. -/
  centralResult : Option CentralResult := none
  /-- Numerical witness for a first-derivative enclosure. -/
  derivativeResult : Option DerivativeResult := none
  /-- Prime factorization witness for minimality of the supplied equation. -/
  minimality : Option MinimalityWitness := none
  /-- Transcripts at 2 and 3 for the arithmetic conductor and root number. -/
  localData : Option WildData := none

end VerifiedLcalc
