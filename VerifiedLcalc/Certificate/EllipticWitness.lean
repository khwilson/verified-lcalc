module

public import VerifiedLcalc.Certificate.IntegralXSupport
public import VerifiedLcalc.Certificates.AlgebraicRank
public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.Tate.WildRootCore

/-! # Input for elliptic-curve certification

Optional claims and arithmetic witnesses for the `certify_ec` command.
-/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

/-- An integral or scalar-valued discriminant together with its curve and exact proof. -/
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
  bInvariants : Option { b : R × R × R × R // (curve.b₂, curve.b₄, curve.b₆, curve.b₈) = b } := none
  /-- The ordered pair of c₄ and c₆ with a proof about the equation. -/
  cInvariants : Option { c : R × R // (curve.c₄, curve.c₆) = c } := none

/-- Attach a standalone discriminant witness to its own equation. -/
def DiscriminantWitness.toProofs {R : Type*} [CommRing R] (w : DiscriminantWitness R) :
    EllipticProofs w.curve :=
  { discriminant := some ⟨w.discriminant, w.discriminant_eq⟩ }

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
  deriving Repr, DecidableEq

/-- A reported abc quality and evidence for its absolute error bound. -/
structure AbcQualityClaim where
  /-- Exact rational interpretation of the reported value. -/
  reported : Rat
  /-- Claimed maximum absolute error. -/
  error : Rat
  /-- All prime factors of the abc product, with multiplicity. -/
  factors : List Nat
  deriving Repr, DecidableEq

/-- Two proposed odd primes of good reduction and the gcd of their point counts. -/
structure TorsionBoundWitness where
  /-- First proposed prime of good reduction. -/
  firstPrime : Nat
  /-- Second proposed prime of good reduction. -/
  secondPrime : Nat
  /-- Claimed positive gcd of the two reduced point counts. -/
  bound : Nat
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
/-- Lean proofs accepted alongside raw claims on an integral Weierstrass equation. -/
structure IntegralCurveProofs (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] extends EllipticProofs curve where
  /-- Proved endpoints of a Mordell–Weil rank interval on the rational curve. -/
  algebraicRank : Option (AlgebraicRankBounds (curve.baseChange ℚ)) := none
  /-- Exhaustive abscissa support for integral points on the supplied equation. -/
  integralXSupport : Option (IntegralXSupport curve) := none

/-- The single input record for elliptic-curve certification. `none` means that
no data of that kind was supplied; `some []` is an explicitly supplied empty
list, not a claim of completeness. Numerical results are rank candidates;
analytic certification additionally needs checked minimality and local data.
This record asserts no mathematical validity. -/
structure EllipticWitness where
  /-- Integral Weierstrass equation representing the input curve. -/
  equation : WeierstrassCurve ℤ
  /-- LMFDB analytic rank to compare with an independently checked analytic payload. -/
  catalogueAnalyticRank : Option Nat := none
  /-- A supplied minimum-degree rational isogeny edge. -/
  isogenyEdge : Option IsogenyEdgeClaim := none
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
  /-- Selected indices for a rank bound; requires a supplied independence proof. -/
  independentPoints : Option (List Nat) := none
  /-- Numerical witness for a central-value enclosure. -/
  centralResult : Option CentralResult := none
  /-- Numerical witness for a first-derivative enclosure. -/
  derivativeResult : Option DerivativeResult := none
  /-- Prime factorization witness for minimality of the supplied equation. -/
  minimality : Option MinimalityWitness := none
  /-- Transcripts at 2 and 3 for the arithmetic conductor and root number. -/
  localData : Option WildData := none
  deriving Repr, DecidableEq

namespace EllipticWitness

/-- The requested conductor exponents, keyed by their rational primes. -/
def conductorValuations (w : EllipticWitness) : Option (List (Nat × Nat)) :=
  let claims := (w.localInvariants.getD []).filterMap fun row =>
    row.conductorValuation.map fun exponent => (row.prime, exponent)
  if claims.isEmpty then none else some claims

/-- Convenience constructor for a complete rank-zero candidate. -/
def central (r : CentralResult) (m : MinimalityWitness) (d : WildData) : EllipticWitness :=
  { equation := r.equation, centralResult := some r, minimality := some m, localData := some d }

/-- Convenience constructor for a complete rank-one candidate. -/
def derivative (r : DerivativeResult) (m : MinimalityWitness) (d : WildData) : EllipticWitness :=
  { equation := r.equation, derivativeResult := some r, minimality := some m, localData := some d }

theorem central_fields (r : CentralResult) (m : MinimalityWitness) (d : WildData) :
    (central r m d).equation = r.equation ∧
      (central r m d).centralResult = some r ∧
      (central r m d).derivativeResult = none ∧
      (central r m d).minimality = some m ∧ (central r m d).localData = some d :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem derivative_fields (r : DerivativeResult) (m : MinimalityWitness) (d : WildData) :
    (derivative r m d).equation = r.equation ∧
      (derivative r m d).derivativeResult = some r ∧
      (derivative r m d).centralResult = none ∧
      (derivative r m d).minimality = some m ∧ (derivative r m d).localData = some d :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end EllipticWitness
end VerifiedLcalc
