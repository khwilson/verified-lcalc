module

public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.Tate.WildRootCore

/-!
# Witness fields for elliptic-curve certification
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
  /-- Integral Weierstrass coefficients of the curve being certified. -/
  equation : WeierstrassCurve ℤ
  /-- The supplied tuple of equation invariants b₂, b₄, b₆, and b₈. -/
  bInvariants : Option (Int × Int × Int × Int) := none
  /-- The supplied pair of equation invariants c₄ and c₆. -/
  cInvariants : Option (Int × Int) := none
  /-- The signed discriminant of the supplied equation. -/
  discriminant : Option Int := none
  /-- The supplied exact rational j-invariant. -/
  jInvariant : Option Rat := none
  /-- Whether the rational j-invariant belongs to the image of ℤ. -/
  jIntegral : Option Bool := none
  /-- The sign of the discriminant of the supplied equation. -/
  discriminantSign : Option Int := none
  /-- LMFDB absD; certification needs a checked globally minimal model. -/
  minimalDiscriminantAbs : Option Nat := none
  /-- Identification with the modular level uses the authorized modularity axiom. -/
  conductor : Option Nat := none
  /-- The global root number, with the same assumption boundary as the conductor. -/
  rootNumber : Option Int := none
  /-- Consecutive a_n values starting at n=1; JSON anlist also carries a_0=0. -/
  dirichletCoefficients : Option (List Int) := none
  /-- The supplied list of bad primes, to be checked for completeness and uniqueness. -/
  badPrimes : Option (List Nat) := none
  /-- The number of distinct bad primes. -/
  numBadPrimes : Option Nat := none
  /-- Supplied pairs of a prime and the corresponding L-series coefficient. -/
  primeCoefficients : Option (List (Nat × Int)) := none
  /-- Supplied affine integer coordinates whose point membership is requested. -/
  integralCoordinates : Option (List (Int × Int)) := none
  /-- Indices into the supplied integral-coordinate list. -/
  infiniteOrderPoints : Option (List Nat) := none
  /-- Selected indices for a rank bound; requires a supplied independence proof. -/
  independentPoints : Option (List Nat) := none
  /-- An exact numerical payload for a proposed analytic rank of zero. -/
  centralResult : Option CentralResult := none
  /-- An exact numerical payload for a proposed analytic rank of one. -/
  derivativeResult : Option DerivativeResult := none
  /-- A complete prime factorization of the absolute discriminant for checking minimality. -/
  minimality : Option MinimalityWitness := none
  /-- The supplied wild local reduction data at two and three. -/
  localData : Option WildData := none
  deriving Repr, DecidableEq

namespace EllipticWitness

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
