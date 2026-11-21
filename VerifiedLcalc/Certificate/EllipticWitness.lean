module

public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.Tate.WildRootCore

/-! # Optional input facts for elliptic-curve certification -/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

/-- The single input record for elliptic-curve certification. `none` means that
no data of that kind was supplied; `some []` is an explicitly supplied empty
list, not a claim of completeness. Numerical results are rank candidates;
analytic certification additionally needs checked minimality and local data.
This record asserts no mathematical validity. -/
structure EllipticWitness where
  equation : WeierstrassCurve ℤ
  bInvariants : Option (Int × Int × Int × Int) := none
  cInvariants : Option (Int × Int) := none
  discriminant : Option Int := none
  jInvariant : Option Rat := none
  discriminantSign : Option Int := none
  /-- LMFDB absD; certification needs a checked globally minimal model. -/
  minimalDiscriminantAbs : Option Nat := none
  /-- Identification with the modular level uses the authorized modularity axiom. -/
  conductor : Option Nat := none
  rootNumber : Option Int := none
  /-- Consecutive a_n values starting at n=1; JSON anlist also carries a_0=0. -/
  dirichletCoefficients : Option (List Int) := none
  badPrimes : Option (List Nat) := none
  numBadPrimes : Option Nat := none
  primeCoefficients : Option (List (Nat × Int)) := none
  integralCoordinates : Option (List (Int × Int)) := none
  /-- Rational affine coordinates for the LMFDB generator list, checked for membership. -/
  generatorCoordinates : Option (List (Rat × Rat)) := none
  /-- Rational affine coordinates for the LMFDB torsion generator list, checked for membership. -/
  torsionGeneratorCoordinates : Option (List (Rat × Rat)) := none
  /-- Indices into the supplied integral-coordinate list. -/
  infiniteOrderPoints : Option (List Nat) := none
  /-- Selected indices for a rank bound; requires a supplied independence proof. -/
  independentPoints : Option (List Nat) := none
  centralResult : Option CentralResult := none
  derivativeResult : Option DerivativeResult := none
  minimality : Option MinimalityWitness := none
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
