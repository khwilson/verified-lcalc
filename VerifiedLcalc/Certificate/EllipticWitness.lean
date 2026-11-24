module

public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Certificate.Support.CurveProofs
public import VerifiedLcalc.Certificate.Support.SpecialValue
public import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
public import VerifiedLcalc.Certificate.Support.Torsion
public import VerifiedLcalc.Certificate.Support.AlgebraicRank
public import VerifiedLcalc.Certificate.Support.Regulator
public import VerifiedLcalc.EllipticCurve.AlgebraicRank
public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.Tate.WildRootCore

/-! # Input for elliptic-curve certification

Optional claims and arithmetic witnesses for the `certify_ec` command.
-/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

deriving instance Repr, DecidableEq for LocalReductionClaim
deriving instance Repr, DecidableEq for IsogenyEdgeClaim
deriving instance Repr, DecidableEq for DecimalEnclosureClaim
deriving instance Repr, DecidableEq for AdelicGeneratorsClaim
deriving instance Repr, DecidableEq for TorsionGrowthFieldClaim
deriving instance Repr, DecidableEq for PadicRegulatorClaim
deriving instance Repr, DecidableEq for CanonicalHeightsClaim
deriving instance Repr, DecidableEq for EllipticWitness

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

/-- The rank-zero constructor fills the central slot and leaves the derivative empty. -/
theorem central_fields (r : CentralResult) (m : MinimalityWitness) (d : WildData) :
    (central r m d).equation = r.equation ∧
      (central r m d).centralResult = some r ∧
      (central r m d).derivativeResult = none ∧
      (central r m d).minimality = some m ∧ (central r m d).localData = some d :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The rank-one constructor fills the derivative slot and leaves the central empty. -/
theorem derivative_fields (r : DerivativeResult) (m : MinimalityWitness) (d : WildData) :
    (derivative r m d).equation = r.equation ∧
      (derivative r m d).derivativeResult = some r ∧
      (derivative r m d).centralResult = none ∧
      (derivative r m d).minimality = some m ∧ (derivative r m d).localData = some d :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end EllipticWitness
end VerifiedLcalc
