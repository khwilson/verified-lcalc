module

public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.WildRootCore

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

/-- Supplied numerical and local arithmetic data. This type asserts no validity.
`certify_ec` checks it without invoking numerical or arithmetic witness search. -/
inductive EllipticWitness where
  | central (result : CentralResult) (minimality : MinimalityWitness) (localData : WildData)
  | derivative (result : DerivativeResult) (minimality : MinimalityWitness) (localData : WildData)
  deriving Repr, DecidableEq

end VerifiedLcalc
