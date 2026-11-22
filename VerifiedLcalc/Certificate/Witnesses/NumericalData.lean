/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Enclosures
public import VerifiedLcalc.Certificate.Witnesses.PrecisionPolicy
public import VerifiedLcalc.Certificates.Enclosures
public import VerifiedLcalc.Certificates.WeierstrassInstances

/-! Raw central-value and first-derivative numerical output records. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

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
  finite : RealInterval
  /-- Bound on the omitted normalized integral from `cutoff` to infinity. -/
  tail : Rat
  /-- Rational rectangle enclosing the normalized derivative integral. -/
  box : Box

end VerifiedLcalc.EllipticCurve
