/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import Mathlib.Algebra.Polynomial.OfFn

/-! ## Exact presentations of the number fields in torsion growth rows -/

@[expose] public section

namespace VerifiedLcalc

open Polynomial

/-- Read ascending integral coefficients as a polynomial over ℚ. -/
def TorsionGrowthFieldClaim.polynomial (claim : TorsionGrowthFieldClaim) : Polynomial ℚ :=
  ofFn claim.coefficients.length fun i => (claim.coefficients[i] : ℚ)

end VerifiedLcalc
