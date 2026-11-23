/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
public import Mathlib.Algebra.Polynomial.OfFn

/-! ## Field presentations and ordered height witnesses -/

@[expose] public section

namespace VerifiedLcalc

open Polynomial

/-- Read ascending integral coefficients as a polynomial over ℚ. -/
def TorsionGrowthFieldClaim.polynomial (claim : TorsionGrowthFieldClaim) : Polynomial ℚ :=
  ofFn claim.coefficients.length fun i => (claim.coefficients[i] : ℚ)

/-- If the coefficient list ends in a nonzero coefficient at the claimed index,
the decoded polynomial has the claimed degree. -/
theorem TorsionGrowthFieldClaim.natDegree_eq (claim : TorsionGrowthFieldClaim)
    (length : claim.coefficients.length = claim.degree + 1)
    (leading : claim.coefficients[claim.degree]?.getD 0 ≠ 0) :
    claim.polynomial.natDegree = claim.degree := by
  have h : claim.degree < claim.coefficients.length := by omega
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have upper := ofFn_natDegree_lt (by omega : 1 ≤ claim.coefficients.length)
      (fun i => (claim.coefficients[i] : ℚ))
    rw [polynomial]
    omega
  · rw [polynomial, ofFn_coeff_eq_val_of_lt _ h]
    rw [List.getElem?_eq_getElem h, Option.getD_some] at leading
    exact_mod_cast leading

/-- The absolute degree of the field presented by the growth witness. -/
def TorsionGrowthFieldFact.degree {curve : WeierstrassCurve ℤ}
    (fact : TorsionGrowthFieldFact curve) : ℕ :=
  fact.polynomial.natDegree

/-- The absolute degree is the dimension of the field as a rational vector space. -/
theorem TorsionGrowthFieldFact.degree_eq {curve : WeierstrassCurve ℤ}
    (fact : TorsionGrowthFieldFact curve) :
    Module.finrank ℚ (AdjoinRoot fact.polynomial) = fact.degree :=
  finrank_quotient_span_eq_natDegree

/-- Transfer indexed heights along equality of the entire ordered coordinate list. -/
def CanonicalHeightFacts.ofCoordinatesEq {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    {source target : AffineMembership curve} (facts : CanonicalHeightFacts source)
    (equal : source.coordinates = target.coordinates) : CanonicalHeightFacts target := by
  cases source
  cases target
  cases equal
  exact facts

end VerifiedLcalc
