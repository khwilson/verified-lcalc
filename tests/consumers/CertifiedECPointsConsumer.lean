import CertifiedCurves.Direct

-- These use compiled theorems only: no JSON, point search, or recertification.
theorem imported_infinite_order : ¬ IsOfFinAddOrder DirectPoints.infiniteOrder.point0.point :=
  DirectPoints.infiniteOrder.point0.infinite_order

theorem imported_algebraic_rank_lower_bound :
    (1 : Cardinal) ≤ Module.rank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectPoints.algebraic_rank_lower_bound

#print axioms imported_infinite_order
#print axioms imported_algebraic_rank_lower_bound

example : DirectPoints.certificate.algebraic.independentPoints.isSome = true := rfl
example : DirectPoints.certificate.algebraic.rankLowerBound.map Subtype.val = some 1 := rfl

private def importedIndexedInfinite :=
  (DirectPoints.certificate.algebraic.infiniteOrderPoints.getD []).get ⟨0, by decide +kernel⟩

example :
    ¬ IsOfFinAddOrder
      ((DirectPoints.certificate.algebraic.integralPoints.getD
        (VerifiedLcalc.AffineMembership.empty DirectPoints.curve)).rationalPoint
        importedIndexedInfinite.val) :=
  importedIndexedInfinite.property

private def importedIndexedFamily :=
  DirectPoints.certificate.algebraic.independentPoints.get (by decide +kernel)

example : LinearIndependent ℤ importedIndexedFamily.points := importedIndexedFamily.independent
