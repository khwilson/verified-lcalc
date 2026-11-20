import CertifiedCurves.Direct

-- These use compiled theorems only: no JSON, point search, or recertification.
theorem imported_infinite_order : ¬ IsOfFinAddOrder DirectOrder.point :=
  DirectOrder.infinite_order

theorem imported_algebraic_rank_lower_bound :
    (1 : Cardinal) ≤ Module.rank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectRank.algebraic_rank_lower_bound

#print axioms imported_infinite_order
#print axioms imported_algebraic_rank_lower_bound
