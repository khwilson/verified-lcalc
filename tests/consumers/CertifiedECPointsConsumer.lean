import CertifiedCurves.Direct

/-! # Reuse compiled point and numerical facts -/

theorem imported_infinite_order : ¬ IsOfFinAddOrder DirectPoints.infiniteOrder.point0.point :=
  DirectPoints.infiniteOrder.point0.infinite_order

theorem imported_algebraic_rank_lower_bound :
    (1 : Cardinal) ≤ Module.rank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectPoints.algebraic_rank_lower_bound

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``imported_infinite_order, ``imported_algebraic_rank_lower_bound] do
    for axiomName in ← liftTermElabM <| Lean.collectAxioms name do
      unless standard.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"

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

example : (DirectNumerics.certificate.analytic.central.get (by decide +kernel)).enclosure.isNone =
    true := rfl
example : DirectNumerics.certificate.analytic.rank.isNone = true := rfl
