import CertifiedCurves.Direct
import VerifiedLcalcTests.Fixtures.RationalIndependence

/-! # Reuse compiled point and numerical facts -/

theorem imported_infinite_order : ¬ IsOfFinAddOrder DirectPoints.infiniteOrder.point0.point :=
  DirectPoints.infiniteOrder.point0.infinite_order

theorem imported_algebraic_rank_lower_bound :
    1 ≤ Module.finrank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
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

open VerifiedLcalcTests.RationalIndependence in
example : Rank189.certificate.algebraic.integralPoints = none := rfl

open VerifiedLcalcTests.RationalIndependence in
example : Rank189.certificate.algebraic.independentPoints = none := rfl

open VerifiedLcalcTests.RationalIndependence in
example : Rank189.certificate.algebraic.rankLowerBound.map Subtype.val = some 1 := rfl

open VerifiedLcalcTests.RationalIndependence in
example : Rank189Lean.certificate.algebraic.rankLowerBound.map Subtype.val = some 1 := rfl

section RationalGenerator

open VerifiedLcalcTests.RationalIndependence

example : Rank189Lean.certificate.algebraic.generatorCount = some 1 := rfl

private def rationalFamily :=
  Rank189.certificate.algebraic.independentGeneratorPoints.get (by decide +kernel)

example : rationalFamily.rank = 1 := rfl
example : (rationalFamily.indices ⟨0, by decide +kernel⟩).val = 0 := rfl
example : LinearIndependent ℤ rationalFamily.points := rationalFamily.independent
example : rationalFamily.points ⟨0, by decide +kernel⟩ =
    Rank189.generators.point ⟨0, by decide +kernel⟩ := rfl

example : 1 ≤ Module.finrank ℤ (Rank189.curve.baseChange ℚ).toAffine.Point :=
  Rank189.algebraic_rank_lower_bound

example : Rank189.certificate.algebraic.rank = none := rfl

open Lean Elab Command in
run_cmd do
  for name in [``Rank189.certificate, ``Rank189Lean.certificate,
      ``Rank189.algebraic.points_independent, ``Rank189.algebraic_rank_lower_bound] do
    for assumption in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected rational independence axiom {assumption} in {name}"

end RationalGenerator
