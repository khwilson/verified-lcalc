import VerifiedLcalc.UpstreamCandidates.TauCeti.Minimality
import VerifiedLcalc.UpstreamCandidates.TauCeti.TwoAdicMinimality
import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
import Lean

open Lean Elab Command

-- All extracted results must remain independent of project assumptions.
run_cmd do
  for name in [``WeierstrassCurve.minimal_of_small_discriminant,
      ``WeierstrassCurve.isMinimal_of_small_c4,
      ``WeierstrassCurve.isMinimal_of_small_c6,
      ``WeierstrassCurve.integral_c4_two_adic_gap,
      ``WeierstrassCurve.isMinimal_of_two_adic_c4_six,
      ``WeierstrassCurve.pointCountFinite_eq_pointCount,
      ``WeierstrassCurve.pointCount_map_equiv,
      ``WeierstrassCurve.frobeniusTrace_map_equiv] do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in upstream candidate {name}: {axiomName}"
