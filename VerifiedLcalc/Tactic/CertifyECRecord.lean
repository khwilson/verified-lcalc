module

public import VerifiedLcalc.Certificate.CheckedElliptic
public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Tactic.CertifyECArithmeticFacts
public import VerifiedLcalc.Tactic.CertifyECAnalyticFacts
public meta import Lean

/-! Assemble the public certificate from the facts the command has already audited. -/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta

private def invariantValue (base label : Name) : CommandElabM (TSyntax `term) := do
  let theoremName := base ++ label
  unless (← getEnv).contains theoremName do return ← `(none)
  let value := rootIdent (base ++ Name.mkSimple s!"claimed_{label}")
  let proof := rootIdent theoremName
  `(some ⟨$value, $proof⟩)

private def rationalFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let sign ← invariantValue base `discriminant_sign
  let j ← invariantValue base `j_invariant
  let integral ← invariantValue base `j_integral
  `({ discriminantSign := $sign, jInvariant := $j, jIntegral := $integral })

private def integralMembershipTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let witnessName := base ++ `witness
  unless (← optionalInput witnessName `integralCoordinates).isSome do return ← `(none)
  let w := rootIdent witnessName
  let sound := rootIdent (base ++ `points_on_curve)
  `(some ⟨($w).integralCoordinates.getD [], $sound⟩)

private def rationalMembershipTerm (base : Name) : CommandElabM (TSyntax `term) := do
  unless (← getEnv).contains (base ++ `points_on_curve) do return ← `(none)
  let coords := rootIdent (base ++ `coordinates)
  let sound := rootIdent (base ++ `points_on_curve)
  `(some ⟨$coords, $sound⟩)

private def infiniteOrderFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let ixName := base ++ `infinite_order_indices
  unless (← getEnv).contains ixName do return ← `(none)
  let ix := rootIdent ixName
  let count ← liftTermElabM do
    let size ← Term.elabTerm (← `(($ix).length)) (some (mkConst ``Nat))
    let some n ← (evalNat (← whnf size)).run
      | throwError "Expected closed checked infinite-order indices"
    return n
  let mut facts := #[]
  for i in [:count] do
    let child := base ++ `infiniteOrder ++ Name.mkSimple s!"point{i}"
    let index := rootIdent (child ++ `index)
    let valid := rootIdent (child ++ `index_valid)
    let sound := rootIdent (child ++ `infinite_order)
    facts := facts.push (← `(⟨⟨$index, $valid⟩, $sound⟩))
  `(some [$facts,*])

private def independenceFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let child := base ++ `algebraic
  unless (← getEnv).contains (child ++ `points_independent) do return ← `(none)
  let indices := rootIdent (child ++ `indices)
  let valid := rootIdent (child ++ `indices_valid)
  let independent := rootIdent (child ++ `points_independent)
  `(some ⟨$indices, $valid, $independent⟩)

private def rankLowerBoundTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let theoremName := base ++ `algebraic_rank_lower_bound
  unless (← getEnv).contains theoremName do return ← `(none)
  let indicesName := base ++ `algebraic.indices
  let count ← if (← getEnv).contains indicesName then
    `(($(rootIdent indicesName)).length)
  else `(1)
  let proof := rootIdent theoremName
  `(some ⟨$count, $proof⟩)

private def torsionGeneratorOrderTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let child := base ++ `torsion_generators
  unless (← getEnv).contains (child ++ `exact_order) do return ← `(none)
  let orders := rootIdent (child ++ `orders)
  let length := rootIdent (child ++ `orders_length)
  let support := rootIdent (child ++ `orders_in_range)
  let exactOrder := rootIdent (child ++ `exact_order)
  `(some ⟨$orders, $length, by
    intro n h
    exact (of_decide_eq_true (List.all_eq_true.mp $support n h)).1, $exactOrder⟩)

private def algebraicFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let integral ← integralMembershipTerm base
  let generators ← rationalMembershipTerm (base ++ `generators)
  let torsionGenerators ← rationalMembershipTerm (base ++ `torsion_generators)
  let torsionOrders ← torsionGeneratorOrderTerm base
  let infinite ← infiniteOrderFactsTerm base
  let independent ← independenceFactsTerm base
  let lowerBound ← rankLowerBoundTerm base
  `({ integralPoints := $integral, generators := $generators,
      torsionGenerators := $torsionGenerators, torsionGeneratorOrders := $torsionOrders,
      infiniteOrderPoints := $infinite,
      independentPoints := $independent, rankLowerBound := $lowerBound })

private def torsionFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let boundName := base ++ `torsion_bound
  unless (← getEnv).contains boundName do return ← `({})
  let evidence := rootIdent (base ++ `claimed_torsion_bound)
  let checkedBound := rootIdent (base ++ `torsion_bound_value_valid)
  let valid := rootIdent boundName
  let consistent ← if (← getEnv).contains (base ++ `torsion_claim_consistent) then
    `(some ⟨$(rootIdent (base ++ `claimed_torsion)),
      $(rootIdent (base ++ `torsion_claim_consistent))⟩)
  else `(none)
  let exactName := base ++ `torsion
  let exactCardinality ← if (← getEnv).contains exactName then do
    let value ← liftTermElabM do
      let type ← inferType (mkConst exactName)
      let some (_, _, value) := type.eq? | throwError "Expected an exact torsion cardinality"
      pure value
    let n ← literalSyntax value
    `(some ⟨$n, $(rootIdent exactName)⟩)
  else `(none)
  `({ divisor := some ⟨$evidence, $checkedBound, $valid, $consistent⟩,
      cardinality := $exactCardinality })

/-- Emit the indexed public certificate with a standard-axiom dependency audit. -/
def certifyRecord (base : Name) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  let nonsingular := rootIdent (base ++ `nonsingular)
  let eqName := base ++ `checked_facts
  let equationFacts ← if (← getEnv).contains eqName then
    `($(rootIdent eqName))
  else `({})
  let rational ← rationalFactsTerm base
  let algebraic ← algebraicFactsTerm base
  let arithmetic ← arithmeticFactsTerm base curve
  let analytic ← analyticFactsTerm base curve
  let torsion ← torsionFactsTerm base
  let name := base ++ `certificate
  let certificate := rootIdent name
  emit (← `(def $certificate : EllipticCertificate $curve :=
    { nonsingular := $nonsingular, equationFacts := $equationFacts,
      rational := $rational, algebraic := $algebraic, arithmetic := $arithmetic,
      analytic := $analytic, torsion := $torsion }))
  auditAxioms name

end VerifiedLcalc.CertifyEC
