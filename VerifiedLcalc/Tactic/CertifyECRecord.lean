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
  let abcQuality ← if (← getEnv).contains (base ++ `abc_quality) then
    `(some ⟨$(rootIdent (base ++ `claimed_abc_quality)), $(rootIdent (base ++ `abc_quality_valid)),
      $(rootIdent (base ++ `abc_quality_defined)), $(rootIdent (base ++ `abc_quality))⟩)
  else `(none)
  `({ discriminantSign := $sign, jInvariant := $j, jIntegral := $integral,
      abcQuality := $abcQuality })

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

private def generatorCountTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let proofName := base ++ `generators.count_valid
  unless (← getEnv).contains proofName do return ← `(none)
  let count := rootIdent (base ++ `generators.count)
  `(some ⟨$count, $(rootIdent proofName)⟩)

private def rankBoundsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let proofName := base ++ `algebraic_rank_witness
  unless (← getEnv).contains proofName do return ← `(none)
  `(some $(rootIdent proofName))

private def exactRankTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let proofName := base ++ `algebraic_rank
  unless (← getEnv).contains proofName do return ← `(none)
  `(some ⟨$(rootIdent (base ++ `mordell_weil_rank)), $(rootIdent proofName)⟩)

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

private def integralYFiberTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let completeName := base ++ `integral_y_fiber_complete
  unless (← getEnv).contains completeName do return ← `(none)
  let curve := rootIdent (base ++ `curve)
  let roots := rootIdent (base ++ `integral_fiber_roots)
  let valid := rootIdent (base ++ `integral_fiber_roots_valid)
  let fiber := rootIdent (base ++ `integral_y_fiber)
  let complete := rootIdent completeName
  `(some ⟨⟨$roots, EllipticWitness.affineCoordinatesValid_sound $curve $roots $valid⟩,
    $fiber, $complete⟩)

private def algebraicFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let integral ← integralMembershipTerm base
  let fibers ← integralYFiberTerm base
  let generators ← rationalMembershipTerm (base ++ `generators)
  let generatorCount ← generatorCountTerm base
  let torsionGenerators ← rationalMembershipTerm (base ++ `torsion_generators)
  let torsionOrders ← torsionGeneratorOrderTerm base
  let infinite ← infiniteOrderFactsTerm base
  let independent ← independenceFactsTerm base
  let lowerBound ← rankLowerBoundTerm base
  let rankBounds ← rankBoundsTerm base
  let exactRank ← exactRankTerm base
  `({ integralPoints := $integral, integralYFibers := $fibers, generators := $generators,
      generatorCount := $generatorCount,
      torsionGenerators := $torsionGenerators, torsionGeneratorOrders := $torsionOrders,
      infiniteOrderPoints := $infinite,
      independentPoints := $independent, rankLowerBound := $lowerBound,
      rankBounds := $rankBounds, rank := $exactRank })

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
  let cyclic ← if (← getEnv).contains (base ++ `torsion_structure) &&
      !(← getEnv).contains (base ++ `torsion_structure_equiv) then
    `(some ⟨$(rootIdent (base ++ `claimed_torsion_structure)),
      $(rootIdent (base ++ `cyclic_torsion_order)),
      $(rootIdent (base ++ `cyclic_torsion_generator)), $(rootIdent (base ++ `torsion_structure))⟩)
  else `(none)
  let twoFactor ← if (← getEnv).contains (base ++ `torsion_structure_equiv) then
    `(some ⟨$(rootIdent (base ++ `torsion_structure_second_order)),
      $(rootIdent (base ++ `torsion_structure_second_order_positive)),
      $(rootIdent (base ++ `torsion_structure_first_factor_dvd_second)),
      $(rootIdent (base ++ `torsion_structure_first_generator)),
      $(rootIdent (base ++ `torsion_structure_second_generator)),
      $(rootIdent (base ++ `torsion_structure_equiv)),
      $(rootIdent (base ++ `torsion_structure_first_image)),
      $(rootIdent (base ++ `torsion_structure_second_image)),
      $(rootIdent (base ++ `torsion_structure_cardinality))⟩)
  else `(none)
  let primeSupport ← if (← getEnv).contains (base ++ `torsion_primes_exact) then
    `(some ⟨$(rootIdent (base ++ `torsion_primes)),
      $(rootIdent (base ++ `torsion_primes_nodup)),
      $(rootIdent (base ++ `torsion_primes_exact))⟩)
  else `(none)
  `({ divisor := some ⟨$evidence, $checkedBound, $valid, $consistent⟩,
      cardinality := $exactCardinality, cyclicStructure := $cyclic,
      twoFactorStructure := $twoFactor, primeSupport := $primeSupport })

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
  let edgeName := base ++ `degree_two_isogeny
  let isogeny ← if (← getEnv).contains edgeName then
    `(some ⟨$(rootIdent (base ++ `isogeny_target)), $(rootIdent edgeName)⟩)
  else `(none)
  let record ← `({
    nonsingular := $nonsingular
    equationFacts := $equationFacts
    rational := $rational
    algebraic := $algebraic
    arithmetic := $arithmetic
    analytic := $analytic
    torsion := $torsion
    isogeny := $isogeny })
  if (← getEnv).contains edgeName ||
      (← getEnv).contains (base ++ `torsion_structure_equiv) then
    emit (← `(noncomputable def $certificate : EllipticCertificate $curve := $record))
  else
    emit (← `(def $certificate : EllipticCertificate $curve := $record))
  auditAxioms name

end VerifiedLcalc.CertifyEC
