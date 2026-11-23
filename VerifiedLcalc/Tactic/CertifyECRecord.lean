module

public import VerifiedLcalc.Certificate.CheckedElliptic
public import VerifiedLcalc.Verification.TorsionBoundFacts
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
    `(some (Certification.abcQualityFactsOfCheck _
      $(rootIdent (base ++ `claimed_abc_quality))
      $(rootIdent (base ++ `abc_quality_valid))).facts)
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

private def independenceFactsTerm (base inputEquality : Name) :
    CommandElabM (TSyntax `term) := do
  unless (← getEnv).contains (base ++ inputEquality) do return ← `(none)
  let child := base ++ `algebraic
  let indices := rootIdent (child ++ `indices)
  let selected := rootIdent (child ++ `point_indices)
  let independent := rootIdent (child ++ `points_independent)
  `(some ⟨($indices).length, $selected, $independent⟩)

private def rankLowerBoundTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let theoremName := base ++ `algebraic_rank_lower_bound
  unless (← getEnv).contains theoremName do return ← `(none)
  let indicesName := base ++ `algebraic.indices
  let count ← if (← getEnv).contains indicesName then
    `(($(rootIdent indicesName)).length)
  else `(1)
  let proof := rootIdent theoremName
  `(some ⟨$count, $proof⟩)

private def rankBoundsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let proofName := base ++ `algebraic_rank_witness
  unless (← getEnv).contains proofName do return ← `(none)
  `(some $(rootIdent proofName))

private def exactRankTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let proofName := base ++ `algebraic_rank
  unless (← getEnv).contains proofName do return ← `(none)
  `(some ⟨$(rootIdent (base ++ `mordell_weil_rank)), $(rootIdent proofName)⟩)

private def regulatorFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let name := base ++ `regulator_facts
  unless (← getEnv).contains name do return ← `(none)
  `(some $(rootIdent name))

private def torsionGeneratorOrderTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let child := base ++ `torsion_generators
  unless (← getEnv).contains (child ++ `exact_order) do return ← `(none)
  let order := rootIdent (child ++ `order)
  let positive := rootIdent (child ++ `order_positive)
  let exactOrder := rootIdent (child ++ `exact_order)
  `(some ⟨$order, $positive, $exactOrder⟩)

private def torsionWitnessTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let child := base ++ `torsion_generators
  unless (← getEnv).contains (child ++ `points_on_curve) do return ← `(none)
  let coords := rootIdent (child ++ `coordinates)
  let sound := rootIdent (child ++ `points_on_curve)
  let orders ← torsionGeneratorOrderTerm base
  let generation ← if (← getEnv).contains (child ++ `generates_torsion) then
    `(some ⟨$(rootIdent (child ++ `generates_torsion))⟩)
  else `(none)
  `(some {
    elliptic := inferInstance
    membership := ⟨$coords, $sound⟩
    orders := $orders
    generation := $generation })

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

private def completeIntegralPointsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let name := base ++ `integral_point_certificate
  if (← getEnv).contains name then
    return ← `(some $(rootIdent name))
  `(none)

private def algebraicFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let integral ← integralMembershipTerm base
  let fibers ← integralYFiberTerm base
  let completeIntegralPoints ← completeIntegralPointsTerm base
  let generators ← rationalMembershipTerm (base ++ `generators)
  let infinite ← infiniteOrderFactsTerm base
  let independent ← independenceFactsTerm base `independent_points_eq
  let independentGenerators ← independenceFactsTerm base `independent_generator_points_eq
  let lowerBound ← rankLowerBoundTerm base
  let rankBounds ← rankBoundsTerm base
  let exactRank ← exactRankTerm base
  let regulator ← regulatorFactsTerm base
  `({ integralPoints := $integral, integralYFibers := $fibers,
      completeIntegralPoints := $completeIntegralPoints, generators := $generators,
      infiniteOrderPoints := $infinite,
      independentPoints := $independent, independentGeneratorPoints := $independentGenerators,
      rankLowerBound := $lowerBound,
      rankBounds := $rankBounds, rank := $exactRank, regulator := $regulator })

private def torsionFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let family ← torsionWitnessTerm base
  let boundName := base ++ `torsion_bound
  unless (← getEnv).contains boundName do return ← `({ family := $family })
  let evidence := rootIdent (base ++ `claimed_torsion_bound)
  let checkedBound := rootIdent (base ++ `torsion_bound_value_valid)
  let consistent ← if (← getEnv).contains (base ++ `torsion_claim_consistent) then
    `(some ⟨$(rootIdent (base ++ `claimed_torsion)),
      $(rootIdent (base ++ `torsion_claim_consistent))⟩)
  else `(none)
  let divisor ← `(some ({ Certification.torsionDivisorFacts_of_check $curve $evidence
    $checkedBound with consistentClaim := $consistent }))
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
      $(rootIdent (base ++ `cyclic_torsion_generator)),
      $(rootIdent (base ++ `torsion_structure))⟩)
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
  `({ family := $family, divisor := $divisor,
      cardinality := $exactCardinality, cyclicStructure := $cyclic,
      twoFactorStructure := $twoFactor, primeSupport := $primeSupport })

private def optionalFactTerm (base field : Name) : CommandElabM (TSyntax `term) := do
  let name := base ++ field
  if (← getEnv).contains name then
    `(some $(rootIdent name))
  else
    `(none)

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
  let torsion ← torsionFactsTerm base curve
  let name := base ++ `certificate
  let certificate := rootIdent name
  let edgeName := base ++ `degree_two_isogeny
  let isogeny ← if (← getEnv).contains edgeName then
    `(some ⟨$(rootIdent (base ++ `isogeny_target)), $(rootIdent edgeName)⟩)
  else `(none)
  let className := base ++ `isogeny_class
  let isogenyClass ← if (← getEnv).contains className then
    `(some ⟨$(rootIdent className), ($(rootIdent (base ++ `isogeny_class_evidence))).ordering⟩)
  else `(none)
  let realPeriod ← optionalFactTerm base `real_period_fact
  let tamagawaProduct ← optionalFactTerm base `tamagawa_product_fact
  let analyticSha ← optionalFactTerm base `analytic_sha_fact
  let roundedAnalyticSha ← optionalFactTerm base `rounded_analytic_sha_fact
  let record ← `({
    nonsingular := $nonsingular
    equationFacts := $equationFacts
    rational := $rational
    algebraic := $algebraic
    arithmetic := $arithmetic
    analytic := $analytic
    torsion := $torsion
    isogeny := $isogeny
    isogenyClass := $isogenyClass
    realPeriod := $realPeriod
    tamagawaProduct := $tamagawaProduct
    analyticSha := $analyticSha
    roundedAnalyticSha := $roundedAnalyticSha })
  if (← getEnv).contains edgeName || (← getEnv).contains className ||
      (← getEnv).contains (base ++ `torsion_structure_equiv) then
    emit (← `(noncomputable def $certificate : EllipticCertificate $curve := $record))
  else
    emit (← `(def $certificate : EllipticCertificate $curve := $record))
  auditAxioms name

end VerifiedLcalc.CertifyEC
