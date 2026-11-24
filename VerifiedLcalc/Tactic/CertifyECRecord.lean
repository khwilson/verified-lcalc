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

private def integralPointsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let witnessName := base ++ `witness
  unless (← optionalInput witnessName `integralCoordinates).isSome do return ← `(none)
  let w := rootIdent witnessName
  let point := rootIdent (base ++ `point)
  let integral := rootIdent (base ++ `point_integral)
  `(some ⟨(($w).integralCoordinates.getD []).length, fun i => ⟨$point i, $integral i⟩⟩)

private def rationalPointsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  unless (← getEnv).contains (base ++ `point) do return ← `(none)
  let coords := rootIdent (base ++ `coordinates)
  let point := rootIdent (base ++ `point)
  `(some ⟨($coords).length, $point⟩)

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
  `(some ⟨($indices).length, $selected, by
    first
    | exact $independent
    | let empty : IsEmpty (Fin ($indices).length) := ⟨fun i => Fin.elim0 i⟩
      exact linearIndependent_empty_type⟩)

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
  `(some (fun i => ⟨⟨$order i, $positive i⟩, $exactOrder i⟩))

private def integralYFiberTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let completeName := base ++ `integral_y_fiber_complete
  unless (← getEnv).contains completeName do return ← `(none)
  let roots := rootIdent (base ++ `integral_fiber_roots)
  let seed := rootIdent (base ++ `integral_fiber_seed)
  let fiber := rootIdent (base ++ `integral_y_fiber)
  let complete := rootIdent completeName
  `(some ⟨($roots).length, $seed, $fiber, by
    intro i y
    simpa only [$seed:term, WeierstrassCurve.pointOfIntegralSolution_eq_some,
      WeierstrassCurve.Affine.Point.xCoord_some, Rat.num_intCast] using $complete i y⟩)

private def completeIntegralPointsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let name := base ++ `integral_point_certificate
  if (← getEnv).contains name then
    return ← `(some $(rootIdent name))
  `(none)

private def optionalFactTerm (base field : Name) : CommandElabM (TSyntax `term) := do
  let name := base ++ field
  if (← getEnv).contains name then
    `(some $(rootIdent name))
  else
    `(none)

private def algebraicFactsTerm (base : Name) : CommandElabM (TSyntax `term) := do
  let integral ← integralPointsTerm base
  let fibers ← integralYFiberTerm base
  let completeIntegralPoints ← completeIntegralPointsTerm base
  let generators ← rationalPointsTerm (base ++ `generators)
  let heights ← optionalFactTerm base `canonical_heights_fact
  let infinite ← infiniteOrderFactsTerm base
  let independent ← independenceFactsTerm base `independent_points_eq
  let independentGenerators ← independenceFactsTerm base `independent_generator_points_eq
  let lowerBound ← rankLowerBoundTerm base
  let rankBounds ← rankBoundsTerm base
  let exactRank ← exactRankTerm base
  let regulator ← regulatorFactsTerm base
  `({ integralPoints := $integral, integralYFibers := $fibers,
      completeIntegralPoints := $completeIntegralPoints, generators := $generators,
      heights := $heights,
      infiniteOrderPoints := $infinite,
      independentPoints := $independent, independentGeneratorPoints := $independentGenerators,
      rankLowerBound := $lowerBound,
      rankBounds := $rankBounds, rank := $exactRank, regulator := $regulator })

private def torsionWitnessTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let child := base ++ `torsion_generators
  let generators ← rationalPointsTerm child
  let orders ← torsionGeneratorOrderTerm base
  let generation ← if (← getEnv).contains (child ++ `generates_torsion) then
    `(some ⟨$(rootIdent (child ++ `generates_torsion))⟩)
  else `(none)
  let presName := base ++ `torsion_presentation
  let presentation ← if (← getEnv).contains presName then
    `(some $(rootIdent presName))
  else `(none)
  let boundName := base ++ `torsion_bound
  unless (← getEnv).contains boundName do
    return ← `({ generators := $generators, orders := $orders })
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
  let primeSupport ← if (← getEnv).contains (base ++ `torsion_primes_exact) then
    `(some ⟨$(rootIdent (base ++ `torsion_primes)),
      $(rootIdent (base ++ `torsion_primes_nodup)),
      $(rootIdent (base ++ `torsion_primes_exact))⟩)
  else `(none)
  `({
    generators := $generators
    orders := $orders
    generation := $generation
    presentation := $presentation
    divisor := $divisor
    cardinality := $exactCardinality
    primeSupport := $primeSupport })

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
  let torsion ← torsionWitnessTerm base curve
  let intrinsicTorsion ← optionalFactTerm base `intrinsic_torsion_fact
  let torsionGrowthField ← optionalFactTerm base `torsion_growth_field_fact
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
  let nonmaxPrimes ← optionalFactTerm base `nonmax_prime_support
  let adelicGenerators ← optionalFactTerm base `adelic_generator_fact
  let adelicImage ← optionalFactTerm base `adelic_image_certificate
  let modPrimeImage ← optionalFactTerm base `modell_image_fact
  let modPrimeImages ← optionalFactTerm base `modell_images_fact
  let cm ← optionalFactTerm base `cm_fact
  let twist ← optionalFactTerm base `minimum_quadratic_twist_evidence
  let szpiroRatio ← optionalFactTerm base `szpiro_ratio_fact
  let faltingsIndex ← optionalFactTerm base `faltings_index_fact
  let modularParametrization ← optionalFactTerm base `modular_parametrization_fact
  let iwasawa ← optionalFactTerm base `iwasawa_fact
  let periodGeometry ← optionalFactTerm base `period_geometry_fact
  let realPeriod ← optionalFactTerm base `real_period_fact
  let tamagawaProduct ← optionalFactTerm base `tamagawa_product_fact
  let analyticSha ← optionalFactTerm base `analytic_sha_fact
  let roundedAnalyticSha ← optionalFactTerm base `rounded_analytic_sha_fact
  let catalogueName := base ++ `lmfdb_catalogue
  let catalogue ← if (← getEnv).contains catalogueName then
    `($(rootIdent catalogueName))
  else `({})
  let traceHash ← optionalFactTerm base `trace_hash_fact
  let cremonaCatalogue ← optionalFactTerm base `cremona_catalogue_fact
  let record ← `({
    nonsingular := $nonsingular
    equationFacts := $equationFacts
    rational := $rational
    algebraic := $algebraic
    arithmetic := $arithmetic
    analytic := $analytic
    torsion := $torsion
    intrinsicTorsion := $intrinsicTorsion
    torsionGrowthField := $torsionGrowthField
    isogeny := $isogeny
    isogenyClass := $isogenyClass
    lmfdbCatalogue := $catalogue
    traceHash := $traceHash
    cremonaCatalogue := $cremonaCatalogue
    nonmaxPrimes := $nonmaxPrimes
    adelicGenerators := $adelicGenerators
    adelicImage := $adelicImage
    modPrimeImage := $modPrimeImage
    modPrimeImages := $modPrimeImages
    complexMultiplication := $cm
    minimumQuadraticTwist := $twist
    modifiedSzpiroRatio := $szpiroRatio
    faltingsIndex := $faltingsIndex
    modularParametrization := $modularParametrization
    iwasawa := $iwasawa
    periodGeometry := $periodGeometry
    realPeriod := $realPeriod
    tamagawaProduct := $tamagawaProduct
    analyticSha := $analyticSha
    roundedAnalyticSha := $roundedAnalyticSha })
  let env ← getEnv
  if env.contains edgeName || env.contains className ||
      env.contains (base ++ `period_geometry_fact) ||
      env.contains (base ++ `modular_parametrization_fact) || env.contains (base ++ `iwasawa_fact) then
    emit (← `(noncomputable def $certificate : EllipticCertificate $curve := $record))
  else
    emit (← `(def $certificate : EllipticCertificate $curve := $record))
  auditAxioms name

end VerifiedLcalc.CertifyEC
