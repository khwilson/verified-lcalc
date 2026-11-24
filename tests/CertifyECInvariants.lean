import CertifiedCurves.Invariants
import Lean

/-! Regression tests for stored invariant checks through `certify_ec`. -/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Native LMFDB rational pairs, canonical strings, exact integer literals, and
-- partial data all feed the same witness. Missing prerequisites emit no claim.
certify_ec Partial37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"jinv":[110592,37],"signD":1,"absD":37,
      "bad_primes":[37],"num_bad_primes":1,"semistable":true,"squarefree_disc":true,
      "local_invariants":[{"prime":37,"discriminant_valuation":1,
        "j_denominator_valuation":1,"reduction_type":-1,
        "conductor_valuation":1,"kodaira_symbol":5}],
      "conductor":37,"global_root_number":-1,"anlist":[0,1,-2,-3]}"#
example : (Partial37.curve.baseChange ℚ).j = 110592 / 37 := Partial37.j_invariant

certify_ec DirectAbcQuality from
  { equation := ⟨0, 1, 0, 0, 4⟩,
    abcQuality := some {
      reported := 1
      error := 1 / 10
      factors := [2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 11, 11] } }
example :
    |(DirectAbcQuality.curve.baseChange ℚ).abcQuality DirectAbcQuality.abc_quality_defined -
      1| ≤ (1 / 10 : ℝ) := by
  convert DirectAbcQuality.abc_quality using 1 <;> norm_num [DirectAbcQuality.claimed_abc_quality]

certify_ec RawAbcMetadata from_json_string
  r#"{"ainvs":[0,1,0,0,4],"abc_quality":1.0348177494302118}"#
example : RawAbcMetadata.witness.abcQuality = none := rfl

certify_ec TrivialTorsion from
  { equation := ⟨0, 0, 1, -1, 0⟩, torsionBound := some ⟨3, 5, 1⟩ }

example : Nat.card
    (AddCommGroup.torsion (TrivialTorsion.curve.baseChange ℚ).toAffine.Point) = 1 :=
  TrivialTorsion.torsion

certify_ec BoundedTorsion from_json_string
  r#"{"ainvs":[0,1,0,0,4],"torsion":2,
      "torsion_bound":{"first_prime":3,"second_prime":5,"bound":2}}"#

example : Nat.card
    (AddCommGroup.torsion (BoundedTorsion.curve.baseChange ℚ).toAffine.Point) ∣ 2 :=
  BoundedTorsion.torsion_bound.1

certify_ec UncheckedTorsion from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"torsion":11}"#

certify_ec JZero from_json_string
  r#"{"ainvs":[0,0,0,0,1],"jinv":"0","signD":-1,"discriminant":-432}"#
certify_ec IntegralJ from { equation := ⟨0, 0, 0, 0, 1⟩, jIntegral := some true }
example : IsLocalization.IsInteger ℤ (IntegralJ.curve.baseChange ℚ).j :=
  IntegralJ.j_integral.mpr rfl

certify_ec NonintegralJ from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"j_integral":false}"#
example : ¬ IsLocalization.IsInteger ℤ (NonintegralJ.curve.baseChange ℚ).j :=
  fun h => Bool.false_ne_true (NonintegralJ.j_integral.mp h)

certify_ec PotentialGood from
  { equation := ⟨0, 0, 0, 0, 1⟩, potentialGoodReduction := some true }
example : EllipticCurve.HasEverywherePotentialGoodReduction (PotentialGood.curve.baseChange ℚ) :=
  PotentialGood.potential_good_reduction.mpr rfl

certify_ec NoPotentialGood from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":false}"#
example :
    ¬ EllipticCurve.HasEverywherePotentialGoodReduction (NoPotentialGood.curve.baseChange ℚ) :=
  fun h => Bool.false_ne_true (NoPotentialGood.potential_good_reduction.mp h)
example : NoPotentialGood.witness.jIntegral = none := rfl

certify_ec J1728 from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"jinv":"1728/1","binvs":[0,-2,0,-1],"cinvs":[48,0]}"#

-- A local table's root_number must never become a global-root claim.
certify_ec LocalSignMetadata from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"prime":37,"root_number":1,"minimality":[37],
      "local_data":{"at_two":null,"at_three":null}}"#
example : LocalSignMetadata.witness.rootNumber = none := rfl
example : LocalSignMetadata.witness.localInvariants =
    some [{ prime := 37, rootNumber := some 1 }] := rfl

certify_ec LocalSignsFromLean from
  { LocalSignMetadata.witness with
    localInvariants := some [{ prime := 37, rootNumber := some 1 },
      { prime := 37, discriminantValuation := some 1 }, { prime := 2, rootNumber := some 1 }] }

example : ((LocalSignsFromLean.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).localRootNumbers.map fun f => ((f.prime : ℕ), f.value)) =
      [(37, 1), (2, 1)] := rfl

certify_ec LocalSignWithoutData from
  { equation := ⟨0, 0, 1, 0, -1⟩, minimality := some ⟨[3, 3, 3, 3, 3]⟩,
    localInvariants := some [{ prime := 3, rootNumber := some 1 }] }

example : (LocalSignWithoutData.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).localRootNumbers = [] := rfl

certify_ec LocalSignWithoutMinimality from
  { equation := ⟨0, 0, 1, -1, 0⟩, localData := some ⟨none, none⟩,
    localInvariants := some [{ prime := 37, rootNumber := some 1 }] }

example : LocalSignWithoutMinimality.certificate.arithmetic.minimalModel = none := rfl

certify_ec JSON37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"jinv":["110592","37"],"binvs":[0,-2,1,-1],"cinvs":[48,-216],
      "absD":37,"bad_primes":[37],"num_bad_primes":1,"semistable":true,"squarefree_disc":true,
      "local_invariants":[{"prime":37,"discriminant_valuation":1,
        "j_denominator_valuation":1,"reduction_type":-1,"conductor_valuation":1}],
      "conductor":37,"global_root_number":-1,"anlist":[0,1,-2,-3,2,-2,6,-1,0],
      "minimality":[37],"local_data":{"at_two":null,"at_three":null}}"#
example : JSON37.curve.Δ.natAbs = 37 := JSON37.minimal_discriminant_abs.2

example : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (JSON37.curve.baseChange ℚ) := JSON37.semistable.mpr rfl

example : (Modularity.modularWitness JSON37.curve JSON37.nonsingular).level.factorization 37 = 1 :=
  (JSON37.conductor_valuation (37, 1) (by decide +kernel)).2

certify_ec DirectConductorValuations from
  { Invariants37.witness with
    localInvariants := some
      [{ prime := 37, conductorValuation := some 1 },
       { prime := 2, conductorValuation := some 0 }] }

example :
    (Modularity.modularWitness DirectConductorValuations.curve
      DirectConductorValuations.nonsingular).level.factorization 2 = 0 :=
  (DirectConductorValuations.conductor_valuation (2, 0) (by decide +kernel)).2

certify_ec AdditiveLocal from_json_string
  r#"{"ainvs":[0,0,0,0,1],"minimality":[2,2,2,2,3,3,3],"semistable":false,
      "squarefree_disc":false,"prime":3,"discriminant_valuation":3,
      "j_denominator_valuation":0,"reduction_type":0}"#

example : ¬ WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (AdditiveLocal.curve.baseChange ℚ) := fun h => by
  have := AdditiveLocal.semistable.mp h
  contradiction

certify_ec GoodTamagawa from
  { equation := ⟨0, 0, 8, -16, 0⟩,
    localInvariants := some [{ prime := 3, tamagawaNumber := some 1 }] }

example : (GoodTamagawa.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 3) = 1 := by
  obtain ⟨_, h⟩ := GoodTamagawa.tamagawa_numbers { prime := 3, tamagawaNumber := some 1 }
    (by decide +kernel) 1 rfl
  exact h (by decide +kernel)

/--
info: TamagawaOutsideScope: Tamagawa claims outside good or I₁ reduction are unverified.
---
info: Certified TamagawaOutsideScope.ap_correct and TamagawaOutsideScope.point_integral
for the supplied lists
-/
#guard_msgs (whitespace := lax) in
certify_ec TamagawaOutsideScope from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"minimality":[11,11,11,11,11],"prime":11,"tamagawa_number":5}"#

certify_ec CompatibleTamagawaRows from_json_string
  r#"{"ainvs":[0,0,8,-16,0],"prime":3,"tamagawa_number":1,
      "local_invariants":[{"prime":3,"tamagawa_number":1}]}"#

certify_ec KodairaGood from
  { equation := ⟨0, 0, 1, -1, 0⟩, minimality := some ⟨[37]⟩,
    localInvariants := some [{ prime := 3, kodairaSymbol := some 1 }] }

example : (KodairaGood.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 3) = .I 0 := by
  obtain ⟨_, h⟩ := KodairaGood.kodaira_symbols { prime := 3, kodairaSymbol := some 1 }
    (by decide +kernel)
  exact h 1 rfl

/--
info: KodairaAdditive: additive Kodaira family verified. Exact additive codes unverified.
---
info: Certified KodairaAdditive.ap_correct and KodairaAdditive.point_integral for the supplied lists
-/
#guard_msgs in
certify_ec KodairaAdditive from_json_string
  r#"{"ainvs":[0,0,0,0,1],"minimality":[2,2,2,2,3,3,3],"prime":3,"kodaira_symbol":2}"#

example : ∀ n, (KodairaAdditive.curve.baseChange ℚ).reductionSymbol
    (RationalLocalRing 3) ≠ .I n := by
  obtain ⟨_, h⟩ := KodairaAdditive.kodaira_symbols { prime := 3, kodairaSymbol := some 2 }
    (by decide +kernel)
  exact h 2 rfl

certify_ec CompatibleKodairaRows from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"minimality":[37],"prime":3,"kodaira_symbol":1,
      "local_invariants":[{"prime":3,"kodaira_symbol":1}]}"#

certify_ec TrivialCyclicStructure from
  { equation := ⟨0, 0, 1, -1, 0⟩, torsionStructure := some [],
    torsionBound := some ⟨3, 5, 1⟩ }
example : Nonempty (ZMod 1 ≃+ AddCommGroup.torsion
    (TrivialCyclicStructure.curve.baseChange ℚ).toAffine.Point) := by
  obtain ⟨equiv, -⟩ := TrivialCyclicStructure.torsion_structure.2
  exact ⟨equiv⟩

certify_ec AssertedTorsionOnly from_json_string
  r#"{"ainvs":[0,1,0,0,4],"torsion":2,"torsion_structure":[2]}"#

certify_ec LooseTorsionBound from_json_string
  r#"{"ainvs":[0,1,0,0,4],"torsion":2,"torsion_structure":[2],
      "torsion_generators":[[-2,0,1]],"torsion_generator_orders":[2],
      "torsion_bound":{"first_prime":3,"second_prime":11,"bound":6}}"#
example :
    Nat.card (AddCommGroup.torsion (LooseTorsionBound.curve.baseChange ℚ).toAffine.Point) ∣ 6 :=
  LooseTorsionBound.torsion_bound.1

certify_ec LooseTorsionPrimeSupport from_json_string
  r#"{"ainvs":[0,1,0,-20,0],"torsion_primes":[2],
      "torsion_bound":{"first_prime":7,"second_prime":11,"bound":8}}"#
example : LooseTorsionPrimeSupport.certificate.torsion.primeSupport.isNone = true := rfl

run_cmd do
  if (← getEnv).contains `LooseTorsionPrimeSupport.torsion_primes then
    throwError "A loose torsion divisor generated exact prime support"

certify_ec NoncyclicTorsion from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"torsion":4,"torsion_structure":[2,2],
      "torsion_generators":[[0,0,1],[-1,0,1],[1,0,1]],"torsion_generator_orders":[2,2,2],
      "torsion_bound":{"first_prime":3,"second_prime":5,"bound":4}}"#

certify_ec SplitLocal from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"minimality":[11,11,11,11,11],
      "local_invariants":[{"prime":11,"reduction_type":1,"kodaira_symbol":9}]}"#

example :
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    (SplitLocal.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 11) = .I 5 := by
  let row : LocalReductionClaim :=
    { prime := 11, reductionType := some 1, kodairaSymbol := some 9 }
  obtain ⟨_, h⟩ := SplitLocal.kodaira_symbols row (by decide +kernel)
  exact h 9 rfl

run_cmd do
  let input ← CertifyEC.jsonInput
    r#"{"ainvs":[0,0,1,-1,0],"jinv":[110592,37]}"#
  CertifyEC.certifyAtomic `ProgrammaticInvariant input

example {R : Type*} [CommRing R] (curve : WeierstrassCurve R) (d : R)
    (h : curve.Δ = d) :
    (DiscriminantWitness.toProofs ⟨curve, d, h⟩).discriminant = some ⟨d, h⟩ := rfl

example {R : Type*} [CommRing R] (curve : WeierstrassCurve R) (d : R) (h : curve.Δ = d) :
    ({ discriminant := some ⟨d, h⟩ } : EllipticProofs curve).discriminant =
      some ⟨d, h⟩ := rfl

private theorem forbiddenDelta : Invariants37.curve.Δ = 37 :=
  (fun _ : Assumptions.GeneralEllipticModularity => Invariants37.discriminant)
    Assumptions.ellipticModularity

private def forbiddenFacts : EllipticProofs Invariants37.curve :=
  { discriminant := some ⟨37, forbiddenDelta⟩ }

example : JZero.discriminant_witness.curve.Δ = -432 :=
  JZero.discriminant_witness.discriminant_eq

certify_ec ComposedProofs from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"discriminant":37,"independent_points":[]}"#
  with_proofs Invariants37.discriminant_witness.toProofs
  with_independence (by exact linearIndependent_empty_type)

example : ComposedProofs.curve.Δ = 37 := ComposedProofs.discriminant

certify_ec EmptyProofs from
  { equation := Invariants37.curve }
  with_proofs ({} : EllipticProofs Invariants37.curve)

run_cmd do
  if (← getEnv).contains `EmptyProofs.discriminant_witness then
    throwError "An absent proved discriminant generated a witness"
  if (← getEnv).contains `EmptyProofs.checked_facts then
    throwError "An empty attachment generated a checked collection"
  let axs ← liftTermElabM <| Lean.collectAxioms ``forbiddenDelta
  unless axs.contains ``Assumptions.ellipticModularity do
    throwError "The forbidden proof fixture lost its axiom dependency"

meta def invariantRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Incorrect invariant accepted: {name}"
  for suffix in [`witness, `curve, `nonsingular, `j_invariant, `discriminant,
      `proofs, `discriminant_witness, `checked_facts, `certificate,
      `claimed_j_invariant, `claimed_j_integral, `j_integral, `j_integral_input_eq,
      `j_integral_value_valid, `claimed_discriminant, `global_minimal,
      `claimed_abc_quality, `abc_quality_input_eq, `abc_quality_valid, `abc_quality_defined,
      `abc_quality,
      `torsion, `torsion_bound, `claimed_torsion, `claimed_torsion_bound,
      `torsion_input_eq, `torsion_bound_input_eq, `torsion_bound_value_valid,
      `torsion_claim_consistent,
      `claimed_torsion_primes, `torsion_primes_input_eq, `torsion_primes_value_valid,
      `torsion_primes, `torsion_primes_nodup, `torsion_primes_exact,
      `claimed_potential_good_reduction, `potential_good_reduction,
      `potential_good_reduction_input_eq, `potential_good_reduction_value_valid,
      `minimal_discriminant_abs, `conductor, `root_number, `dirichlet_coefficients,
      `bad_primes, `bad_reduction_primes, `num_bad_primes,
      `local_invariants_agree, `local_invariants_agree_valid,
      `local_root_number_inputs_valid, `local_root_number_values_valid, `local_root_numbers,
      `semistable, `squarefree_discriminant, `local_invariants, `tamagawa_numbers, `kodaira_symbols,
      `tamagawa_values_valid, `claimed_semistable,
      `claimed_squarefree_discriminant, `claimed_local_invariants, `claimed_conductor_valuations,
      `conductor_valuations_input_eq, `conductor_valuation_value_valid, `conductor_valuation,
      `claimed_torsion_structure, `torsion_structure, `torsion_structure_order_consistent,
      `torsion_point_orders_consistent, `torsion_structure_divisor_consistent,
      `torsion_structure_normalized, `torsion_structure_equiv,
      `torsion_structure_second_order, `torsion_structure_first_generator,
      `torsion_structure_second_generator, `torsion_structure_image_witness,
      `torsion_structure_first_image, `torsion_structure_second_image,
      `torsion_structure_cardinality, `torsion_generators.independence_valid] do
    if env.contains (name ++ suffix) then throwError "Rejected invariant leaked {name ++ suffix}"

run_cmd do
  invariantRejected `WrongLocalRootNumber (← `(certify_ec WrongLocalRootNumber from
    { LocalSignMetadata.witness with
      localInvariants := some [{ prime := 37, rootNumber := some (-1) }] }))
  invariantRejected `NonSignLocalRootNumber (← `(certify_ec NonSignLocalRootNumber
    from_json_string r#"{"ainvs":[0,0,1,-1,0],"prime":37,"root_number":0}"#))
  invariantRejected `CompositeLocalRootPrime (← `(certify_ec CompositeLocalRootPrime from
    { equation := ⟨0, 0, 1, -1, 0⟩,
      localInvariants := some [{ prime := 4, rootNumber := some 1 }] }))
  invariantRejected `ConflictingLocalRootNumbers (← `(certify_ec ConflictingLocalRootNumbers
    from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"prime":37,"root_number":1,
        "local_invariants":[{"prime":37,"root_number":-1}]}"#))
  invariantRejected `InvalidWildLocalRootData (← `(certify_ec InvalidWildLocalRootData from
    { LocalSignWithoutData.witness with localData := some ⟨none, none⟩ }))
  invariantRejected `IncompatibleTamagawaRows (← `(certify_ec IncompatibleTamagawaRows
    from_json_string
    r#"{"ainvs":[0,0,8,-16,0],"prime":2,"tamagawa_number":1,
        "local_invariants":[{"prime":2,"tamagawa_number":2}]}"#))
  invariantRejected `IncompatibleTamagawaRowsReversed
    (← `(certify_ec IncompatibleTamagawaRowsReversed from_json_string
      r#"{"ainvs":[0,0,8,-16,0],"prime":2,"tamagawa_number":2,
          "local_invariants":[{"prime":2,"tamagawa_number":1}]}"#))
  invariantRejected `WrongTamagawa (← `(certify_ec WrongTamagawa from
    { GoodTamagawa.witness with
      localInvariants := some [{ prime := 3, tamagawaNumber := some 2 }] }))
  invariantRejected `IncompatibleAdditiveRows (← `(certify_ec IncompatibleAdditiveRows
    from_json_string
    r#"{"ainvs":[0,0,0,0,1],"minimality":[2,2,2,2,3,3,3],
        "prime":3,"kodaira_symbol":2,"local_invariants":[{"prime":3,"kodaira_symbol":3}]}"#))
  invariantRejected `IncompatibleAdditiveRowsReversed
    (← `(certify_ec IncompatibleAdditiveRowsReversed from_json_string
      r#"{"ainvs":[0,0,0,0,1],"minimality":[2,2,2,2,3,3,3],
          "prime":3,"kodaira_symbol":3,"local_invariants":[{"prime":3,"kodaira_symbol":2}]}"#))
  invariantRejected `AdditiveCodeAtGoodPrime (← `(certify_ec AdditiveCodeAtGoodPrime from
    { KodairaGood.witness with localInvariants := some [{ prime := 3, kodairaSymbol := some 2 }] }))
  invariantRejected `GoodCodeAtAdditivePrime (← `(certify_ec GoodCodeAtAdditivePrime from
    { KodairaAdditive.witness with
      localInvariants := some [{ prime := 3, kodairaSymbol := some 1 }] }))
  invariantRejected `AdditiveCodeAtMultiplicativePrime
    (← `(certify_ec AdditiveCodeAtMultiplicativePrime from
      { SplitLocal.witness with
        localInvariants := some [{ prime := 11, kodairaSymbol := some (-5) }] }))
  invariantRejected `WrongMultiplicativeIndex (← `(certify_ec WrongMultiplicativeIndex from
    { SplitLocal.witness with localInvariants := some [{ prime := 11, kodairaSymbol := some 5 }] }))
  invariantRejected `WrongAbcDecimal (← `(certify_ec WrongAbcDecimal from_json_string
    r#"{"ainvs":[0,1,0,0,4],"abc_quality":1.05,
        "abc_quality_evidence":{"error":[1,1000000],"factors":[2,2,2,2,3,3,3,5,5,7,11,11]}}"#))
  invariantRejected `MissingAbcDecimal (← `(certify_ec MissingAbcDecimal from_json_string
    r#"{"ainvs":[0,1,0,0,4],"abc_quality_evidence":{"error":1,"factors":[]}}"#))
  invariantRejected `WrongAbcFactors (← `(certify_ec WrongAbcFactors from
    { DirectAbcQuality.witness with
      abcQuality := some { DirectAbcQuality.claimed_abc_quality with
        factors := [2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 121] } }))
  invariantRejected `NegativeAbcError (← `(certify_ec NegativeAbcError from
    { DirectAbcQuality.witness with
      abcQuality := some { DirectAbcQuality.claimed_abc_quality with error := -1 } }))
  invariantRejected `UndefinedAbcZero (← `(certify_ec UndefinedAbcZero from
    { JZero.witness with abcQuality := some DirectAbcQuality.claimed_abc_quality }))
  invariantRejected `UndefinedAbc1728 (← `(certify_ec UndefinedAbc1728 from
    { J1728.witness with abcQuality := some DirectAbcQuality.claimed_abc_quality }))
  invariantRejected `ConflictingBProof (← `(certify_ec ConflictingBProof from
    { equation := Invariants37.curve, bInvariants := some (0, 0, 0, 0) }
    with_proofs Invariants37.checked_facts))
  invariantRejected `WrongTorsion (← `(certify_ec WrongTorsion from
    { TrivialTorsion.witness with torsion := some 2 }))
  invariantRejected `InconsistentTorsion (← `(certify_ec InconsistentTorsion from
    { BoundedTorsion.witness with torsion := some 3 }))
  invariantRejected `WrongTorsionBound (← `(certify_ec WrongTorsionBound from
    { TrivialTorsion.witness with torsionBound := some ⟨3, 5, 2⟩ }))
  invariantRejected `TorsionAtBadPrime (← `(certify_ec TorsionAtBadPrime from
    { TrivialTorsion.witness with torsionBound := some ⟨3, 37, 1⟩ }))
  invariantRejected `ConflictingAggregateReuse (← `(certify_ec ConflictingAggregateReuse from
    { equation := Invariants37.certificate.equation, cInvariants := some (48, 216) }
    with_proofs Invariants37.certificate.equationFacts))
  invariantRejected `WrongProofCurve (← `(certify_ec WrongProofCurve from
    { equation := JZero.curve } with_proofs Invariants37.discriminant_witness.toProofs))
  invariantRejected `ConflictingProofValue (← `(certify_ec ConflictingProofValue from
    { equation := Invariants37.curve, discriminant := some 36 }
    with_proofs Invariants37.discriminant_witness.toProofs))
  invariantRejected `ForbiddenProof (← `(certify_ec ForbiddenProof from
    { equation := Invariants37.curve } with_proofs forbiddenFacts))
  invariantRejected `WrongJ (← `(certify_ec WrongJ from
    { Invariants37.witness with jInvariant := some 0 }))
  invariantRejected `WrongIntegralJ (← `(certify_ec WrongIntegralJ from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"j_integral":true}"#))
  invariantRejected `WrongNonintegralJ (← `(certify_ec WrongNonintegralJ from
    { IntegralJ.witness with jIntegral := some false }))
  invariantRejected `WrongPotentialGood (← `(certify_ec WrongPotentialGood from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":true}"#))
  invariantRejected `WrongNoPotentialGood (← `(certify_ec WrongNoPotentialGood from
    { PotentialGood.witness with potentialGoodReduction := some false }))
  invariantRejected `DependentTorsionPair (← `(certify_ec DependentTorsionPair from_json_string
    r#"{"ainvs":[0,1,0,-20,0],"torsion":8,"torsion_structure":[2,4],
        "torsion_generators":[[4,0,1],[-2,6,1]],"torsion_generator_orders":[2,4],
        "torsion_bound":{"first_prime":7,"second_prime":11,"bound":8}}"#))
  invariantRejected `WrongTorsionPrimeSupport (← `(certify_ec WrongTorsionPrimeSupport
    from_json_string
    r#"{"ainvs":[0,1,0,-20,0],"torsion":8,"torsion_structure":[2,4],
        "torsion_primes":[3],"torsion_generators":[[0,0,1],[-2,6,1]],
        "torsion_generator_orders":[2,4],
        "torsion_bound":{"first_prime":7,"second_prime":11,"bound":8}}"#))
  invariantRejected `TorsionCountBelowPointOrder (← `(certify_ec TorsionCountBelowPointOrder
    from_json_string
    r#"{"ainvs":[0,1,0,0,4],"torsion":1,
        "torsion_generators":[[-2,0,1]],"torsion_generator_orders":[2],
        "torsion_bound":{"first_prime":3,"second_prime":5,"bound":2}}"#))
  invariantRejected `StructureCountMismatch (← `(certify_ec StructureCountMismatch
    from_json_string r#"{"ainvs":[0,1,0,0,4],"torsion":4,"torsion_structure":[2]}"#))
  invariantRejected `StructureAboveDivisor (← `(certify_ec StructureAboveDivisor
    from_json_string r#"{"ainvs":[0,1,0,0,4],"torsion_structure":[4],
        "torsion_bound":{"first_prime":3,"second_prime":5,"bound":2}}"#))
  invariantRejected `OrderAboveStructureExponent (← `(certify_ec OrderAboveStructureExponent from
    { equation := ⟨1, -1, -1, 0, 0⟩, torsionGeneratorCoordinates := some [(0, 0)],
      torsionGeneratorOrders := some [4], torsion := some 4, torsionStructure := some [2, 2],
      torsionBound := some ⟨5, 13, 8⟩ }))
  invariantRejected `WrongCyclicStructure (← `(certify_ec WrongCyclicStructure from
    { equation := ⟨1, -1, -1, 0, 0⟩, torsionGeneratorCoordinates := some [(0, 0)],
      torsionGeneratorOrders := some [4], torsion := some 4, torsionStructure := some [2, 2],
      torsionBound := some ⟨3, 5, 4⟩ }))
  invariantRejected `TorsionAtTwo (← `(certify_ec TorsionAtTwo from
    { TrivialTorsion.witness with torsionBound := some ⟨2, 5, 1⟩ }))
  invariantRejected `WrongDiscriminant (← `(certify_ec WrongDiscriminant from
    { Invariants37.witness with discriminant := some (-37) }))
  invariantRejected `WrongB (← `(certify_ec WrongB from
    { Invariants37.witness with bInvariants := some (0, 0, 0, 0) }))
  invariantRejected `WrongC (← `(certify_ec WrongC from
    { Invariants37.witness with cInvariants := some (48, 216) }))
  invariantRejected `WrongSign (← `(certify_ec WrongSign from
    { Invariants37.witness with discriminantSign := some 0 }))
  invariantRejected `WrongAbsD (← `(certify_ec WrongAbsD from
    { Invariants37.witness with minimalDiscriminantAbs := some 1 }))
  invariantRejected `MissingBadPrime (← `(certify_ec MissingBadPrime from
    { Invariants37.witness with badPrimes := some [] }))
  invariantRejected `DuplicateBadPrime (← `(certify_ec DuplicateBadPrime from
    { Invariants37.witness with badPrimes := some [37, 37] }))
  invariantRejected `WrongBadCount (← `(certify_ec WrongBadCount from
    { Invariants37.witness with numBadPrimes := some 2 }))
  invariantRejected `WrongSemistability (← `(certify_ec WrongSemistability from
    { Invariants37.witness with semistable := some false }))
  invariantRejected `WrongSquarefree (← `(certify_ec WrongSquarefree from
    { Invariants37.witness with squarefreeDiscriminant := some false }))
  invariantRejected `WrongLocalValuation (← `(certify_ec WrongLocalValuation from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, discriminantValuation := some 0 }] }))
  invariantRejected `WrongLocalJValuation (← `(certify_ec WrongLocalJValuation from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, jDenominatorValuation := some 0 }] }))
  invariantRejected `WrongLocalReduction (← `(certify_ec WrongLocalReduction from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, reductionType := some 1 }] }))
  invariantRejected `CompositeLocalPrime (← `(certify_ec CompositeLocalPrime from
    { Invariants37.witness with localInvariants := some [
        { prime := 4, discriminantValuation := some 0 }] }))
  invariantRejected `BadConductorValuation (← `(certify_ec BadConductorValuation from
    { DirectConductorValuations.witness with
      localInvariants := some [{ prime := 37, conductorValuation := some 50000 }] }))
  invariantRejected `CompositeConductorPrime (← `(certify_ec CompositeConductorPrime from
    { DirectConductorValuations.witness with
      localInvariants := some [{ prime := 4, conductorValuation := some 0 }] }))
  invariantRejected `WrongConductor (← `(certify_ec WrongConductor from
    { DirectConductorValuations.witness with conductor := some 1 }))
  invariantRejected `WrongRootNumber (← `(certify_ec WrongRootNumber from
    { Invariants37.witness with rootNumber := some 1 }))
  invariantRejected `WrongAN (← `(certify_ec WrongAN from
    { Invariants37.witness with dirichletCoefficients := some [1, 999] }))
  -- Scaling the equation scales its discriminant; it must not be passed off
  -- as a globally minimal model for an absD certificate.
  invariantRejected `NonminimalAbsD (← `(certify_ec NonminimalAbsD from
    { equation := ⟨0, 0, 8, -16, 0⟩, minimality := some ⟨[2,2,2,2,2,2,2,2,2,2,2,2,37]⟩,
      minimalDiscriminantAbs := some 151552 }))
  for suffix in [`minimal_discriminant_abs, `conductor, `root_number, `dirichlet_coefficients,
      `bad_primes, `bad_reduction_primes, `num_bad_primes,
      `semistable, `squarefree_discriminant, `local_invariants, `conductor_valuation,
      `kodaira_symbols] do
    if (← getEnv).contains (`Partial37 ++ suffix) then
      throwError "Missing arithmetic evidence generated an invariant claim"
  if (← getEnv).contains `GoodTamagawa.global_minimal then
    throwError "Local Tamagawa verification unexpectedly required global minimality"
  for name in [`BoundedTorsion, `UncheckedTorsion] do
    if (← getEnv).contains (name ++ `torsion) then
      throwError "Unproved torsion order generated a theorem"
  if (← getEnv).contains `NoPotentialGood.j_integral then
    throwError "An omitted j_integral claim generated a theorem"
  if (← getEnv).contains `IntegralJ.potential_good_reduction then
    throwError "An omitted potential_good_reduction claim generated a theorem"
  for suffix in [`torsion, `torsion_structure] do
    for name in [`AssertedTorsionOnly, `LooseTorsionBound] do
      if (← getEnv).contains (name ++ suffix) then
        throwError "Insufficient torsion evidence generated a claim"
  if (← getEnv).contains `LocalSignMetadata.root_number then
    throwError "Local root metadata became a global sign theorem"
  unless (← getEnv).contains `LocalSignMetadata.local_root_numbers do
    throwError "Top-level local root number was not checked"
  for name in [`LocalSignWithoutData, `LocalSignWithoutMinimality] do
    if (← getEnv).contains (name ++ `local_root_numbers) then
      throwError "Missing local sign evidence generated a theorem"

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [`CompatibleTamagawaRows.local_invariants_agree,
      `GoodTamagawa.tamagawa_numbers,
      `CompatibleKodairaRows.local_invariants_agree,
      `KodairaGood.kodaira_symbols, `KodairaAdditive.kodaira_symbols,
      `TrivialTorsion.torsion, `BoundedTorsion.torsion_bound,
      `IntegralJ.j_integral, `NonintegralJ.j_integral,
      `PotentialGood.potential_good_reduction, `NoPotentialGood.potential_good_reduction] do
    for ax in ← liftTermElabM <| Lean.collectAxioms theoremName do
      unless standard.contains ax do throwError "Unexpected j-invariant check axiom: {ax}"
  for name in [`Invariants37, `JSON37] do
    for rankName in [`analytic_rank, `algebraic_rank_lower_bound] do
      if (← getEnv).contains (name ++ rankName) then
        throwError "Stored arithmetic invariants generated an unsupported rank claim"
    for suffix in [`b_invariants, `c_invariants, `j_invariant, `minimal_discriminant_abs,
        `global_minimal, `dirichlet_coefficients, `bad_primes,
        `bad_reduction_primes, `num_bad_primes, `semistable, `squarefree_discriminant,
        `local_invariants] do
      for ax in ← liftTermElabM <| Lean.collectAxioms (name ++ suffix) do
        unless standard.contains ax do throwError "Unexpected invariant axiom: {ax}"
    for suffix in [`conductor, `root_number] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      unless axioms.contains ``VerifiedLcalc.Assumptions.ellipticModularity do
        throwError "Conditional arithmetic boundary was not recorded"
      for ax in axioms do
        unless standard.contains ax || ax == ``VerifiedLcalc.Assumptions.ellipticModularity do
          throwError "Unexpected conditional invariant axiom: {ax}"

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [`JSON37, `DirectConductorValuations] do
    let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ `conductor_valuation)
    let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
    unless axioms.contains modularity do throwError "Conductor exponent lost its assumption"
    for ax in axioms do
      unless standard.contains ax || ax == modularity do
        throwError "Unexpected conductor exponent axiom: {ax}"
  if (← getEnv).contains `SplitLocal.conductor_valuation then
    throwError "A row without a conductor exponent generated an exponent theorem"
  let additiveFields := [`semistable, `squarefree_discriminant, `local_invariants]
  for (name, fields) in [(`AdditiveLocal, additiveFields), (`SplitLocal, [`local_invariants])] do
    for field in fields do
      for ax in ← liftTermElabM <| Lean.collectAxioms (name ++ field) do
        unless standard.contains ax do throwError "Unexpected local invariant axiom: {ax}"

run_cmd do
  for j in ["[1,0]", "[1,-1]", "[1,2,3]", "0.5", "\"0.5\""] do
    match CurveDataJson.parse ("{\"ainvs\":[0,0,1,-1,0],\"jinv\":" ++ j ++ "}") with
    | .error _ => pure ()
    | .ok _ => throwError "Malformed exact rational accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,0,0,1],"prime":3,"kodaira_symbol":0}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Zero PARI Kodaira code accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"j_integral":"false"}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Non-boolean j_integral accepted"
  for v in ["-1", "1.5", "true"] do
    let raw := "{\"ainvs\":[0,0,1,-1,0],\"prime\":37,\"conductor_valuation\":" ++ v ++ "}"
    match CurveDataJson.parse raw with
    | .error _ => pure ()
    | .ok _ => throwError "Malformed conductor exponent accepted"
  let row := r#"{"prime":37,"conductor_valuation":1}"#
  let oversized := String.intercalate "," (List.replicate 257 row)
  let raw := "{\"ainvs\":[0,0,1,-1,0],\"local_invariants\":[" ++ oversized ++ "]}"
  match CurveDataJson.parse raw with
  | .error _ => pure ()
  | .ok _ => throwError "Oversized conductor valuation row list accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":0}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Non-boolean potential_good_reduction accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"anlist":[1,1]}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Nonzero anlist origin accepted"

certify_ec FullCyclicFamily from
  { equation := ⟨0, -1, 1, -10, -20⟩, torsion := some 5, torsionBound := some ⟨3, 5, 5⟩,
    torsionGeneratorCoordinates := some [(5, 5), (5, -6)],
    torsionGeneratorOrders := some [5, 5] }

private def fullCyclicFamily := FullCyclicFamily.certificate.torsion
private def fullCyclicPoints := fullCyclicFamily.generators.getD ⟨0, Fin.elim0⟩
private def fullCyclicPresentation := fullCyclicFamily.presentation.get (by decide +kernel)

example : fullCyclicPoints.1 = 2 := rfl
example : List.ofFn fullCyclicPresentation.factor = [5] := rfl
example : (fullCyclicPresentation.indices (0 : Fin 1)).val = 0 := rfl

example : AddSubgroup.closure (Set.range fullCyclicPoints.2) =
    AddCommGroup.torsion (FullCyclicFamily.curve.baseChange ℚ).toAffine.Point :=
  (fullCyclicFamily.generation.get (by decide +kernel)).down

certify_ec TrivialTorsionFamily from
  { equation := ⟨0, 0, 1, -1, 0⟩, torsion := some 1, torsionBound := some ⟨3, 5, 1⟩,
    torsionGeneratorCoordinates := some [] }

example : TrivialTorsionFamily.certificate.torsion.generation.isSome := by decide +kernel
example : TrivialTorsionFamily.certificate.torsion.orders.isNone := by decide +kernel
example : TrivialTorsionFamily.certificate.torsion.generators.map Sigma.fst = some 0 := rfl
example : TrivialTorsion.certificate.torsion.generators.isNone := by decide +kernel
example : TrivialTorsion.certificate.torsion.generation.isNone := by decide +kernel
example : List.ofFn (TrivialTorsion.certificate.torsion.presentation.get
    (by decide +kernel)).factor = [] := rfl

private def twoByTwo := NoncyclicTorsion.certificate.torsion.presentation.get (by decide +kernel)

example : NoncyclicTorsion.certificate.torsion.generators.map Sigma.fst = some 3 := rfl
example : NoncyclicTorsion.certificate.torsion.generation.isSome := by decide +kernel
example : List.ofFn twoByTwo.factor = [2, 2] := rfl
example : List.ofFn (fun i => (twoByTwo.indices i).val) = [0, 1] := rfl

-- Keep the contract exhaustive as the raw witness gains fields. A field can be
-- an input prerequisite, rather than a direct certified conclusion.
run_cmd do
  let equation := #[`equation, `bInvariants, `cInvariants, `discriminant]
  let rational := #[`discriminantSign, `jInvariant, `jIntegral, `abcQuality]
  let algebraic := #[`integralCoordinates, `integralFiberRoots, `numIntegralPoints,
    `generatorCoordinates, `generatorCount, `algebraicRank, `algebraicRankBounds,
    `torsionGeneratorCoordinates, `infiniteOrderPoints, `independentPoints,
    `independentGeneratorPoints, `regulator, `canonicalHeights]
  let arithmetic := #[`potentialGoodReduction, `minimalDiscriminantAbs, `conductor, `rootNumber,
    `dirichletCoefficients, `badPrimes, `numBadPrimes, `semistable,
    `squarefreeDiscriminant, `localInvariants, `primeCoefficients, `minimality, `localData,
    `tamagawaProduct]
  let analytic := #[`centralResult, `derivativeResult, `catalogueAnalyticRank,
    `specialLValue, `realPeriod, `analyticSha, `sha, `shaPrimes, `padicRegulator]
  let torsion := #[`torsionBound, `torsion, `torsionStructure, `torsionPrimes,
    `torsionGeneratorOrders, `torsionGrowthField]
  let cover (record : Name) (tracked : Array Name) : CommandElabM Unit := do
    let fields := Lean.getStructureFields (← getEnv) record
    for field in fields do
      unless tracked.contains field do
        throwError "Add the checked data/proof contract for new witness field {record}.{field}"
    for field in tracked do
      unless fields.contains field do
        throwError "Remove obsolete witness field {record}.{field} from the certificate inventory"
  let isogeny := #[`isogenyEdge, `classSize, `classDegree, `isogenyDegrees, `isogenyMatrix]
  let geometry := #[`complexMultiplication, `minimumTwistEquation, `minimumTwistDiscriminant,
    `modifiedSzpiroRatio, `area, `faltingsHeight, `stableFaltingsHeight, `faltingsRatio]
  let galois := #[`nonmaxPrimes, `nonmaxRadical, `adelicGenerators, `modPrimeImage, `modPrimeImages,
    `adelicLevel, `adelicIndex, `adelicGenus, `adelicImage]
  cover ``EllipticWitness
    (equation ++ rational ++ algebraic ++ arithmetic ++ analytic ++ torsion ++
      isogeny ++ geometry ++ galois ++ #[`lmfdbNumber, `isoNlabel, `lmfdbIso, `lmfdbLabel])
  cover ``AdelicGeneratorsClaim #[`modulus, `rows]
  cover ``IsogenyEdgeClaim #[`target, `degree, `kernelX]
  cover ``LocalReductionClaim #[`prime, `discriminantValuation, `conductorValuation,
    `jDenominatorValuation, `reductionType, `tamagawaNumber, `kodairaSymbol, `rootNumber]
  cover ``AbcQualityClaim #[`reported, `error, `factors]
  cover ``RegulatorClaim #[`reported, `error]
  cover ``PadicRegulatorClaim #[`p, `prec, `val, `unit]
  cover ``DecimalEnclosureClaim #[`reported, `error]
  cover ``TorsionBoundWitness #[`firstPrime, `secondPrime, `bound]
  cover ``TorsionGrowthFieldClaim #[`coefficients, `degree]
  cover ``CanonicalHeightsClaim #[`reported, `errors]

example : EmptyProofs.certificate.equationFacts.discriminant.isNone = true := rfl
example : JZero.certificate.equationFacts.discriminant.map Subtype.val = some (-432) := rfl

example : NonintegralJ.certificate.rational.jIntegral.map Subtype.val = some false := rfl
example : JZero.certificate.algebraic.integralYFibers = none := rfl
example : Partial37.certificate.arithmetic.minimalModel.isNone = true := rfl

example : BoundedTorsion.certificate.torsion.divisor.isSome = true := rfl
example : BoundedTorsion.certificate.torsion.divisor.map
    (fun fact => (fact.evidence.firstPrime, fact.evidence.secondPrime)) = some (3, 5) := rfl
example : BoundedTorsion.certificate.torsion.cardinality.isNone = true := rfl
example : TrivialTorsion.certificate.torsion.cardinality.map Subtype.val = some 1 := rfl


example : GoodTamagawa.certificate.arithmetic.tamagawa.map LocalTamagawaFact.value = [1] :=
  by decide +kernel

example : TamagawaOutsideScope.certificate.arithmetic.tamagawa.length = 0 := by decide +kernel

example : ((KodairaAdditive.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).kodaira.map LocalKodairaFact.index) = [none] := by decide +kernel

example : LooseTorsionBound.certificate.torsion.presentation.isNone = true := rfl
example : TrivialCyclicStructure.certificate.torsion.presentation.map
    (fun p => List.ofFn p.factor) = some [] := rfl

example : RawAbcMetadata.certificate.rational.abcQuality.isNone = true := rfl
