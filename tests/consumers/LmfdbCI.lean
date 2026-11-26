import CertifiedCurves.Json
import VerifiedLcalcTests.Fixtures.LmfdbCI

/-!
# Reuse LMFDB arithmetic certificates

Check the exported theorem types and audit their dependencies after importing the compiled fixtures.
-/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

example : LMFDB.C112a2.curve = (⟨0, 1, 0, 0, 4⟩ : WeierstrassCurve ℤ) := rfl

example : (LMFDB.C112a2.curve.baseChange ℚ).j = -4 / 7 :=
  LMFDB.C112a2.j_invariant
example : LMFDB.C112a2.curve.Δ = -7168 := LMFDB.C112a2.discriminant

example :
    |(LMFDB.C112a2.curve.baseChange ℚ).abcQuality LMFDB.C112a2.abc_quality_defined -
      (10348177494302118 / 10000000000000000 : ℝ)| ≤ (1 / 1000000000000000 : ℝ) := by
  convert LMFDB.C112a2.abc_quality using 1 <;> norm_num [LMFDB.C112a2.claimed_abc_quality]

example : (LMFDB.C179a1.curve.baseChange ℚ).j = -110592 / 179 :=
  LMFDB.C179a1.j_invariant
example : LMFDB.C179a1.curve.Δ = -179 := LMFDB.C179a1.discriminant
example : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (LMFDB.C179a1.curve.baseChange ℚ) :=
  LMFDB.C179a1.semistable.mpr rfl
example : Squarefree LMFDB.C179a1.curve.Δ.natAbs :=
  LMFDB.C179a1.squarefree_discriminant.mpr rfl
example :
    LocalReductionClaim.Spec
      { prime := 179, discriminantValuation := some 1, jDenominatorValuation := some 1,
        reductionType := some 1, kodairaSymbol := some 5, tamagawaNumber := some 1,
        rootNumber := some (-1) }
      LMFDB.C179a1.curve :=
  LMFDB.C179a1.local_invariants _ (by decide +kernel)

example :
    letI : Fact (Nat.Prime 179) := ⟨by decide +kernel⟩
    (LMFDB.C179a1.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 179) = 1 := by
  let row : LocalReductionClaim :=
    { prime := 179, discriminantValuation := some 1, jDenominatorValuation := some 1,
      reductionType := some 1, kodairaSymbol := some 5, tamagawaNumber := some 1,
      rootNumber := some (-1) }
  obtain ⟨_, h⟩ := LMFDB.C179a1.tamagawa_numbers row (by decide +kernel) 1 rfl
  exact h (by decide +kernel)

example : (LMFDB.C179a1.certificate.arithmetic.tamagawa.map fun fact =>
    ((fact.prime : ℕ), fact.value)) = [(179, 1)] := by decide +kernel

example :
    letI : Fact (Nat.Prime 179) := ⟨by decide +kernel⟩
    (LMFDB.C179a1.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 179) = 1 := by
  let facts := LMFDB.C179a1.certificate.arithmetic.tamagawa
  let first := facts[0]'(by decide +kernel)
  exact first.correct

example :
    letI : Fact (Nat.Prime 179) := ⟨by decide +kernel⟩
    (LMFDB.C179a1.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 179) = .I 1 := by
  let row : LocalReductionClaim :=
    { prime := 179, discriminantValuation := some 1, jDenominatorValuation := some 1,
      reductionType := some 1, kodairaSymbol := some 5, tamagawaNumber := some 1,
      rootNumber := some (-1) }
  obtain ⟨_, h⟩ := LMFDB.C179a1.kodaira_symbols row (by decide +kernel)
  exact h 5 rfl

example : ((LMFDB.C179a1.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).kodaira.map fun fact => ((fact.prime : ℕ), fact.index)) =
    [(179, some 1)] := by decide +kernel

example : (LMFDB.C17a2.curve : WeierstrassCurve ℤ) = ⟨1, -1, 1, -6, -4⟩ := rfl

example : (LMFDB.C17a2.certificate.arithmetic.tamagawa.map fun fact =>
    ((fact.prime : ℕ), fact.value)) = [(17, 2)] := by decide +kernel

example :
    letI : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
    (LMFDB.C17a2.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 17) = 2 := by
  exact (LMFDB.C17a2.certificate.arithmetic.tamagawa[0]'(by decide +kernel)).correct

example : (LMFDB.C49a4.certificate.arithmetic.tamagawa.map fun fact =>
    ((fact.prime : ℕ), fact.value)) = [(7, 2)] := by decide +kernel

example :
    letI : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
    (LMFDB.C49a4.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 7) = 2 := by
  let fact := LMFDB.C49a4.certificate.arithmetic.tamagawa[0]'(by decide +kernel)
  have hp : fact.prime = ⟨7, by decide +kernel⟩ := Subtype.ext (by decide +kernel)
  have hv : fact.value = 2 := by decide +kernel
  obtain ⟨prime, value, correct⟩ := fact
  change prime = _ at hp
  change value = 2 at hv
  subst prime value
  exact correct

example : (LMFDB.C112a2.certificate.arithmetic.tamagawa.map fun fact =>
    ((fact.prime : ℕ), fact.value)) = [(7, 1)] := by decide +kernel

example :
    (((LMFDB.C179a1.certificate.arithmetic.minimalModel.get
      (by decide +kernel)).localRows.get (by decide +kernel)).val.map fun row =>
        (row.kodairaSymbol, row.tamagawaNumber)) = [(none, none)] := by decide +kernel

example : (LMFDB.C197a1.curve.baseChange ℚ).j = 13824000 / 197 :=
  LMFDB.C197a1.j_invariant
example : LMFDB.C197a1.curve.Δ = 197 := LMFDB.C197a1.discriminant
example : ¬ IsLocalization.IsInteger ℤ (LMFDB.C197a1.curve.baseChange ℚ).j :=
  fun h => Bool.false_ne_true (LMFDB.C197a1.j_integral.mp h)

example :
    ¬ EllipticCurve.HasEverywherePotentialGoodReduction (LMFDB.C197a1.curve.baseChange ℚ) :=
  fun h => Bool.false_ne_true (LMFDB.C197a1.potential_good_reduction.mp h)

example : (LMFDB.C214a1.curve.baseChange ℚ).j = 357911 / 214 :=
  LMFDB.C214a1.j_invariant
example : LMFDB.C214a1.curve.Δ = -214 := LMFDB.C214a1.discriminant

example : (LMFDB.C243a1.curve.baseChange ℚ).j = 0 :=
  LMFDB.C243a1.j_invariant
example : LMFDB.C243a1.curve.Δ = -243 := LMFDB.C243a1.discriminant
example : ¬ WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (LMFDB.C243a1.curve.baseChange ℚ) :=
  fun h => by cases LMFDB.C243a1.semistable.mp h
example : ¬ Squarefree LMFDB.C243a1.curve.Δ.natAbs :=
  fun h => by cases LMFDB.C243a1.squarefree_discriminant.mp h
example :
    LocalReductionClaim.Spec
      { prime := 3, discriminantValuation := some 5, jDenominatorValuation := some 0,
        reductionType := some 0, rootNumber := some 1 } LMFDB.C243a1.curve :=
  LMFDB.C243a1.local_invariants _ (by decide +kernel)

example : (LMFDB.C254a1.curve.baseChange ℚ).j = 15438249 / 1016 :=
  LMFDB.C254a1.j_invariant
example : LMFDB.C254a1.curve.Δ = 1016 := LMFDB.C254a1.discriminant

example : (LMFDB.C275a1.curve.baseChange ℚ).j = 22930509321 / 6875 :=
  LMFDB.C275a1.j_invariant
example : LMFDB.C275a1.curve.Δ = 107421875 := LMFDB.C275a1.discriminant

example : (LMFDB.C286f1.curve.baseChange ℚ).j = -1 / 286 :=
  LMFDB.C286f1.j_invariant
example : LMFDB.C286f1.curve.Δ = -286 := LMFDB.C286f1.discriminant

example : (LMFDB.C288a1.curve.baseChange ℚ).j = 1728 :=
  LMFDB.C288a1.j_invariant
example : LMFDB.C288a1.curve.Δ = 110592 := LMFDB.C288a1.discriminant
example : IsLocalization.IsInteger ℤ (LMFDB.C288a1.curve.baseChange ℚ).j :=
  LMFDB.C288a1.j_integral.mpr rfl

example : EllipticCurve.HasEverywherePotentialGoodReduction (LMFDB.C288a1.curve.baseChange ℚ) :=
  LMFDB.C288a1.potential_good_reduction.mpr rfl

example : (LMFDB.C291d1.curve.baseChange ℚ).j = -4096 / 291 :=
  LMFDB.C291d1.j_invariant
example : LMFDB.C291d1.curve.Δ = -291 := LMFDB.C291d1.discriminant

example : LMFDB.C112a2.generators.coordinates.length = 1 :=
  LMFDB.C112a2.generators.count_valid

example : LMFDB.C112a2.integral_y_fiber ⟨0, by decide⟩ = ({0} : Finset ℤ) := by
  decide +kernel

example (y : ℤ) : y ∈ LMFDB.C112a2.integral_y_fiber ⟨0, by decide⟩ ↔
    LMFDB.C112a2.curve.toAffine.Equation (-2) y :=
  LMFDB.C112a2.integral_y_fiber_complete _ y

example : LMFDB.C112a2.integral_y_fiber ⟨2, by decide⟩ = ({2, -2} : Finset ℤ) := by
  decide +kernel

-- The double root still occupies both of its original integral-coordinate indices.
example : (LMFDB.C112a2.witness.integralCoordinates.getD [])[0]? = some (-2, 0) := by
  decide +kernel
example : (LMFDB.C112a2.witness.integralCoordinates.getD [])[1]? = some (-2, 0) := by
  decide +kernel

example : LMFDB.C112a2.curve.toAffine.Equation 0 2 :=
  LMFDB.C112a2.points_on_curve 0 2 (by decide +kernel)

example : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Equation 0 2 :=
  LMFDB.C112a2.generators.points_on_curve 0 2 (by decide +kernel)

example : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Equation (-2) 0 :=
  LMFDB.C112a2.torsion_generators.points_on_curve (-2) 0 (by decide +kernel)

example : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point :=
  LMFDB.C112a2.torsion_generators.point ⟨0, by decide⟩

example : LMFDB.C243a1.curve.toAffine.Equation 1 0 :=
  LMFDB.C243a1.points_on_curve 1 0 (by decide +kernel)

/-- The complete stored coefficient prefix begins at one after decoding the zero sentinel. -/
theorem imported_112a2_anlist :
    (List.range 20).map (fun n => (LMFDB.C112a2.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, 0, -2, 0, -4, 0, -1, 0, 1, 0, 0, 0, 0, 0, 8, 0, -2, 0, 2, 0] :=
  (LMFDB.C112a2.certificate.arithmetic.dirichletCoefficients.get (by rfl)).property

/-- Taking the first eight entries recovers the shorter coefficient prefix. -/
theorem imported_112a2_anlist_first_eight :
    (List.range 8).map (fun n => (LMFDB.C112a2.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, 0, -2, 0, -4, 0, -1, 0] := by
  have h := congrArg (List.take 8) imported_112a2_anlist
  rw [← List.map_take, List.take_range] at h
  exact h

run_cmd do
  let input ← IO.ofExcept <| Json.parse
    r#"{"ainvs":[0,1,0,0,4],"anlist":[1,1]}"#
  match CurveDataJson.decode input with
  | .ok _ => throwError "Expected rejection of a nonzero leading anlist entry"
  | .error message =>
    unless message == "LMFDB anlist must start with a_0 = 0" do
      throwError "Unexpected anlist decoding error: {message}"

private def primeCoefficients112a2 : List (ℕ × ℤ) :=
  [(2, 0), (3, -2), (5, -4), (7, -1), (11, 0), (13, 0), (17, -2), (19, 2), (23, -8), (29, 2),
    (31, -4), (37, -6), (41, -2), (43, -8), (47, 4), (53, -10), (59, -6), (61, 4), (67, 12),
    (71, 0), (73, -14), (79, 8), (83, -6), (89, 10), (97, -2)]

/-- The decoded list contains exactly the stored prime-indexed entries in their source order. -/
theorem imported_112a2_aplist_values :
    LMFDB.C112a2.certificate.arithmetic.primeCoefficients.map Subtype.val =
      some primeCoefficients112a2 := rfl

/-- Every coefficient in the stored prime-indexed list agrees with the curve's L-function. -/
theorem imported_112a2_aplist (p : ℕ) (a : ℤ) (h : (p, a) ∈ primeCoefficients112a2) :
    (LMFDB.C112a2.curve.baseChange ℚ).LFunction p = a :=
  (LMFDB.C112a2.certificate.arithmetic.primeCoefficients.get (by rfl)).property p a h

example :
    analyticOrderAt
      (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).formL
      (1 : ℂ) = 1 :=
  Curve112.analytic_rank

example : addOrderOf (LMFDB.C112a2.torsion_generators.point ⟨0, by decide⟩) = 2 :=
  LMFDB.C112a2.torsion_generators.exact_order _

/-- The stored conductor exponents agree with the level of the modular realization. -/
theorem imported_112a2_conductor_exponents (row : ℕ × ℕ)
    (h : row ∈ ([(2, 4), (7, 1)] : List (ℕ × ℕ))) :
    (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).level.factorization
      row.1 = row.2 :=
  (LMFDB.C112a2.conductor_valuation row h).2

example :
    Nat.card (AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) = 2 :=
  LMFDB.C112a2.torsion

example : ∃ e : ZMod 2 ≃+ AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point,
    (e 1 : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) =
      LMFDB.C112a2.torsion_generators.point ⟨0, by decide⟩ :=
  LMFDB.C112a2.torsion_structure.2

/-- The stored list is exactly the distinct prime support of rational torsion on 112.a2. -/
theorem imported_112a2_torsion_primes (p : ℕ) :
    p ∈ ([2] : List ℕ) ↔ p.Prime ∧
      p ∣ Nat.card (AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) := by
  let support := LMFDB.C112a2.certificate.torsion.primeSupport.get (by rfl)
  have hprimes : support.primes = [2] := by decide +kernel
  simpa only [hprimes] using support.exact_support p

/-- The complete stored torsion generator family consists of the literal point `(-2, 0)`. -/
theorem imported_112a2_torsion_generator_list :
    LMFDB.C112a2.certificate.torsion.generators.map (fun family => List.ofFn family.2) =
      some [.mk (LMFDB.C112a2.torsion_generators.points_on_curve (-2) 0
        (by decide +kernel))] := rfl

/-- The literal affine point `(-2, 0)` generates the full rational torsion subgroup. -/
theorem imported_112a2_torsion_generator :
    ∃ e : ZMod 2 ≃+ AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point,
      (e 1 : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) =
        .mk (LMFDB.C112a2.torsion_generators.points_on_curve (-2) 0 (by decide +kernel)) :=
  LMFDB.C112a2.torsion_structure.2

/-- The checked generation proof identifies the subgroup generated by the literal point. -/
theorem imported_112a2_torsion_generation :
    AddSubgroup.closure
      ({.mk (LMFDB.C112a2.torsion_generators.points_on_curve (-2) 0 (by decide +kernel))} :
        Set (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) =
      AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point := by
  have h := (LMFDB.C112a2.certificate.torsion.generation.get (by rfl)).down
  change AddSubgroup.closure (Set.range
    (fun i : Fin 1 => LMFDB.C112a2.torsion_generators.point ⟨i.val, i.isLt⟩)) = _ at h
  have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simp only [Set.range_unique, hzero] at h
  exact h

example : ¬ EllipticCurve.HasEverywherePotentialGoodReduction
    (LMFDB.C112a2.curve.baseChange ℚ) :=
  fun h => Bool.false_ne_true (LMFDB.C112a2.potential_good_reduction.mp h)

example : ¬ WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (LMFDB.C112a2.curve.baseChange ℚ) :=
  fun h => Bool.false_ne_true (LMFDB.C112a2.semistable.mp h)

example : ¬ Squarefree LMFDB.C112a2.curve.Δ.natAbs :=
  fun h => Bool.false_ne_true (LMFDB.C112a2.squarefree_discriminant.mp h)

private def localRow112a2Two : LocalReductionClaim :=
  { prime := 2, conductorValuation := some 4, discriminantValuation := some 10,
    jDenominatorValuation := some 0, reductionType := some 0, rootNumber := some 1 }

private def localRow112a2Seven : LocalReductionClaim :=
  { prime := 7, conductorValuation := some 1, discriminantValuation := some 1,
    jDenominatorValuation := some 1, reductionType := some (-1), kodairaSymbol := some 5,
    tamagawaNumber := some 1, rootNumber := some 1 }

/-- The wild row gives the supported exact discriminant, denominator, and reduction data. -/
theorem imported_112a2_local_two : localRow112a2Two.Spec LMFDB.C112a2.curve :=
  LMFDB.C112a2.local_invariants _ (by decide +kernel)

/-- The tame row gives the supported exact discriminant, denominator, and reduction data. -/
theorem imported_112a2_local_seven : localRow112a2Seven.Spec LMFDB.C112a2.curve :=
  LMFDB.C112a2.local_invariants _ (by decide +kernel)

example :
    letI : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
    (LMFDB.C112a2.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 7) = .I 1 := by
  obtain ⟨_, h⟩ := LMFDB.C112a2.kodaira_symbols localRow112a2Seven (by decide +kernel)
  exact h 5 rfl

example :
    letI : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
    (LMFDB.C112a2.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 7) = 1 := by
  let fact := LMFDB.C112a2.certificate.arithmetic.tamagawa[0]'(by decide +kernel)
  exact fact.correct

/-- The local arithmetic sign is positive at both primes of bad reduction. -/
theorem imported_112a2_local_sign (p : ℕ) [Fact p.Prime] (h : p = 2 ∨ p = 7) :
    wildLocalRootSpec LMFDB.C112a2.curve LMFDB.C112a2.localData p = 1 := by
  let signs := (LMFDB.C112a2.certificate.arithmetic.minimalModel.get (by rfl)).localRootNumbers
  rcases h with rfl | rfl
  · exact (signs[0]'(by decide +kernel)).correct
  · exact (signs[1]'(by decide +kernel)).correct

run_cmd do
  for fact in [``imported_112a2_anlist, ``imported_112a2_anlist_first_eight,
      ``imported_112a2_aplist_values, ``imported_112a2_aplist,
      ``imported_112a2_torsion_primes,
      ``imported_112a2_torsion_generator_list, ``imported_112a2_torsion_generator,
      ``imported_112a2_torsion_generation,
      ``imported_112a2_local_two, ``imported_112a2_local_seven, ``imported_112a2_local_sign] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms fact) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {fact}: {axiomName}"

private def wildLocalSign : LocalRootNumberFact LMFDB.C243a1.curve :=
  (LMFDB.C243a1.certificate.arithmetic.minimalModel.get (by decide +kernel)).localRootNumbers[0]

/-- The aggregate retains the checked wild arithmetic sign at 3. -/
theorem imported_wild_local_root_number :
    letI : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
    wildLocalRootSpec LMFDB.C243a1.curve LMFDB.C243a1.localData 3 = 1 :=
  wildLocalSign.correct

/-- The aggregate retains the checked split multiplicative sign at 179. -/
theorem imported_tame_local_root_number :
    letI : Fact (Nat.Prime 179) := ⟨by decide +kernel⟩
    wildLocalRootSpec LMFDB.C179a1.curve LMFDB.C179a1.localData 179 = -1 :=
  ((LMFDB.C179a1.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).localRootNumbers[0]).correct

run_cmd do
  let unconditional := [``propext, ``Classical.choice, ``Quot.sound]
  let modularity := ``Assumptions.ellipticModularity
  let check (curve suffix : Name) (conditional : Bool) : CommandElabM Unit := do
    let lemmaName := curve ++ suffix
    let some (.thmInfo _) := (← getEnv).find? lemmaName
      | throwError "Missing certificate theorem {lemmaName}"
    let dependencies ← liftTermElabM <| Lean.collectAxioms lemmaName
    unless dependencies.contains modularity == conditional do
      throwError "Unexpected modularity dependency for {lemmaName}"
    for axiomName in dependencies do
      unless unconditional.contains axiomName || (conditional && axiomName == modularity) do
        throwError "Unexpected dependency {axiomName} in {lemmaName}"
  check `LMFDB.C112a2 `abc_quality false
  check `LMFDB.C112a2 `integral_y_fiber_complete false
  check `LMFDB.C112a2 `generators.count_valid false
  check `LMFDB.C112a2 `generators.points_on_curve false
  check `LMFDB.C112a2 `torsion_generators.points_on_curve false
  check `LMFDB.C179a1 `tamagawa_numbers false
  check `LMFDB.C179a1 `kodaira_symbols false
  check `LMFDB.C179a1 `local_root_numbers false
  check `LMFDB.C243a1 `local_root_numbers false
  check Name.anonymous `imported_wild_local_root_number false
  check Name.anonymous `imported_tame_local_root_number false
  for axiomName in ← liftTermElabM (Lean.collectAxioms ``LMFDB.C179a1.certificate) do
    unless unconditional.contains axiomName do
      throwError "Unexpected aggregate dependency {axiomName}"
  check `LMFDB.C112a2 `torsion_generators.exact_order false
  check `LMFDB.C112a2 `torsion false
  check `LMFDB.C112a2 `torsion_structure false
  check `LMFDB.C112a2 `torsion_primes_value_valid false
  check `LMFDB.C112a2 `dirichlet_coefficients false
  check `LMFDB.C197a1 `j_integral false
  check `LMFDB.C288a1 `j_integral false
  check `LMFDB.C112a2 `conductor_valuation_value_valid false
  check `LMFDB.C112a2 `conductor_valuation true
  check `LMFDB.C197a1 `potential_good_reduction false
  check `LMFDB.C288a1 `potential_good_reduction false
  check `Curve112 `analytic_rank true
  for curve in [`LMFDB.C179a1, `LMFDB.C243a1] do
    for suffix in [`semistable, `squarefree_discriminant, `local_invariants] do
      check curve suffix false
  for curve in [`LMFDB.C112a2, `LMFDB.C179a1, `LMFDB.C197a1, `LMFDB.C214a1, `LMFDB.C243a1,
      `LMFDB.C254a1, `LMFDB.C275a1, `LMFDB.C286f1, `LMFDB.C288a1, `LMFDB.C291d1] do
    for suffix in [`j_invariant, `discriminant, `discriminant_sign, `minimal_discriminant_abs,
        `global_minimal, `bad_primes, `bad_reduction_primes, `num_bad_primes, `points_on_curve] do
      check curve suffix false
    check curve `conductor true
    check curve `root_number true
    for suffix in [`analytic_rank, `algebraic_rank_lower_bound] do
      if (← getEnv).contains (curve ++ suffix) then
        throwError "Unexpected rank declaration for {curve}"

private def importedCentral :=
  Curve11.certificate.analytic.central.get (by decide +kernel)

/-- The numerical payload remains independently certified on a mixed certificate. -/
theorem imported_aggregate_central_payload :
    EllipticCurve.CentralPayloadCorrect importedCentral.result :=
  importedCentral.payload

/-- The checked rank applies to a supplied arithmetic modular realization. -/
theorem imported_aggregate_rank
    (model : Modularity.ArithmeticModularRealization Curve11.curve) :
    analyticOrderAt model.formL 1 = 0 :=
  (Curve11.certificate.analytic.rank.get (by decide +kernel)).correct model

/-- Actual central containment, instantiated at an explicit realization. -/
theorem imported_aggregate_central_enclosure
    (model : Modularity.ArithmeticModularRealization Curve11.curve) :
    Curve11.result.box.Contains (Complex.ofReal (model.formL 1).re) :=
  (importedCentral.enclosure.get (by decide +kernel)).contains model

/-- Actual scaled first-derivative containment for the explicit realization. -/
theorem imported_aggregate_derivative_enclosure
    (model : Modularity.ArithmeticModularRealization Curve37.curve) :
    Curve37.result.realDerivativeBounds.Contains (deriv model.formL 1).re :=
  (((Curve37.certificate.analytic.derivative.get (by decide +kernel)).enclosure).get
    (by decide +kernel)).contains model

/-- The compiled certificate gives all integral solutions over the indexed seed's x-coordinate. -/
theorem imported_aggregate_integral_y_fiber (y : ℤ) :
    y ∈ (LMFDB.C112a2.certificate.algebraic.integralYFibers.get
      (by decide +kernel)).fiber ⟨0, by decide⟩ ↔
      LMFDB.C112a2.curve.toAffine.Equation (-2) y :=
  (LMFDB.C112a2.certificate.algebraic.integralYFibers.get
    (by decide +kernel)).complete _ y

run_cmd do
  let modularity := ``Assumptions.ellipticModularity
  let legacyAxioms ← liftTermElabM <| Lean.collectAxioms ``Curve11.analytic_rank
  unless legacyAxioms.contains modularity do
    throwError "Expected the legacy rank to use the authorized assumption"
  for fact in [``imported_aggregate_central_payload, ``imported_aggregate_rank,
      ``imported_aggregate_central_enclosure, ``imported_aggregate_derivative_enclosure,
      ``imported_aggregate_integral_y_fiber] do
    let axioms ← liftTermElabM <| Lean.collectAxioms fact
    for name in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Unexpected aggregate axiom in {fact}: {name}"

example : LMFDB.C112a2.certificate.algebraic.generators.map
    (fun family => List.ofFn family.2) =
    some [LMFDB.C112a2.generators.point ⟨0, by decide +kernel⟩] := rfl

example : LMFDB.C112a2.certificate.torsion.orders.map
    (fun orders => List.ofFn (fun i => ((orders i).val : ℕ))) = some [2] := rfl

private def checkedCyclic :=
  LMFDB.C112a2.certificate.torsion.presentation.get (by decide +kernel)

example : List.ofFn checkedCyclic.factor = [2] := rfl

/-- The compiled presentation sends the standard generator to the submitted point. -/
theorem imported_cyclic_torsion_structure :
    ∃ e : (∀ _ : Fin 1, ZMod 2) ≃+
        AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point,
      (e (Pi.single (0 : Fin 1) 1) : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) =
        LMFDB.C112a2.torsion_generators.point ⟨0, by decide⟩ := by
  obtain ⟨e, maps⟩ := checkedCyclic.realization
  exact ⟨e, maps (0 : Fin 1)⟩

run_cmd do
  for axiomName in ← liftTermElabM (Lean.collectAxioms ``imported_cyclic_torsion_structure) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected aggregate axiom: {axiomName}"

private def checkedAbcQuality :=
  LMFDB.C112a2.certificate.rational.abcQuality.get (by decide +kernel)

/-- The compiled aggregate bounds the actual abc quality. -/
theorem imported_abc_quality_bound :
    |(LMFDB.C112a2.curve.baseChange ℚ).abcQuality checkedAbcQuality.defined -
      (checkedAbcQuality.claim.reported : ℝ)| ≤ (checkedAbcQuality.claim.error : ℝ) :=
  checkedAbcQuality.within_error

run_cmd do
  for axiomName in ← liftTermElabM (Lean.collectAxioms ``imported_abc_quality_bound) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected aggregate axiom: {axiomName}"
