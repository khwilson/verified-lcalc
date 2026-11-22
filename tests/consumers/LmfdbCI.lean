import CertifiedCurves.Json
import VerifiedLcalcTests.Fixtures.LmfdbCI

/-!
# Reuse LMFDB arithmetic certificates

Check the exported theorem types and audit their dependencies after importing the compiled fixtures.
-/

open Lean Elab Command VerifiedLcalc

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
        reductionType := some 1 } LMFDB.C179a1.curve :=
  LMFDB.C179a1.local_invariants _ (by decide +kernel)

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
        reductionType := some 0 } LMFDB.C243a1.curve :=
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

example :
    (List.range 8).map (fun n => (LMFDB.C112a2.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, 0, -2, 0, -4, 0, -1, 0] :=
  LMFDB.C112a2.dirichlet_coefficients

example :
    analyticOrderAt
      (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).formL
      (1 : ℂ) = 1 :=
  Curve112.analytic_rank

example :
    (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).level.factorization 2 =
      4 :=
  (LMFDB.C112a2.conductor_valuation (2, 4) (by decide +kernel)).2

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
  check `LMFDB.C112a2 `generators.points_on_curve false
  check `LMFDB.C112a2 `torsion_generators.points_on_curve false
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
