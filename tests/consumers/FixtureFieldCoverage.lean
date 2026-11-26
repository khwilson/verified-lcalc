/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import CertifiedCurves.Json
import VerifiedLcalc.Certificate.FieldCatalogue
import VerifiedLcalcTests.Fixtures.LmfdbCI
import Lean

/-! # Table-qualified evidence from imported LMFDB fixtures

The named propositions pin the represented curve and the statement actually
proved. The report joins these examples to the production field catalogue.
-/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

namespace FixtureFieldCoverage

theorem equation179 :
    LMFDB.C179a1.curve = (⟨0, 0, 1, -1, -1⟩ : WeierstrassCurve ℤ) ∧
      LMFDB.C179a1.curve.Δ ≠ 0 :=
  ⟨rfl, LMFDB.C179a1.nonsingular⟩

theorem j179 : (LMFDB.C179a1.curve.baseChange ℚ).j = -110592 / 179 :=
  LMFDB.C179a1.j_invariant

theorem minDiscriminant179 :
    WeierstrassCurve.IsGlobalMinimal (NumberField.RingOfIntegers ℚ)
      (LMFDB.C179a1.curve.baseChange ℚ) ∧ LMFDB.C179a1.curve.Δ.natAbs = 179 :=
  LMFDB.C179a1.minimal_discriminant_abs

theorem discriminantSign179 : LMFDB.C179a1.curve.Δ.sign = -1 :=
  LMFDB.C179a1.discriminant_sign

theorem badPrimes179 (p : ℕ) [Fact p.Prime] :
    p ∈ [179] ↔ ¬ (LMFDB.C179a1.curve.baseChange (ZMod p)).IsElliptic :=
  LMFDB.C179a1.bad_reduction_primes p

theorem badPrimeCount179 : LMFDB.C179a1.curve.Δ.natAbs.primeFactors.card = 1 :=
  LMFDB.C179a1.num_bad_primes

theorem semistable179 : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (LMFDB.C179a1.curve.baseChange ℚ) :=
  LMFDB.C179a1.semistable.mpr rfl

theorem squarefree179 : Squarefree LMFDB.C179a1.curve.Δ.natAbs :=
  LMFDB.C179a1.squarefree_discriminant.mpr rfl

private def row179 : LocalReductionClaim :=
  { prime := 179, discriminantValuation := some 1, jDenominatorValuation := some 1,
    reductionType := some 1, kodairaSymbol := some 5, tamagawaNumber := some 1,
    rootNumber := some (-1) }

theorem reduction179 :
    LocalReductionClaim.Spec
      { prime := 179, discriminantValuation := some 1, jDenominatorValuation := some 1,
        reductionType := some 1, kodairaSymbol := some 5, tamagawaNumber := some 1,
        rootNumber := some (-1) }
      LMFDB.C179a1.curve :=
  LMFDB.C179a1.local_invariants _ (by decide +kernel)

theorem localPrime179 : Nat.Prime 179 := by
  obtain ⟨hp, _⟩ := reduction179
  exact hp

theorem discriminantValuation179 : LMFDB.C179a1.curve.Δ.natAbs.factorization 179 = 1 := by
  obtain ⟨_, _, h, _, _⟩ := reduction179
  exact h 1 rfl

theorem jDenominatorValuation179 :
    (LMFDB.C179a1.curve.baseChange ℚ).j.den.factorization 179 = 1 := by
  obtain ⟨_, _, _, h, _⟩ := reduction179
  exact h 1 rfl

theorem tamagawa179 :
    letI : Fact (Nat.Prime 179) := ⟨localPrime179⟩
    (LMFDB.C179a1.curve.baseChange ℚ).tamagawaNumberAt (rationalPlace 179) = 1 := by
  let facts := LMFDB.C179a1.certificate.arithmetic.tamagawa
  let first := facts[0]'(by decide +kernel)
  exact first.correct

theorem kodaira179 :
    letI : Fact (Nat.Prime 179) := ⟨localPrime179⟩
    (LMFDB.C179a1.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 179) = .I 1 := by
  obtain ⟨_, h⟩ := LMFDB.C179a1.kodaira_symbols row179 (by decide +kernel)
  exact h 5 rfl

theorem rootNumber179 :
    letI : Fact (Nat.Prime 179) := ⟨localPrime179⟩
    wildLocalRootSpec LMFDB.C179a1.curve LMFDB.C179a1.localData 179 = -1 :=
  ((LMFDB.C179a1.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).localRootNumbers[0]).correct

theorem conductor112 :
    (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).level = 112 :=
  LMFDB.C112a2.conductor

theorem conductorValuation112 :
    (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).level.factorization 2 =
      4 :=
  (LMFDB.C112a2.conductor_valuation (2, 4) (by decide +kernel)).2

theorem dirichlet112 :
    (List.range 8).map (fun n => (LMFDB.C112a2.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, 0, -2, 0, -4, 0, -1, 0] :=
  LMFDB.C112a2.dirichlet_coefficients

theorem abcQuality112 :
    |(LMFDB.C112a2.curve.baseChange ℚ).abcQuality LMFDB.C112a2.abc_quality_defined -
      (10348177494302118 / 10000000000000000 : ℝ)| ≤ (1 / 1000000000000000 : ℝ) := by
  convert LMFDB.C112a2.abc_quality using 1 <;> norm_num [LMFDB.C112a2.claimed_abc_quality]

theorem generator112 : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Equation 0 2 :=
  LMFDB.C112a2.generators.points_on_curve 0 2 (by decide +kernel)

theorem generatorCount112 : LMFDB.C112a2.generators.coordinates.length = 1 :=
  LMFDB.C112a2.generators.count_valid

theorem torsionGenerator112 : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Equation (-2) 0 :=
  LMFDB.C112a2.torsion_generators.points_on_curve (-2) 0 (by decide +kernel)

theorem torsion112 :
    Nat.card (AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) = 2 :=
  LMFDB.C112a2.torsion

theorem torsionStructure112 :
    ∃ e : ZMod 2 ≃+ AddCommGroup.torsion (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point,
      (e 1 : (LMFDB.C112a2.curve.baseChange ℚ).toAffine.Point) =
        LMFDB.C112a2.torsion_generators.point ⟨0, by decide⟩ :=
  LMFDB.C112a2.torsion_structure.2

theorem integralFiber112 (y : ℤ) :
    y ∈ LMFDB.C112a2.integral_y_fiber ⟨0, by decide⟩ ↔
      LMFDB.C112a2.curve.toAffine.Equation (-2) y :=
  LMFDB.C112a2.integral_y_fiber_complete _ y

theorem rank112 :
    analyticOrderAt
      (Modularity.modularWitness LMFDB.C112a2.curve LMFDB.C112a2.nonsingular).formL
      (1 : ℂ) = 1 :=
  Curve112.analytic_rank

theorem rank37 (model : Modularity.ArithmeticModularRealization Curve37.curve) :
    analyticOrderAt model.formL 1 = 1 :=
  Curve37.catalogue_analytic_rank model

private inductive ProofKind
  | unconditional
  | modularity
  | conditional
  deriving BEq

private def ProofKind.status : ProofKind → String
  | .unconditional => "unconditional"
  | .modularity => "assumption_backed"
  | .conditional => "conditional_fixture"

private structure Sample where
  table : String
  field : String
  curve : String
  proof : Name
  scope : String
  kind : ProofKind
  partial : Bool

private def samples : List Sample :=
  [⟨"ec_curvedata", "ainvs", "179.a1", ``equation179, "Integral equation and nonsingularity.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "jinv", "179.a1", ``j179, "Exact rational j-invariant.", .unconditional, false⟩,
   ⟨"ec_curvedata", "absD", "179.a1", ``minDiscriminant179, "Global minimality and absolute discriminant.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "signD", "179.a1", ``discriminantSign179, "Exact discriminant sign.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "bad_primes", "179.a1", ``badPrimes179, "Complete bad prime support.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "num_bad_primes", "179.a1", ``badPrimeCount179, "Number of distinct bad primes.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "semistable", "179.a1", ``semistable179, "Semistable at every finite prime.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "squarefree_disc", "179.a1", ``squarefree179, "Squarefree absolute discriminant.",
      .unconditional, false⟩,
   ⟨"ec_localdata", "prime", "179.a1", ``localPrime179, "Primality of the checked local row.",
      .unconditional, false⟩,
   ⟨"ec_localdata", "discriminant_valuation", "179.a1", ``discriminantValuation179,
      "Discriminant valuation of the checked minimal equation at 179.", .unconditional, false⟩,
   ⟨"ec_localdata", "j_denominator_valuation", "179.a1", ``jDenominatorValuation179,
      "Valuation of the denominator of j at 179.", .unconditional, false⟩,
   ⟨"ec_localdata", "reduction_type", "179.a1", ``reduction179,
      "Code 1 gives split multiplicative reduction and the corresponding trace.",
      .unconditional, false⟩,
   ⟨"ec_localdata", "tamagawa_number", "179.a1", ``tamagawa179, "Intrinsic local factor at 179.",
      .unconditional, false⟩,
   ⟨"ec_localdata", "kodaira_symbol", "179.a1", ``kodaira179, "Exact I₁ symbol at 179.",
      .unconditional, false⟩,
   ⟨"ec_localdata", "root_number", "179.a1", ``rootNumber179,
      "Exact local arithmetic formula at 179.",
      .unconditional, true⟩,
   ⟨"ec_curvedata", "conductor", "112.a2", ``conductor112, "Level of the modular realization.",
      .modularity, false⟩,
   ⟨"ec_localdata", "conductor_valuation", "112.a2", ``conductorValuation112,
      "Exponent of 2 in the level of the modular realization.", .modularity, false⟩,
   ⟨"ec_classdata", "anlist", "112.a2", ``dirichlet112, "Coefficients a₁ through a₈, after a₀.",
      .unconditional, true⟩,
   ⟨"ec_curvedata", "abc_quality", "112.a2", ``abcQuality112,
      "Absolute error enclosure for the specified decimal.", .unconditional, false⟩,
   ⟨"ec_mwbsd", "gens", "112.a2", ``generator112, "Membership of the supplied point.",
      .unconditional, true⟩,
   ⟨"ec_mwbsd", "ngens", "112.a2", ``generatorCount112, "Length of the checked point list.",
      .unconditional, false⟩,
   ⟨"ec_mwbsd", "torsion_generators", "112.a2", ``torsionGenerator112, "Membership of the supplied point.",
      .unconditional, true⟩,
   ⟨"ec_curvedata", "torsion", "112.a2", ``torsion112, "Exact rational torsion cardinality.",
      .unconditional, false⟩,
   ⟨"ec_curvedata", "torsion_structure", "112.a2", ``torsionStructure112,
      "Full rational cyclic group with the submitted generator.", .unconditional, false⟩,
   ⟨"ec_mwbsd", "xcoord_integral_points", "112.a2", ``integralFiber112,
      "Complete integral fiber at x = -2.", .unconditional, true⟩,
   ⟨"ec_curvedata", "analytic_rank", "112.a2", ``rank112, "Exact order at 1 of the modular realization.",
      .modularity, false⟩,
   ⟨"ec_curvedata", "analytic_rank", "37.a1", ``rank37,
      "Exact order at 1 for an explicitly supplied ArithmeticModularRealization.", .conditional, false⟩]

private def auditSample (sample : Sample) : CommandElabM Json := do
  let some (.thmInfo _) := (← getEnv).find? sample.proof
    | throwError "Fixture sample must name a theorem: {sample.proof}"
  let axioms ← liftTermElabM <| Lean.collectAxioms sample.proof
  let dependencies := axioms.filter fun axiomName =>
    ![``propext, ``Classical.choice, ``Quot.sound].contains axiomName
  let expected := if sample.kind == .modularity then [``Assumptions.ellipticModularity] else []
  unless dependencies.toList == expected do
    throwError "Unexpected axioms for {sample.proof}: {dependencies}"
  let source := if sample.field == "analytic_rank" then
      s!"data/witnesses/{if sample.curve == "37.a1" then "37a1" else "112a2"}.json"
    else s!"tests/fixtures/lmfdb/{sample.curve}.json"
  let origin := if sample.field == "squarefree_disc" then "computed_from_equation"
    else if sample.field == "analytic_rank" then "certified_numerical_witness"
    else "fixture_claim"
  return Json.mkObj [
    ("curve", toJson sample.curve), ("theorem", toJson sample.proof.toString),
    ("status", toJson sample.kind.status), ("scope", toJson sample.scope),
    ("source", toJson source), ("value_origin", toJson origin),
    ("extent", toJson (if sample.partial then "partial" else "complete_for_sample")),
    ("project_axioms", toJson (expected.map Name.toString))]

run_cmd do
  let columns := FieldCatalogue.columns
  let names := (columns.map (·.field)).eraseDups
  unless columns.length == 101 && names.length == 85 &&
      ((columns.map fun col => (col.table, col.field)).eraseDups.length == columns.length) do
    throwError "Fixture report schema denominator changed"
  for sample in samples do
    unless columns.any (fun col => col.table == sample.table && col.field == sample.field &&
        col.paths.any (·.verify.isSome)) do
      throwError "Fixture sample does not match a checked catalogue field: {sample.table}.{sample.field}"
  unless (samples.map (·.proof)).eraseDups.length == samples.length do
    throwError "Duplicate proof in fixture report samples"
  let fields ← columns.mapM fun column => do
    let matching := samples.filter (fun sample => sample.table == column.table &&
      sample.field == column.field)
    let evidence ← matching.mapM auditSample
    let reports := (column.paths.filter (·.verify.isNone)).map (·.scope) |>.eraseDups
    let checkerScopes := (column.paths.filter (·.verify.isSome)).map (·.scope) |>.eraseDups
    let status := if !evidence.isEmpty then "sampled" else if !checkerScopes.isEmpty then "pending_review"
      else "missing_checker"
    let metadata := if column.field == "lmfdb_label" || column.field == "lmfdb_iso" then
      ["Fixture/source identifiers serve as provenance until tied to a checked catalogue ordering."]
      else []
    return Json.mkObj [
      ("table", toJson column.table), ("field", toJson column.field), ("status", toJson status),
      ("evidence", toJson evidence), ("checker_scopes", toJson checkerScopes),
      ("report_only_scopes", toJson reports),
      ("metadata_scopes", toJson metadata)]
  if (← IO.getEnv "VERIFIED_LCALC_FIXTURE_COVERAGE") == some "1" then
    IO.println (Json.mkObj [
      ("schema", toJson "lcalc.fixture-field-coverage.v1"),
      ("table_qualified_fields", toJson columns.length), ("distinct_names", toJson names.length),
      ("fields", toJson fields)]).compress

end FixtureFieldCoverage
