/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Certificate.FieldCatalogue
import VerifiedLcalc.Tactic.CertifyEC
import Lean

/-! Validate the catalogue against the displayed LMFDB schemas and compiled declarations. -/

open Lean Elab Command VerifiedLcalc.FieldCatalogue

-- From https://www.lmfdb.org/EllipticCurve/Q/data/37.a1, excluding row identifiers.
-- The schema displays columns even when the corresponding example row omits them.
private def displayedSchema : List (String × List String) :=
  [("ec_curvedata",
    ("Ciso Clabel Cnumber abc_quality absD adelic_genus adelic_index adelic_level ainvs " ++
      "analytic_rank bad_primes class_deg class_size cm conductor degree elladic_images " ++
      "faltings_height faltings_index faltings_ratio " ++
      "intrinsic_torsion iso_nlabel isogeny_degrees " ++
      "jinv lmfdb_iso lmfdb_label lmfdb_number manin_constant min_quad_twist_ainvs " ++
      "min_quad_twist_disc modell_images modm_images nonmax_primes nonmax_rad num_bad_primes " ++
      "num_int_pts optimality potential_good_reduction rank " ++
      "regulator semistable serre_invariants " ++
      "sha sha_primes signD squarefree_disc " ++
      "stable_faltings_height szpiro_ratio torsion torsion_primes " ++
      "torsion_structure").splitOn " "),
   ("ec_classdata",
    "anlist aplist class_deg class_size conductor isogeny_matrix lmfdb_iso trace_hash".splitOn " "),
   ("ec_mwbsd", ("area conductor gens heights lmfdb_label ngens rank_bounds real_period sha_an " ++
      "special_value tamagawa_product torsion_generators xcoord_integral_points").splitOn " "),
   ("ec_localdata", ("conductor conductor_valuation " ++
      "discriminant_valuation j_denominator_valuation " ++
      "kodaira_symbol lmfdb_label prime reduction_type root_number tamagawa_number").splitOn " "),
   ("ec_galrep",
    "adelic_gens adelic_image conductor elladic_image lmfdb_label modell_image prime".splitOn " "),
   ("ec_padic", "lmfdb_iso p prec unit val".splitOn " "),
   ("ec_torsion_growth", "degree field lmfdb_label torsion".splitOn " "),
   ("ec_iwasawa", "iwdata iwp0 lmfdb_label".splitOn " ")]

run_cmd do
  let expected := displayedSchema.flatMap fun (table, fields) => fields.map (table, ·)
  let actual := columns.map fun col => (col.table, col.field)
  let missing := expected.filter fun entry => !actual.contains entry
  let unexpected := actual.filter fun entry => !expected.contains entry
  unless missing.isEmpty && unexpected.isEmpty && actual.length == 101 &&
      (actual.map Prod.snd).eraseDups.length == 85 do
    throwError (m!"LMFDB schema mismatch ({actual.length} columns), " ++
      m!"missing {repr missing}, unexpected {repr unexpected}")
  let env ← getEnv
  let resolve (location : String) (path : Path) : CommandElabM Unit := do
    if path.scope.isEmpty then throwError "{location} has no documented scope"
    for decl in path.claim ++ path.verify.toList ++ path.output ++ path.prerequisites do
      unless env.contains decl do
        throwError "{location} refers to missing Lean declaration {decl}"
  for path in extensions do
    resolve s!"Project input {path.json}" path
  for column in columns do
    let location := s!"{column.table}.{column.field}"
    if column.paths.isEmpty then throwError "{location} has no path"
    for path in column.paths do
      unless path.json.getLast? == some column.field do
        throwError "{location} routes to a different stored source: {path.json}"
      resolve location path
    if (column.table, column.field) == ("ec_torsion_growth", "torsion") then
      unless column.paths.all (fun path =>
          path.verify.isNone && path.check.isNone && path.output.isEmpty) do
        throwError "{location} must record the missing extension torsion checker"
    else
      unless column.paths.any (fun path => path.verify.isSome && !path.output.isEmpty) do
        throwError "{location} must specify a verifier and its checked output"

-- The same database column name can be the input to different mathematical checks.
run_cmd do
  let requirePath (table field : String) (json : List String) : CommandElabM Path := do
    let some column := columns.find? (fun col => col.table == table && col.field == field)
      | throwError "Missing {table}.{field}"
    let some path := column.paths.find? (fun path => path.json == json)
      | throwError "Missing {json} input for {table}.{field}"
    pure path
  let degree ← requirePath "ec_curvedata" "degree" ["degree"]
  let extensionDegree ← requirePath "ec_torsion_growth" "degree" ["torsion_growth", "degree"]
  unless degree.claim.contains ``VerifiedLcalc.EllipticWitness.modularDegree &&
      degree.output.contains ``VerifiedLcalc.CertifiedModularParametrization.degree &&
      degree.check == some `modular_degree do
    throwError "Curve degree must describe the checked minimum modular degree"
  unless extensionDegree.claim.contains ``VerifiedLcalc.TorsionGrowthFieldClaim.degree &&
      extensionDegree.output.contains ``VerifiedLcalc.EllipticCertificate.torsionGrowthField &&
      extensionDegree.check == some `torsion_growth_degree_matches do
    throwError "Extension degree must describe the checked field of strict torsion growth"
  let torsion ← requirePath "ec_curvedata" "torsion" ["torsion"]
  let _ ← requirePath "ec_torsion_growth" "torsion" ["torsion_growth", "torsion"]
  unless torsion.claim.contains ``VerifiedLcalc.EllipticWitness.torsion &&
      torsion.output.contains ``VerifiedLcalc.EllipticCertificate.torsion &&
      torsion.check == some `torsion do
    throwError "Curve torsion must describe rational torsion"
  let rank ← requirePath "ec_curvedata" "analytic_rank" ["analytic_rank"]
  unless rank.claim.contains ``VerifiedLcalc.EllipticWitness.catalogueAnalyticRank &&
      rank.output.contains ``VerifiedLcalc.ConditionalAnalyticRank.correct &&
      rank.check == some `catalogue_analytic_rank do
    throwError "The stored analytic rank must use the conditional rank comparison"

-- Project JSON aliases are tracked separately from the stored-column count.
run_cmd do
  let aliases : List (String × Name) :=
    [("ap", ``VerifiedLcalc.EllipticWitness.primeCoefficients),
     ("algebraic_rank", ``VerifiedLcalc.EllipticWitness.algebraicRank),
     ("global_root_number", ``VerifiedLcalc.EllipticWitness.rootNumber)]
  for (key, projection) in aliases do
    unless extensions.any (fun path => path.json == [key] && path.claim.contains projection) do
      throwError "Project JSON alias {key} must retain its typed claim"

-- Repeated table routes may share a decoder or an assembly declaration. Every
-- participating route must agree with the lookup, regardless of table order.
run_cmd do
  let native := columns.flatMap (·.paths)
  let witnessField (projection : Name) : Option Name :=
    match projection with
    | .str parent field =>
      if parent == ``VerifiedLcalc.EllipticWitness then some (.mkSimple field) else none
    | _ => none
  for path in native do
    if let ([projection], [key]) := (path.claim, path.json) then
      if let some field := witnessField projection then
        unless sourceKey field == some key do
          throwError "Conflicting native source for {projection}: {key}"
  for path in native ++ extensions do
    if let some fact := path.fact then
      let some field := path.claim.head?.bind witnessField
        | throwError "Shared assembly fact {fact} has no witness field"
      unless outputFact field == some fact do
        throwError "Conflicting assembly declaration for {field}: {fact}"
  unless sourceKey `modularDegree == some "degree" && (sourceKey `torsionGrowthField).isNone &&
      outputFact `modularDegree == some `modular_parametrization_fact &&
      outputFact `torsionGrowthField == some `torsion_growth_field_fact do
    throwError "Curve degree and extension degree must keep separate decoder and assembly routes"
  unless sourceKey `primeCoefficients == some "aplist" &&
      sourceKey `algebraicRank == some "rank" do
    throwError "Project aliases must not replace the native source keys"
  unless outputFact `sha == some `rounded_analytic_sha_fact &&
      outputFact `shaPrimes == outputFact `sha do
    throwError "The rounded analytic quotient and its prime support share a checked output"

-- These slots construct indexed records from several checked declarations.
-- Every other aggregate slot needs a direct catalogue route to a checked fact.
run_cmd do
  let owner := ``VerifiedLcalc.EllipticCertificate
  let specialized := #[`nonsingular, `equationFacts, `rational, `algebraic, `arithmetic,
    `analytic, `torsion, `isogeny, `isogenyClass, `lmfdbCatalogue]
  let fields := Lean.getStructureFields (← getEnv) owner
  let mut direct : NameMap Name := {}
  for path in columns.flatMap (·.paths) ++ extensions do
    if let (some (.str parent field), some fact) := (path.output.head?, path.fact) then
      let slot := Name.mkSimple field
      if parent == owner && !specialized.contains slot then
        unless fields.contains slot do
          throwError "Direct certificate slot {slot} is not a record field"
        if let some previous := direct.find? slot then
          unless fact == previous do
            throwError "Conflicting direct facts for {slot}: {previous} and {fact}"
        direct := direct.insert slot fact
  for slot in specialized do
    unless fields.contains slot do
      throwError "Specialized certificate slot {slot} is no longer a field"
  for slot in fields do
    unless specialized.contains slot || (direct.find? slot).isSome do
      throwError "Certificate slot {slot} has no direct or specialized assembly route"
  unless direct.find? `realPeriod == some `real_period_fact &&
      direct.find? `tamagawaProduct == some `tamagawa_product_fact do
    throwError "Real period and Tamagawa product need separate top-level certificate outputs"
