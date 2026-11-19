import VerifiedLcalc.BatchIO
open Lean

private def derivativeTarget (name : String) : IO String := do
  let source ← IO.FS.readFile (name.replace "." "/" ++ ".lean")
  let prefixText := "public import VerifiedLcalc.Certificates.DerivativeBatch.Bundles."
  let lines := (source.splitOn "\n").filter (·.startsWith prefixText)
  if lines.length != 1 then throw (IO.userError "Missing/ambiguous derivative proof bundle")
  let target := (lines[0]!.drop "public import ".length).toString
  if !(target.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then
    throw (IO.userError "Invalid derivative proof target")
  return target

def installDerivativeRegistry (rows : List BatchRow) : IO Bool := do
  let core : System.FilePath := "VerifiedLcalc/Regression/GeneratedRankOne.lean"
  let proof : System.FilePath := "VerifiedLcalc/Assumptions/GeneratedRankOne.lean"
  let beforeCore ← IO.FS.readFile core
  let beforeProof ← IO.FS.readFile proof
  let keys := String.intercalate ",\n  " (rows.map fun r => s!"({r.equation}, {r.conductor})")
  IO.FS.writeFile core ("module\npublic import VerifiedLcalc.Certificate\n@[expose] public section\nnamespace VerifiedLcalc.Regression\ndef generatedRankOneKeys : List (Artifacts.CurveEquation × Nat) := [\n  " ++ keys ++ "]\nend VerifiedLcalc.Regression\n")
  let mut targets : List String := []
  for r in rows do targets := targets ++ [← derivativeTarget r.moduleName]
  let imports := String.join (targets.eraseDups.map fun name => "public import " ++ name ++ "\n")
  let mut body := "module\npublic import VerifiedLcalc.Regression.GeneratedRankOne\npublic import VerifiedLcalc.Assumptions.Modularity\n" ++ imports ++
    "@[expose] public section\nnamespace VerifiedLcalc.Assumptions\nopen EllipticCurve Regression\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nset_option pp.fullNames true\n" ++
    "private def OneSound (k : Artifacts.CurveEquation × Nat) : Prop :=\n  ∃ hn : discriminant k.1 ≠ 0, analyticOrderAt (modularWitness k.1 hn).formL (1 : ℂ) = 1\n" ++
    "private theorem allOneSound : ∀ k ∈ generatedRankOneKeys, OneSound k := by\n  unfold generatedRankOneKeys\n  exact\n"
  for r in rows do
    body := body ++ "    (List.forall_mem_cons (p := OneSound)).mpr ⟨⟨" ++ r.moduleName ++ ".nonsingular, " ++ r.moduleName ++ ".analytic_rank_one⟩,\n"
  body := body ++ "    List.forall_mem_nil _" ++ String.ofList (List.replicate rows.length '⟩') ++ "\n" ++
    "theorem generatedRankOneKeys_sound (e : Artifacts.CurveEquation) (N : Nat) (h : (e,N) ∈ generatedRankOneKeys) :\n  ∃ hn : discriminant e ≠ 0, analyticOrderAt (modularWitness e hn).formL (1 : ℂ) = 1 := allOneSound (e,N) h\n" ++
    "/-- info: 'VerifiedLcalc.Assumptions.generatedRankOneKeys_sound' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/\n" ++
    "#guard_msgs (whitespace := lax) in\n#print axioms generatedRankOneKeys_sound\nend VerifiedLcalc.Assumptions\n"
  IO.FS.writeFile proof body
  let code ← runLogged #["lake","build","VerifiedLcalc.Assumptions.Regression"] "output/derivative/registry.log"
  if code != 0 then
    IO.FS.writeFile core beforeCore
    IO.FS.writeFile proof beforeProof
    let restored ← runLogged #["lake","build","VerifiedLcalc.Assumptions.Regression"] "output/derivative/rollback.log"
    IO.eprintln (if restored == 0 then "Rank-one registry rejected; checked sources and artifacts restored."
      else "Rank-one registry rejected; sources restored but dependency rebuild failed.")
    return false
  return true

private def validateSubject (r : BatchRow) : IO Unit := do
  let some c := VerifiedLcalc.Lmfdb.allCases.find? (fun c => c.input.label == r.label)
    | throw (IO.userError "Derivative subject absent from fixture")
  if r.conductor != toString c.input.conductor || r.equation != (reprStr c.input.equation).replace "\n" " " then
    throw (IO.userError "Derivative subject differs from fixture")
  if r.moduleName != "VerifiedLcalc.Certificates.DerivativeBatch.C" ++ r.label.replace "." "_" then
    throw (IO.userError "Derivative proof namespace differs from label")

private def finish (rows : List BatchRow) (elapsed : Nat) : IO UInt32 := do
  let finishStart ← IO.monoMsNow
  let verified := rows.filter (fun r => r.status == "verified-conditional-rank-one")
  let installed ← installDerivativeRegistry verified
  if installed then
    let mut bundles : List String := []
    for r in verified do bundles := bundles ++ [← derivativeTarget r.moduleName]
    let mut hashes := ""
    for target in bundles.eraseDups do
      let hash ← IO.Process.output {cmd := "shasum", args := #["-a","256",target.replace "." "/" ++ ".lean"]}
      if hash.exitCode != 0 then return 2
      hashes := hashes ++ hash.stdout
    IO.FS.writeFile "output/derivative/proof-bundles.sha256" hashes
  let elapsed := elapsed + ((← IO.monoMsNow)-finishStart)
  let report := Json.mkObj [("verified_count",toJson verified.length),("input_count",toJson rows.length),
    ("elapsed_milliseconds",toJson elapsed),("registry_installed",toJson installed),
    ("conditional_axiom",toJson "VerifiedLcalc.Assumptions.ellipticModularity"),("cases",toJson (rows.map rowJson))]
  IO.FS.writeFile "output/derivative/report.json" (report.pretty ++ "\n")
  if !installed then return 2
  IO.println s!"Installed {verified.length} checked exact rank-one certificates."
  if (← runLogged #["lake","build","lmfdb-check"] "output/derivative/regression-build.log") != 0 then return 2
  let r ← IO.Process.output {cmd := ".lake/build/bin/lmfdb-check",args := #["--conditional"]}
  IO.print r.stdout
  IO.eprint r.stderr
  return r.exitCode

def main (args : List String) : IO UInt32 := do
  IO.FS.createDirAll "output/derivative"
  let start ← IO.monoMsNow
  if args == ["--seal-cache"] then
    let report ← IO.ofExcept (Json.parse (← IO.FS.readFile "output/derivative/report.json"))
    let entries ← IO.ofExcept ((← IO.ofExcept (report.getObjVal? "cases")).getArr?)
    let mut rows : List BatchRow := []
    let mut labels : List String := []
    for entry in entries do
      let get (k : String) : IO String := IO.ofExcept (entry.getObjValAs? String k)
      let r : BatchRow := ⟨← get "label",← get "status",← get "module",← get "conductor",← get "equation",← get "bits",← get "terms",← get "source_sha256",← get "log"⟩
      if labels.contains r.label then throw (IO.userError "Duplicate cached derivative label")
      labels := r.label :: labels
      if r.status == "verified-conditional-rank-one" then
        validateSubject r
        let hash ← IO.Process.output {cmd := "shasum",args := #["-a","256",r.moduleName.replace "." "/" ++ ".lean"]}
        if hash.exitCode != 0 || (hash.stdout.splitOn " ")[0]! != r.sourceHash then
          throw (IO.userError "Derivative wrapper changed; regenerate certificates")
      rows := rows ++ [r]
    return ← finish rows ((← IO.monoMsNow)-start)
  if args != [] then
    IO.eprintln "Usage: lake exe certify-derivatives [--seal-cache]"
    return 2
  if (← runLogged #["lake","build","derivative-batch","VerifiedLcalc.Assumptions.DerivativeCertification"] "output/derivative/build.log") != 0 then return 2
  if (← runLogged #[".lake/build/bin/derivative-batch"] "output/derivative/producer.log") != 0 then return 2
  let manifest ← IO.FS.readFile "output/derivative/proposals.tsv"
  let mut rows : List BatchRow := []
  let mut targets : List String := []
  for line in (manifest.splitOn "\n").drop 1 do
    if line.isEmpty then continue
    let fs := line.splitOn "\t"
    if fs.length != 7 then throw (IO.userError "Invalid derivative manifest")
    let r : BatchRow := ⟨fs[0]!,fs[1]!,fs[2]!,fs[3]!,fs[4]!,fs[5]!,fs[6]!,"",""⟩
    if r.status == "proposed" then
      validateSubject r
      targets := targets ++ [← derivativeTarget r.moduleName]
    rows := rows ++ [r]
  let unique := targets.eraseDups.toArray
  for group in [: (unique.size+1)/2] do
    let chunk := unique.extract (group*2) ((group+1)*2)
    IO.println s!"Checking derivative proof group {group+1}/{(unique.size+1)/2}"
    let code ← runLogged (#["lake","build"] ++ chunk) ("output/derivative/group-" ++ toString group ++ ".log")
    if code != 0 then
      IO.eprintln "Derivative proof group rejected; no new registry installed."
      return 2
  let mut checked : List BatchRow := []
  for r in rows do
    if r.status == "proposed" then
      let hash ← IO.Process.output {cmd := "shasum",args := #["-a","256",r.moduleName.replace "." "/" ++ ".lean"]}
      if hash.exitCode != 0 then return 2
      checked := checked ++ [{r with status := "verified-conditional-rank-one",sourceHash := (hash.stdout.splitOn " ")[0]!}]
    else checked := checked ++ [r]
  return ← finish checked ((← IO.monoMsNow)-start)
