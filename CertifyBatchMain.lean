import VerifiedLcalc.BatchIO
open Lean

/-- A curve's public module can re-export a shared checked proof bundle.
The complete dependency graph is always built; this never trusts object files. -/
def certificateBuildTarget (moduleName : String) : IO String := do
  let source ← IO.FS.readFile (moduleName.replace "." "/" ++ ".lean")
  let marker := "public import VerifiedLcalc.Certificates.Batch.Bundles."
  let importsFound := (source.splitOn "\n").filter (·.startsWith marker)
  if importsFound.isEmpty then return moduleName
  if importsFound.length != 1 then throw (IO.userError "Ambiguous certificate bundle")
  let target := (importsFound[0]!.drop "public import ".length).toString
  if !(target.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then
    throw (IO.userError "Invalid certificate bundle target")
  return target

def installRegistry (verified : List BatchRow) : IO Bool := do
  let core : System.FilePath := "VerifiedLcalc/Regression/Generated.lean"
  let proof : System.FilePath := "VerifiedLcalc/Assumptions/Generated.lean"
  let oldCore ← IO.FS.readFile core
  let oldProof ← IO.FS.readFile proof
  let keys := String.intercalate ",\n  " (verified.map fun r => s!"({r.equation}, {r.conductor})")
  IO.FS.writeFile core ("module\n\npublic import VerifiedLcalc.Certificate\n\n@[expose] public section\n" ++
    "namespace VerifiedLcalc.Regression\n\n" ++
    "-- Generated from kernel-checked certificates; no expected ranks are inputs.\n" ++
    "def generatedCertificateKeys : List (Artifacts.CurveEquation × Nat) := [\n  " ++ keys ++ "]\n\n" ++
    "end VerifiedLcalc.Regression\n")
  let mut importTargets : List String := []
  for r in verified do
    importTargets := importTargets ++ [← certificateBuildTarget r.moduleName]
  let imports := String.join (importTargets.eraseDups.map fun name => s!"public import {name}\n")
  let mut body := "module\n\npublic import VerifiedLcalc.Regression.Generated\n" ++ imports ++
    "\n@[expose] public section\nnamespace VerifiedLcalc.Assumptions\nopen EllipticCurve Regression\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\n" ++
    "private def KeySound (k : Artifacts.CurveEquation × Nat) : Prop :=\n" ++
    "  ∃ hn : discriminant k.1 ≠ 0, analyticOrderAt (modularWitness k.1 hn).formL (1 : ℂ) = 0\n\n" ++
    "private theorem allKeysSound : ∀ k ∈ generatedCertificateKeys, KeySound k := by\n" ++
    "  unfold generatedCertificateKeys\n  exact\n"
  for r in verified do
    body := body ++ "    (List.forall_mem_cons (p := KeySound)).mpr ⟨⟨" ++
      r.moduleName ++ ".nonsingular, " ++ r.moduleName ++ ".analytic_rank_zero⟩,\n"
  body := body ++ "    List.forall_mem_nil _" ++ String.ofList (List.replicate verified.length '⟩') ++ "\n\n" ++
    "theorem generatedCertificateKeys_sound (e : Artifacts.CurveEquation) (N : Nat)\n" ++
    "    (h : (e, N) ∈ generatedCertificateKeys) :\n    ∃ hn : discriminant e ≠ 0,\n" ++
    "      analyticOrderAt (modularWitness e hn).formL (1 : ℂ) = 0 :=\n" ++
    "  allKeysSound (e, N) h\n"
  body := body ++ "\nset_option pp.fullNames true\n\n" ++
    "/-- info: 'VerifiedLcalc.Assumptions.generatedCertificateKeys_sound' depends on axioms: " ++
    "[propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/\n" ++
    "#guard_msgs (whitespace := lax) in\n#print axioms generatedCertificateKeys_sound\n\n" ++
    "end VerifiedLcalc.Assumptions\n"
  IO.FS.writeFile proof body
  let code ← runLogged #["lake", "build", "VerifiedLcalc.Assumptions.Regression"] "output/batch/registry.log"
  if code != 0 then
    IO.FS.writeFile core oldCore
    IO.FS.writeFile proof oldProof
    let rollback ← runLogged #["lake", "build", "VerifiedLcalc.Assumptions.Regression"] "output/batch/rollback-registry.log"
    if rollback == 0 then
      IO.eprintln "Registry proof failed; previous sources and checked artifacts restored. See output/batch/registry.log"
    else
      IO.eprintln "Registry proof failed; sources restored but artifact rebuild also failed. See output/batch/rollback-registry.log"
    return false
  return true

/-- Re-seal a checked report after validating its source hashes and subjects.
Lake rebuilds the complete proof dependency graph; object-file presence alone
never authorizes a cache entry. Reference ranks are not read here. -/
def sealCheckedCache : IO UInt32 := do
  let start ← IO.monoMsNow
  let report ← IO.ofExcept (Json.parse (← IO.FS.readFile "output/batch/report.json"))
  let entries ← IO.ofExcept ((← IO.ofExcept (report.getObjVal? "cases")).getArr?)
  let mut rows : List BatchRow := []
  let mut verified : List BatchRow := []
  let mut seen : List String := []
  for entry in entries do
    let get (k : String) : IO String := IO.ofExcept (entry.getObjValAs? String k)
    let label ← get "label"
    if seen.contains label then throw (IO.userError "Duplicate cached label")
    seen := label :: seen
    let some c := VerifiedLcalc.Lmfdb.allCases.find? (fun c => c.input.label == label)
      | throw (IO.userError "Cached subject is absent from the current fixture")
    let equation := (reprStr c.input.equation).replace "\n" " "
    if (← get "equation") != equation || (← get "conductor") != toString c.input.conductor then
      throw (IO.userError "Cached subject changed; run the full batch")
    let status ← get "status"
    let name ← get "module"
    let hash ← get "source_sha256"
    if status == "verified-conditional-rank-zero" then
      if name != "VerifiedLcalc.Certificates.Batch.C" ++ label.replace "." "_" ||
          !(name.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then
        throw (IO.userError "Invalid cached module")
      let digest ← IO.Process.output {cmd := "shasum", args := #["-a", "256", name.replace "." "/" ++ ".lean"]}
      if digest.exitCode != 0 || (digest.stdout.splitOn " ")[0]! != hash then
        throw (IO.userError "Checked source changed; run the full batch")
    let r : BatchRow := ⟨label, status, name, toString c.input.conductor, equation,
      ← get "bits", ← get "terms", hash, ← get "log"⟩
    rows := rows ++ [r]
    if status == "verified-conditional-rank-zero" then verified := verified ++ [r]
  if rows.length != VerifiedLcalc.Lmfdb.allCases.length || verified.isEmpty then
    throw (IO.userError "Incomplete checked report")
  let installed ← installRegistry verified
  let report := report.setObjVal! "registry_installed" (toJson installed)
  let report := report.setObjVal! "cases" (toJson (rows.map rowJson))
  let report := report.setObjVal! "seal_elapsed_milliseconds" (toJson ((← IO.monoMsNow) - start))
  IO.FS.writeFile "output/batch/report.json" (report.pretty ++ "\n")
  if !installed then return 2
  IO.println s!"Sealed {verified.length} checked rank-zero certificates for {rows.length} inputs."
  if (← runLogged #["lake", "build", "lmfdb-check"] "output/batch/regression-build.log") != 0 then return 2
  let result ← IO.Process.output {cmd := ".lake/build/bin/lmfdb-check", args := #["--conditional"]}
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode

def main (args : List String) : IO UInt32 := do
  if args == ["--seal-cache"] then return ← sealCheckedCache
  if args != [] then
    IO.eprintln "Usage: lake exe certify-batch [--seal-cache]"
    return 2
  let start ← IO.monoMsNow
  IO.FS.createDirAll "output/batch"
  if (← runLogged #["lake", "build", "ec-batch", "VerifiedLcalc.Assumptions.Batch"] "output/batch/build.log") != 0 then
    IO.eprintln "Batch infrastructure build failed."
    return 2
  if (← runLogged #[".lake/build/bin/ec-batch"] "output/batch/producer.log") != 0 then
    IO.eprintln "Candidate producer failed."
    return 2
  let input ← IO.FS.readFile "output/batch/proposals.tsv"
  -- Replay a bounded group in one Lake invocation. A zero exit status checks
  -- every target; failed groups fall back to individual replay for attribution.
  -- Validate names before giving any producer-supplied target to Lake.
  let mut targets : Array String := #[]
  for line in (input.splitOn "\n").drop 1 do
    if line.isEmpty then continue
    let f := line.splitOn "\t"
    if f.length != 7 then
      IO.eprintln "Malformed producer manifest."
      return 2
    if f[1]! == "proposed" then
      let name := f[2]!
      if !name.startsWith "VerifiedLcalc.Certificates.Batch.C" ||
          !(name.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then
        IO.eprintln "Invalid generated module name."
        return 2
      let target ← certificateBuildTarget name
      if !targets.contains target then targets := targets.push target
  let mut bulkVerified : List String := []
  let mut rejectedTargets : List String := []
  for group in [: (targets.size + 7) / 8] do
    let chunk := targets.extract (group * 8) ((group + 1) * 8)
    IO.println s!"Kernel replay group {group + 1}/{(targets.size + 7) / 8}"
    let code ← runLogged (#["lake", "build"] ++ chunk) s!"output/batch/group-{group}.log"
    if code == 0 then bulkVerified := bulkVerified ++ chunk.toList
    else
      for target in chunk do
        let code ← runLogged #["lake", "build", target]
          ("output/batch/target-" ++ target.replace "." "_" ++ ".log")
        if code == 0 then bulkVerified := bulkVerified ++ [target]
        else rejectedTargets := rejectedTargets ++ [target]
  let mut rows : List BatchRow := []
  let mut verified : List BatchRow := []
  for line in (input.splitOn "\n").drop 1 do
    if line.isEmpty then continue
    let fields := line.splitOn "\t"
    if fields.length != 7 then
      IO.eprintln "Malformed producer manifest."
      return 2
    let mut r : BatchRow := ⟨fields[0]!, fields[1]!, fields[2]!, fields[3]!, fields[4]!, fields[5]!, fields[6]!, "", ""⟩
    if r.status == "proposed" then
      if !r.moduleName.startsWith "VerifiedLcalc.Certificates.Batch.C" ||
          !(r.moduleName.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then
        IO.eprintln "Invalid generated module name."
        return 2
      IO.println s!"Checking {r.label}..."
      let target ← certificateBuildTarget r.moduleName
      let log := if rejectedTargets.contains target then
          "output/batch/target-" ++ target.replace "." "_" ++ ".log"
        else "output/batch/" ++ (r.moduleName.splitOn ".").getLast! ++ ".log"
      let code ← if bulkVerified.contains target then pure 0 else if rejectedTargets.contains target then pure 1 else
        runLogged #["lake", "build", target] log
      if code != 0 then
        r := { r with status := "kernel-rejected", log := log }
      else
        let source := r.moduleName.replace "." "/" ++ ".lean"
        let hash ← IO.Process.output {cmd := "shasum", args := #["-a", "256", source]}
        if hash.exitCode != 0 then
          IO.eprintln "Source checksum failed."
          return 2
        r := { r with status := "verified-conditional-rank-zero", sourceHash := (hash.stdout.splitOn " ")[0]! }
        verified := verified ++ [r]
    rows := rows ++ [r]
  let installed ← if verified.isEmpty then pure true else installRegistry verified
  let elapsed ← IO.monoMsNow
  let report := Json.mkObj [
    ("conditional_axiom", toJson "VerifiedLcalc.Assumptions.ellipticModularity"),
    ("verified_count", toJson verified.length), ("input_count", toJson rows.length),
    ("elapsed_milliseconds", toJson (elapsed - start)),
    ("registry_installed", toJson installed), ("cases", toJson (rows.map rowJson))]
  IO.FS.writeFile "output/batch/report.json" (report.pretty ++ "\n")
  if !installed then return 2
  IO.println s!"Verified {verified.length}/{rows.length} inputs; report: output/batch/report.json"
  if (← runLogged #["lake", "build", "lmfdb-check"] "output/batch/regression-build.log") != 0 then return 2
  let result ← IO.Process.output {cmd := ".lake/build/bin/lmfdb-check", args := #["--conditional"]}
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
