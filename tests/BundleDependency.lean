import CertifyBatchMain

-- A wrapper hash alone must never authorize a changed proof dependency.
-- Inject a false claim into its bundle, require kernel rejection, restore
-- every edited source/report, and rebuild the original checked registry.
#eval do
  let wrapper : System.FilePath := "VerifiedLcalc/Certificates/Batch/C27_a1.lean"
  let target ← certificateBuildTarget "VerifiedLcalc.Certificates.Batch.C27_a1"
  if !target.startsWith "VerifiedLcalc.Certificates.Batch.Bundles." then
    throw (IO.userError "Expected a shared proof bundle")
  let path : System.FilePath := target.replace "." "/" ++ ".lean"
  let beforeWrapper ← IO.FS.readFile wrapper
  let beforeBundle ← IO.FS.readFile path
  let beforeReport ← IO.FS.readFile "output/batch/report.json"
  let beforeCore ← IO.FS.readFile "VerifiedLcalc/Regression/Generated.lean"
  let beforeProof ← IO.FS.readFile "VerifiedLcalc/Assumptions/Generated.lean"
  let beforeLog ← IO.FS.readFile "output/batch/registry.log"
  IO.FS.createDirAll "output/tests/bundle-dependency"
  IO.FS.writeFile "output/tests/bundle-dependency/bundle-before.lean" beforeBundle
  IO.FS.writeFile "output/tests/bundle-dependency/report-before.json" beforeReport
  let mut rejected := false
  try
    IO.FS.writeFile path (beforeBundle ++ "\nexample : False := by decide +kernel\n")
    if (← IO.FS.readFile wrapper) != beforeWrapper then
      throw (IO.userError "Wrapper unexpectedly changed")
    let status ← sealCheckedCache
    let report ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "output/batch/report.json"))
    let installed ← IO.ofExcept (report.getObjValAs? Bool "registry_installed")
    if status == 0 || installed then
      throw (IO.userError "Changed invalid bundle was accepted")
    IO.FS.writeFile "output/tests/bundle-dependency/rejected-bundle.log"
      (← IO.FS.readFile "output/batch/registry.log")
    IO.FS.writeFile "output/tests/bundle-dependency/rejected-rollback.log"
      (← IO.FS.readFile "output/batch/rollback-registry.log")
    rejected := true
  finally
    IO.FS.writeFile path beforeBundle
    IO.FS.writeFile "output/batch/report.json" beforeReport
    IO.FS.writeFile "VerifiedLcalc/Regression/Generated.lean" beforeCore
    IO.FS.writeFile "VerifiedLcalc/Assumptions/Generated.lean" beforeProof
    let restored ← runLogged #["lake", "build", "VerifiedLcalc.Assumptions.Regression"]
      "output/tests/bundle-dependency/restoration.log"
    if restored != 0 then throw (IO.userError "Could not restore the checked registry")
    IO.FS.writeFile "output/batch/registry.log" beforeLog
  if !rejected then throw (IO.userError "Did not verify dependency rejection")
  IO.println "Rejected a false bundle despite an unchanged wrapper; restored sources and checked registry artifacts."
