import CertifyBatchMain

-- Deliberately try to bind the 11.a2 theorem to the 5077.a1 equation.
-- The kernel must reject the binding, and both sources and compiled artifacts
-- must be restored before the previously checked cache is consumed again.
#eval do
  let core : System.FilePath := "VerifiedLcalc/Regression/Generated.lean"
  let proof : System.FilePath := "VerifiedLcalc/Assumptions/Generated.lean"
  let beforeCore ← IO.FS.readFile core
  let beforeProof ← IO.FS.readFile proof
  let beforeLog ← IO.FS.readFile "output/batch/registry.log"
  let report ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "output/batch/report.json"))
  let count ← IO.ofExcept (report.getObjValAs? Nat "verified_count")
  IO.FS.createDirAll "output/tests/registry-rollback"
  IO.FS.writeFile "output/tests/registry-rollback/core-before.lean" beforeCore
  IO.FS.writeFile "output/tests/registry-rollback/proof-before.lean" beforeProof
  let wrong : BatchRow := ⟨"deliberate-wrong-subject", "test", "VerifiedLcalc.Certificates.Batch.C11_a2",
    "5077", "{ a1 := 0, a2 := 0, a3 := 1, a4 := -7, a6 := 6 }", "53", "1", "", ""⟩
  try
    let accepted ← installRegistry [wrong]
    let rejectedLog ← IO.FS.readFile "output/batch/registry.log"
    IO.FS.writeFile "output/tests/registry-rollback/rejected-binding.log" rejectedLog
    if accepted then throw (IO.userError "Incorrectly accepted a certificate for the wrong curve")
    if (← IO.FS.readFile core) != beforeCore || (← IO.FS.readFile proof) != beforeProof then
      throw (IO.userError "Registry sources were not restored")
    let consumer ← IO.Process.output {cmd := "lake", args := #["env", "lean", "certificates/Batch.lean"]}
    IO.FS.writeFile "output/tests/registry-rollback/cached-consumer.log" (consumer.stdout ++ consumer.stderr)
    if consumer.exitCode != 0 || !(consumer.stdout.splitOn "\n").contains (toString count) then
      throw (IO.userError "Restored compiled cache failed its consumer check")
    IO.println s!"Rejected the wrong curve binding; restored sources and the checked {count}-entry compiled cache."
  finally
    if (← IO.FS.readFile core) != beforeCore || (← IO.FS.readFile proof) != beforeProof then
      IO.FS.writeFile core beforeCore
      IO.FS.writeFile proof beforeProof
      let repaired ← runLogged #["lake", "build", "VerifiedLcalc.Assumptions.Regression"]
        "output/tests/registry-rollback/emergency-restore.log"
      if repaired != 0 then throw (IO.userError "Emergency registry restore failed")
    IO.FS.writeFile "output/batch/registry.log" beforeLog
