import CertifyDerivativeMain

-- A rank-one theorem for 37.a1 cannot be bound to the equation for 11.a1.
-- Failed installation must restore both registry sources and checked artifacts.
#eval do
  let core : System.FilePath := "VerifiedLcalc/Regression/GeneratedRankOne.lean"
  let proof : System.FilePath := "VerifiedLcalc/Assumptions/GeneratedRankOne.lean"
  let beforeCore ← IO.FS.readFile core
  let beforeProof ← IO.FS.readFile proof
  let beforeLog ← IO.FS.readFile "output/derivative/registry.log"
  IO.FS.createDirAll "output/tests/derivative-rollback"
  let wrong : BatchRow := ⟨"deliberate-wrong-subject", "test", "VerifiedLcalc.Certificates.DerivativeBatch.C37_a1",
    "11", "{ a1 := 0, a2 := -1, a3 := 1, a4 := -10, a6 := -20 }", "53", "12", "", ""⟩
  try
    let accepted ← installDerivativeRegistry [wrong]
    IO.FS.writeFile "output/tests/derivative-rollback/rejected-binding.log"
      (← IO.FS.readFile "output/derivative/registry.log")
    if accepted then throw (IO.userError "Accepted a derivative theorem for the wrong curve")
    if (← IO.FS.readFile core) != beforeCore || (← IO.FS.readFile proof) != beforeProof then
      throw (IO.userError "Derivative registry sources were not restored")
    let consumer ← IO.Process.output {cmd := "lake", args := #["env", "lean", "certificates/Derivative.lean"]}
    IO.FS.writeFile "output/tests/derivative-rollback/cached-consumer.log" (consumer.stdout ++ consumer.stderr)
    if consumer.exitCode != 0 then throw (IO.userError "Restored derivative artifact failed consumption")
    IO.println "Rejected wrong-curve derivative binding; restored sources and checked artifacts."
  finally
    if (← IO.FS.readFile core) != beforeCore || (← IO.FS.readFile proof) != beforeProof then
      IO.FS.writeFile core beforeCore
      IO.FS.writeFile proof beforeProof
      if (← runLogged #["lake","build","VerifiedLcalc.Assumptions.Regression"]
          "output/tests/derivative-rollback/emergency-restore.log") != 0 then
        throw (IO.userError "Emergency derivative registry restore failed")
    IO.FS.writeFile "output/derivative/registry.log" beforeLog
