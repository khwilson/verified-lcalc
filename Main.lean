import VerifiedLcalc.CertificateDemo

open VerifiedLcalc VerifiedLcalc.Examples

/-- Emit a small checked payload plus its analytic proof, independently of the
producer. Importing this generated module later reuses its compiled theorem. -/
def main (args : List String) : IO UInt32 := do
  match Artifacts.validate cubicRequest cubicArtifact with
  | none =>
    IO.eprintln "The generated payload did not pass its finite checks."
    return 1
  | some c =>
    let proof := "module\n\npublic import VerifiedLcalc.Examples\n\n" ++
      "@[expose] public section\n\n" ++
      "namespace VerifiedLcalc.Certificates.Cubic\n\n" ++
      "open VerifiedLcalc VerifiedLcalc.Examples\n\n" ++
      "-- Polynomial demonstration; this is not an elliptic-curve certificate.\n" ++
      "-- Only the supplied payload is checked; no numerical producer is run.\n" ++
      "def artifact : Artifacts.Artifact :=\n" ++
      "  " ++ (reprStr c.artifact).replace "\n" " " ++ "\n\n" ++
      "theorem checked : Artifacts.check cubicRequest artifact = true := by decide\n\n" ++
      "theorem certified_computation : scan artifact.derivativeBoxes = some artifact.rank :=\n" ++
      "  ((Artifacts.check_correct _ _).mp checked).2.2.2.2\n\n" ++
      "def evidence : Artifacts.AnalyticEvidence cubicRequest artifact :=\n" ++
      "  { function := fun z : ℂ => z ^ 3\n" ++
      "    denotes := rfl\n" ++
      "    analytic := by simpa [cubicRequest, Artifacts.Subject.center] using cubic_analytic\n" ++
      "    enclosures := by\n" ++
      "      have hboxes : artifact.derivativeBoxes = cubicBoxes := by decide\n" ++
      "      rw [hboxes]\n" ++
      "      simpa [cubicRequest, Artifacts.Subject.center] using cubic_enclosures }\n\n" ++
      "theorem certified_analytic_order : analyticOrderAt " ++
      "(fun z : ℂ => z ^ 3) 0 = " ++ toString c.artifact.rank ++ " :=\n" ++
      "  Artifacts.check_monomial_sound rfl evidence checked\n\n" ++
      "end VerifiedLcalc.Certificates.Cubic\n"
    match args with
    | [] => IO.print proof
    | [path] =>
      let file : System.FilePath := path
      let unchanged ← if ← file.pathExists then
          pure ((← IO.FS.readFile file) == proof)
        else pure false
      if unchanged then
        IO.println s!"Certificate already current: {path}"
      else
        IO.FS.writeFile file proof
        IO.println s!"Polynomial demonstration: order = {c.artifact.rank}. Certificate: {path}"
    | _ =>
      IO.eprintln "Usage: lake exe verified-lcalc [certificate.lean]"
      return 2
    return 0
