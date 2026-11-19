import VerifiedLcalc.EllipticCurve.CentralCore
import VerifiedLcalc.Lmfdb

open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Save exact output data and finite replay checks. The enclosing theorem keeps
the series evidence as an explicit argument. -/
def writeCentralCertificate (label : String) (r : CentralResult) (path : String) : IO Unit := do
  let namespaceName := "Central_" ++ label.replace "." "_" ++
    "_M" ++ toString r.termLimit ++ "_P" ++ toString r.policy.precisionBits ++
    (if r.rootNumber == -1 then "_minus" else "_plus")
  let remainder := (squareTailBound r.geometricUpper r.termLimit).getD 0
  let source := "module\n\npublic import VerifiedLcalc.EllipticCurve.Central\n\n" ++
    "@[expose] public section\n\nnamespace VerifiedLcalc.Certificates." ++ namespaceName ++ "\n\n" ++
    "open VerifiedLcalc VerifiedLcalc.EllipticCurve\n\n" ++
    "-- Model central expression. No analytic rank or elliptic continuation is asserted.\n" ++
    "def result : CentralResult :=\n  " ++ (reprStr r).replace "\n" " " ++ "\n\n" ++
    "theorem payload_correct : CentralPayloadCorrect result := by\n" ++
    "  unfold CentralPayloadCorrect\n" ++
    "  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,\n" ++
    "    by decide +kernel, by decide +kernel, by decide +kernel,\n" ++
    "    " ++ (reprStr remainder).replace "\n" " " ++ ", by decide +kernel,\n" ++
    "    by decide +kernel, by decide +kernel⟩\n\n" ++
    "theorem encloses (value : ℝ) (e : CentralSeriesEvidence result value) :\n" ++
    "    result.box.Contains (Complex.ofReal value) :=\n" ++
    "  centralPayload_sound payload_correct e\n\n" ++
    "end VerifiedLcalc.Certificates." ++ namespaceName ++ "\n"
  let file : System.FilePath := path
  let unchanged ← if ← file.pathExists then pure ((← IO.FS.readFile file) == source) else pure false
  if !unchanged then IO.FS.writeFile file source
  IO.println s!"Saved central-expression payload: {path}"

/-- Execute the exact central-expression evaluator. Root number and conductor
are inputs, not proved arithmetic invariants. This command never reports ranks. -/
def main (args : List String) : IO UInt32 := do
  let outputPath := if args.length == 4 then args[3]? else none
  match args.take 3 with
  | [label, rootText, limitText] =>
    if args.length > 4 || (label == "--all" && outputPath.isSome) then
      IO.eprintln "Certificate output requires exactly one curve. Extra arguments are not accepted."
      return 2
    match rootText.toInt?, limitText.toNat? with
    | some root, some limit =>
      let inputs := Lmfdb.cases.map (fun c => c.input)
      let selected := if label == "--all" then inputs else inputs.filter (fun c => c.label == label)
      if selected.isEmpty then
        IO.eprintln "Unknown curve label."
        return 2
      IO.println s!"precision_bits={globalPrecision.precisionBits}; cutoff={globalPrecision.cutoff}"
      IO.println "status=model-central-expression; conductor and root number supplied; analytic connection pending"
      let mut failures := 0
      for input in selected do
        match evaluateCentral input.equation input.conductor root limit with
        | none =>
          failures := failures + 1
          IO.println s!"{input.label}: unresolved (invalid inputs or insufficient terms/precision for tail bound)"
        | some result =>
          IO.println s!"{input.label}: lower={result.box.reLo}; upper={result.box.reHi}; tail={result.tail}"
          if let some path := outputPath then writeCentralCertificate input.label result path
          if label != "--all" then
            IO.println s!"coefficients={result.coefficients}"
            IO.println s!"alpha=[{result.alphaLo},{result.alphaHi}]"
      IO.eprintln s!"{selected.length} central-expression attempts; {failures} unresolved; no analytic ranks claimed."
      return if failures == 0 then 0 else 1
    | _, _ =>
      IO.eprintln "Expected root number 1 or -1 and a natural term limit."
      return 2
  | _ =>
    IO.eprintln "Usage: lake exe ec-central LMFDB_LABEL ROOT_NUMBER TERM_LIMIT [certificate.lean] (or --all ROOT_NUMBER TERM_LIMIT)"
    return 2
