import VerifiedLcalc.EllipticCurve.ReductionCore
import VerifiedLcalc.LmfdbSupplement

open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Untrusted witness production; generated Lean checks every prime, product,
minimality test and coefficient identity. Only CurveInput is inspected. -/
def main (args : List String) : IO UInt32 := do
  if args != [] && args != ["--check"] && args != ["--expanded"] && args != ["--expanded", "--check"] then
    IO.eprintln "Usage: lake exe additive-witnesses [--expanded] [--check]"
    return 2
  let expanded := args.contains "--expanded"
  let check := args.contains "--check"
  let moduleName := if expanded then "VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples" else "VerifiedLcalc.EllipticCurve.AdditiveExamples"
  let sourcePath := if expanded then "VerifiedLcalc/EllipticCurve/AdditiveExpandedExamples.lean" else "VerifiedLcalc/EllipticCurve/AdditiveExamples.lean"
  let outputDir := if expanded then "output/additive-expanded" else "output/additive"
  let ns := if expanded then "VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples" else "VerifiedLcalc.EllipticCurve.AdditiveExamples"
  let mut source := "module\n\npublic import VerifiedLcalc.EllipticCurve.ReductionArithmetic\n\n@[expose] public section\nnamespace " ++ ns ++ "\n\n"
  let mut report := "label\tstatus\tadditive-primes\n"
  let mut supported := 0
  let mut total := 0
  for input in (if expanded then Lmfdb.allCases else Lmfdb.cases).map (fun c => c.input) do
    let e := input.equation
    if Int.gcd (discriminant e) (modelC4 e) != 1 then
      total := total + 1
      let primes := (List.range (input.conductor + 1)).filter isPrime
      let additive := primes.filter (fun p => modelReduction e p == .additive)
      if let some w := minimalityWitness? e primes then
        let name := "C" ++ input.label.replace "." "_"
        source := source ++ "namespace " ++ name ++ "\n" ++
          "def equation : Artifacts.CurveEquation := " ++ (reprStr e).replace "\n" " " ++ "\n" ++
          "def witness : MinimalityWitness := " ++ (reprStr w).replace "\n" " " ++ "\n" ++
          "theorem witness_valid : witness.Valid equation := by decide +kernel\n" ++
          "theorem coefficients_correct (limit : ℕ) :\n" ++
          "    modelCoefficients equation limit = (List.range limit).map\n" ++
          "      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=\n" ++
          "  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit\n"
        for p in additive do
          source := source ++ s!"local instance prime_{p} : Fact (Nat.Prime {p}) := ⟨by decide +kernel⟩\n" ++
            s!"theorem additive_factor_{p} :\n" ++
            s!"    ((weierstrass equation ℚ).baseChange ((rationalPlace {p}).adicCompletion ℚ)).localPolynomial\n" ++
            s!"      ((rationalPlace {p}).adicCompletionIntegers ℚ) = 1 :=\n" ++
            s!"  additive_localPolynomial equation (by decide +kernel) {p}\n" ++
            "    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)\n"
        source := source ++ "end " ++ name ++ "\n\n"
        report := report ++ s!"{input.label}\tarithmetic-witness-produced\t{reprStr additive}\n"
        supported := supported + 1
      else
        report := report ++ s!"{input.label}\tminimality-criterion-inconclusive\t{reprStr additive}\n"
  source := source ++ "end " ++ ns ++ "\n"
  let path : System.FilePath := sourcePath
  let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == source) else pure false
  if !unchanged || check then
    for previous in [outputDir ++ "/checked.tsv", outputDir ++ "/checked-source.sha256"] do
      let previous : System.FilePath := previous
      if ← previous.pathExists then IO.FS.removeFile previous
  if !unchanged then IO.FS.writeFile path source
  IO.FS.createDirAll outputDir
  IO.FS.writeFile (outputDir ++ "/proposals.tsv") report
  if check then
    let checked ← IO.Process.output {cmd := "lake", args := #["build", moduleName]}
    IO.FS.writeFile (outputDir ++ "/kernel-replay.log") (checked.stdout ++ checked.stderr)
    if checked.exitCode != 0 then
      IO.eprintln "Arithmetic kernel replay failed; see the output directory kernel-replay.log."
      return 1
    let digest ← IO.Process.output {cmd := "shasum", args := #["-a", "256", path.toString]}
    if digest.exitCode != 0 then
      IO.eprintln "Could not record the checked source hash; no checked report published."
      return 1
    IO.FS.writeFile (outputDir ++ "/checked-source.sha256") digest.stdout
    IO.FS.writeFile (outputDir ++ "/checked.tsv")
      (report.replace "arithmetic-witness-produced" "kernel-checked-arithmetic-only")
    IO.println s!"{supported}/{total} additive models: minimality, all coefficient prefixes, and additive local factors checked by Lean. Analytic ranks remain separate."
    return if supported == total then 0 else 1
  IO.println s!"{supported}/{total} arithmetic witnesses emitted. Run lake exe additive-witnesses --check for kernel replay. No analytic rank is certified here."
  return 0
