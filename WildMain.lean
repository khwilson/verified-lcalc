import VerifiedLcalc.EllipticCurve.WildRootCore
import VerifiedLcalc.LmfdbSupplement
open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Produce arithmetic-only Tate/table certificates. Expected analytic ranks
are never read, and model minimality is not asserted by this command. -/
def main (args : List String) : IO UInt32 := do
  if args != [] && args != ["--check"] then
    IO.eprintln "Usage: lake exe wild-witnesses [--check]"
    return 2
  let mut source := "module\npublic import VerifiedLcalc.EllipticCurve.WildArithmetic\n@[expose] public section\nnamespace VerifiedLcalc.EllipticCurve.WildExpandedExamples\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\n"
  let mut rows := "label\tstatus\tconductor\tsign\tkodaira2\tkodaira3\n"
  let mut count := 0
  let mut total := 0
  for input in Lmfdb.allCases.map (·.input) do
    let e := input.equation
    if !tameAtWild e && discriminant e != 0 then
      total := total+1
      if let some d := wildData? e then
        let ps := (List.range (input.conductor+1)).filter
          (fun (p : Nat) => isPrime p && discriminant e % (p : Int) == 0)
        let (n,sign) := wildConductorRootFromPrimes e d ps
        let name := "C" ++ input.label.replace "." "_"
        source := source ++ "namespace " ++ name ++ "\n" ++
          "def equation : Artifacts.CurveEquation := " ++ (reprStr e).replace "\n" " " ++ "\n" ++
          "def data : WildData := " ++ (reprStr d).replace "\n" " " ++ "\n" ++
          "theorem valid : data.Valid equation := by decide +kernel\n" ++
          s!"theorem level_fast : wildLevelFast equation data = {n} := by decide +kernel\n" ++
          s!"theorem level_formula : wildLevel equation data = {n} :=\n" ++
          "  (wildLevel_eq_fast equation data).trans level_fast\n" ++
          s!"theorem sign_fast : wildSignFast equation data = ({sign} : Int) := by decide +kernel\n" ++
          s!"theorem sign_formula : wildSign equation data = ({sign} : Int) :=\n" ++
          "  (wildSign_eq_fast equation data valid).trans sign_fast\n" ++
          s!"theorem conductor_reference_match : ({n} : Nat) = {input.conductor} := by decide +kernel\n" ++
          "end " ++ name ++ "\n\n"
        count := count+1
        rows := rows ++ s!"{input.label}\tproposed-arithmetic\t{n}\t{sign}\t{reprStr (d.atTwo.map (·.kodaira))}\t{reprStr (d.atThree.map (·.kodaira))}\n"
      else rows := rows ++ s!"{input.label}\tunresolved\t\t\t\t\n"
  source := source ++ s!"def certificateCount : Nat := {count}\nend VerifiedLcalc.EllipticCurve.WildExpandedExamples\n"
  IO.FS.createDirAll "output/wild"
  let path : System.FilePath := "VerifiedLcalc/EllipticCurve/WildExpandedExamples.lean"
  let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == source) else pure false
  if !unchanged || args == ["--check"] then
    for file in ["output/wild/checked.tsv", "output/wild/checked-source.sha256"] do
      let p : System.FilePath := file
      if ← p.pathExists then IO.FS.removeFile p
  if !unchanged then IO.FS.writeFile path source
  IO.FS.writeFile "output/wild/proposals.tsv" rows
  if args == ["--check"] then
    let result ← IO.Process.output {cmd := "lake", args := #["build", "VerifiedLcalc.EllipticCurve.WildExpandedExamples"]}
    IO.FS.writeFile "output/wild/kernel-replay.log" (result.stdout ++ result.stderr)
    if result.exitCode != 0 then return 1
    let digest ← IO.Process.output {cmd := "shasum", args := #["-a", "256", path.toString]}
    if digest.exitCode != 0 then return 1
    IO.FS.writeFile "output/wild/checked-source.sha256" digest.stdout
    IO.FS.writeFile "output/wild/checked.tsv" (rows.replace "proposed-arithmetic" "kernel-checked-arithmetic-only")
    IO.println s!"{count}/{total} Tate transcripts and conductor/sign mathematical formulas checked. Minimality and analytic ranks remain separate."
    return if count == total then 0 else 1
  IO.println s!"{count}/{total} candidate transcripts emitted. Run --check for kernel replay."
  return 0
