import VerifiedLcalc.EllipticCurve.CentralCore
import VerifiedLcalc.EllipticCurve.PrefixCore
import VerifiedLcalc.EllipticCurve.ReductionCore
import VerifiedLcalc.EllipticCurve.WildRootCore
import VerifiedLcalc.LmfdbSupplement

open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Untrusted source serialization: every mathematical assertion emitted here
is independently checked by Lean. This performs no theorem proving or rank lookup. -/
def emitBatchCertificate (label : String) (r : CentralResult) (dir : System.FilePath) (tame : Option MinimalityWitness := none) (wild : Option WildData := none) : IO String := do
  let name := "C" ++ label.replace "." "_"
  let ns := "VerifiedLcalc.Certificates.Batch." ++ name
  let remainder := (squareTailBound r.geometricUpper r.termLimit).getD 0
  let certification := if let some d := wild then
      "  certifyWildCentralModel result nonsingular\n    (" ++ (reprStr (tame.getD ⟨[]⟩)).replace "\n" " " ++ ") (by decide +kernel)\n    (" ++
      (reprStr d).replace "\n" " " ++ ") (by decide +kernel)\n" ++
      "    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)\n\n"
    else match tame with
    | none => "  certifySemistableCentralModel result nonsingular (by decide +kernel)\n" ++
      "    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct\n" ++
      "    (by decide +kernel)\n\n"
    | some w => "  certifyTameCentralModel result nonsingular\n    (" ++ (reprStr w).replace "\n" " " ++
      ") (by decide +kernel) (by decide +kernel)\n" ++
      "    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)\n\n"
  let source := "module\n\npublic import VerifiedLcalc.Assumptions.Batch\npublic import VerifiedLcalc.Assumptions.FastSign\n" ++
    (if wild.isSome then "public import VerifiedLcalc.Assumptions.WildCertification\n" else if tame.isSome then "public import VerifiedLcalc.Assumptions.TameCertification\n" else "") ++ "\n@[expose] public section\nnamespace " ++ ns ++ "\n" ++
    "open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions\n\n" ++
    "def result : CentralResult :=\n  " ++ (reprStr r).replace "\n" " " ++ "\n\n" ++
    "theorem payload_correct : CentralPayloadCorrect result := by\n  unfold CentralPayloadCorrect\n" ++
    "  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,\n" ++
    "    by decide +kernel, by decide +kernel, by decide +kernel,\n    " ++
    (reprStr remainder).replace "\n" " " ++ ", by decide +kernel, by decide +kernel, by decide +kernel⟩\n\n" ++
    "theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel\n\n" ++
    "theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=\n" ++
    certification ++
    "def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=\n" ++
    "  ⟨0, analytic_rank_zero⟩\n\n" ++
    "set_option pp.fullNames true\n\n" ++
    "/-- info: '" ++ ns ++ ".analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/\n" ++
    "#guard_msgs (whitespace := lax) in\n#print axioms analytic_rank_zero\n\nend " ++ ns ++ "\n"
  let path := dir / (name ++ ".lean")
  let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == source) else pure false
  if !unchanged then IO.FS.writeFile path source
  return ns

/-- Compile proofs sharing a conductor range in one Lean module. Each curve
retains its public namespace and a small re-export module. The mathematical
proof text is preserved, and the registry imports the checked bundle directly. -/
def bundleBatchCertificates (entries : List (String × Nat)) : IO Unit := do
  let dir : System.FilePath := "VerifiedLcalc/Certificates/Batch/Bundles"
  IO.FS.createDirAll dir
  let buckets := (entries.map (fun e => e.2 / 32)).eraseDups
  for bucket in buckets do
    let group := entries.filter (fun e => e.2 / 32 == bucket)
    let name := "VerifiedLcalc.Certificates.Batch.Bundles.N" ++ toString bucket
    let mut body := "module\npublic import VerifiedLcalc.Assumptions.Batch\npublic import VerifiedLcalc.Assumptions.FastSign\npublic import VerifiedLcalc.Assumptions.TameCertification\npublic import VerifiedLcalc.Assumptions.WildCertification\n\n@[expose] public section\n"
    for (moduleName, _) in group do
      let source ← IO.FS.readFile (moduleName.replace "." "/" ++ ".lean")
      let pieces := source.splitOn "@[expose] public section\n"
      if pieces.length != 2 then throw (IO.userError "Malformed candidate source while bundling")
      body := body ++ "\n" ++ pieces[1]!
    let path := dir / ("N" ++ toString bucket ++ ".lean")
    let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == body) else pure false
    if !unchanged then IO.FS.writeFile path body
    for (moduleName, _) in group do
      let wrapper := "module\n-- Certificate proofs are kernel-checked together in the imported bundle.\npublic import " ++ name ++ "\n"
      IO.FS.writeFile (moduleName.replace "." "/" ++ ".lean") wrapper

/-- Candidate search only. The producer sees CurveInput values and never the
reference rank. Eligibility hints, N and w are all checked again in the output. -/
def main (args : List String) : IO UInt32 := do
  if args != [] then
    IO.eprintln "Usage: lake exe ec-batch"
    return 2
  let dir : System.FilePath := "VerifiedLcalc/Certificates/Batch"
  IO.FS.createDirAll dir
  IO.FS.createDirAll "output/batch"
  let mut rows := "label\tstatus\tmodule\tconductor\tequation\tbits\tterms\n"
  let mut proposed := 0
  let mut entries : List (String × Nat) := []
  let inputs := Lmfdb.allCases.map (fun c => c.input)
  for input in inputs do
    let e := input.equation
    let c4 := (b2 e) ^ 2 - 24 * b4 e
    let mut status := "unsupported-semistable-model"
    let mut selected : Option CentralResult := none
    let semistable := Int.gcd (discriminant e) c4 == 1
    let candidates := (List.range (input.conductor + 1)).filter isPrime
    let witness := minimalityWitness? e candidates
    let badPrimes := candidates.filter (fun (p : Nat) => discriminant e % (p : Int) == 0)
    let wild := if tameAtWild e then none else wildData? e
    let supported := discriminant e != 0 &&
      (semistable || (witness.isSome && (tameAtWild e || wild.isSome)))
    if supported then
      let localData := match wild with
        | some d => some (wildConductorRootFromPrimes e d badPrimes)
        | none => conductorRootFromPrimes? e badPrimes
      if let some (_, sign) := localData then
        if sign != 1 then
          status := "nonpositive-sign-needs-derivatives"
        else
          status := "interval-not-separated"
          for bits in [53, 80, 106] do
            for limit in [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64] do
              if selected.isNone then
                if let some r := evaluateCentral e input.conductor 1 limit ⟨bits⟩ then
                  if r.box.excludesZero then selected := some r
    else if discriminant e != 0 && !semistable then
      status := if witness.isSome then "wild-additive-conductor-sign-unproved"
        else "minimal-model-unresolved"
    if let some r := selected then
      let moduleName ← emitBatchCertificate input.label r dir (if semistable then none else witness) wild
      rows := rows ++ s!"{input.label}\tproposed\t{moduleName}\t{input.conductor}\t{(reprStr e).replace "\n" " "}\t{r.policy.precisionBits}\t{r.termLimit}\n"
      proposed := proposed + 1
      entries := entries ++ [(moduleName, input.conductor)]
      IO.println s!"{input.label}: proposed; bits={r.policy.precisionBits}; terms={r.termLimit}"
    else
      rows := rows ++ s!"{input.label}\t{status}\t\t{input.conductor}\t{(reprStr e).replace "\n" " "}\t\t\n"
  bundleBatchCertificates entries
  IO.FS.writeFile "output/batch/proposals.tsv" rows
  IO.println s!"{inputs.length} inputs; {proposed} proposals. No proposal is certified until kernel replay succeeds."
  return 0
