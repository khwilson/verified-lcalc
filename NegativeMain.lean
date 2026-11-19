import VerifiedLcalc.LmfdbSupplement
import VerifiedLcalc.EllipticCurve.WildRootCore

open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Candidate-only generation, followed by independent Lean checking of the
actual sign formula. No expected analytic rank is read. -/
def main (args : List String) : IO UInt32 := do
  if args != [] && args != ["--check"] then
    IO.eprintln "Usage: lake exe negative-certificates [--check]"
    return 2
  let mut source := "module\n\npublic import VerifiedLcalc.Assumptions.TameNegativeSign\npublic import VerifiedLcalc.Assumptions.WildCertification\n\n@[expose] public section\nnamespace VerifiedLcalc.Certificates.NegativeSigns\nopen EllipticCurve Assumptions\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\n"
  let mut report := "label\tclaim\n"
  let mut count := 0
  for input in Lmfdb.allCases.map (·.input) do
    let e := input.equation
    let primes := (List.range (input.conductor + 1)).filter isPrime
    let bad := primes.filter (fun (p : Nat) => discriminant e % (p : Int) == 0)
    let semistable := Int.gcd (discriminant e) (modelC4 e) == 1
    let witness := minimalityWitness? e primes
    let wild := if tameAtWild e then none else wildData? e
    if discriminant e != 0 && (semistable || (witness.isSome && (tameAtWild e || wild.isSome))) then
      let hint := match wild with
        | some d => some (wildConductorRootFromPrimes e d bad).2
        | none => (conductorRootFromPrimes? e bad).map (·.2)
      if hint == some (-1) then
        let name := "C" ++ input.label.replace "." "_"
        let proof := if let some d := wild then
          "def witness : MinimalityWitness := " ++ (reprStr (witness.getD ⟨[]⟩)).replace "\n" " " ++ "\n" ++
          "def wildData : WildData := " ++ (reprStr d).replace "\n" " " ++ "\n" ++
          "theorem witness_valid : witness.Valid equation := by decide +kernel\n" ++
          "theorem wild_valid : wildData.Valid equation := by decide +kernel\n" ++
          "theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel\n" ++
          "theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=\n" ++
          "  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative\n" ++
          "theorem analytic_rank_at_least_one :\n" ++
          "    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=\n" ++
          "  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative\n"
        else if semistable then
          "theorem semistable : SemistableModel equation := by decide +kernel\n" ++
          "theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel\n" ++
          "theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=\n" ++
          "  central_zero_of_semistable_negative equation nonsingular semistable sign_negative\n" ++
          "theorem analytic_rank_at_least_one :\n" ++
          "    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=\n" ++
          "  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative\n"
        else
          "def witness : MinimalityWitness := " ++ (reprStr (witness.getD ⟨[]⟩)).replace "\n" " " ++ "\n" ++
          "theorem witness_valid : witness.Valid equation := by decide +kernel\n" ++
          "theorem tame : tameAtWild equation = true := by decide +kernel\n" ++
          "theorem sign_negative : tameSignFast equation = -1 := by decide +kernel\n" ++
          "theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=\n" ++
          "  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative\n" ++
          "theorem analytic_rank_at_least_one :\n" ++
          "    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=\n" ++
          "  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative\n"
        source := source ++ "namespace " ++ name ++ "\n" ++
          "def equation : Artifacts.CurveEquation := " ++ (reprStr e).replace "\n" " " ++ "\n" ++
          "theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel\n" ++
          proof ++ "end " ++ name ++ "\n\n"
        report := report ++ input.label ++ "\tanalytic-rank-at-least-one\n"
        count := count + 1
  source := source ++ s!"def certificateCount : Nat := {count}\nend VerifiedLcalc.Certificates.NegativeSigns\n"
  let path : System.FilePath := "VerifiedLcalc/Certificates/NegativeSigns.lean"
  let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == source) else pure false
  IO.FS.createDirAll "output/negative-signs"
  if !unchanged || args == ["--check"] then
    let checked : System.FilePath := "output/negative-signs/checked.tsv"
    if ← checked.pathExists then IO.FS.removeFile checked
  if !unchanged then IO.FS.writeFile path source
  IO.FS.writeFile "output/negative-signs/proposals.tsv" report
  if args == ["--check"] then
    let result ← IO.Process.output {cmd := "lake", args := #["build", "VerifiedLcalc.Certificates.NegativeSigns"]}
    IO.FS.writeFile "output/negative-signs/kernel-replay.log" (result.stdout ++ result.stderr)
    if result.exitCode != 0 then
      IO.eprintln "Negative-sign certificate replay failed."
      return 1
    let hash ← IO.Process.output {cmd := "shasum", args := #["-a", "256", path.toString]}
    if hash.exitCode != 0 then return 1
    IO.FS.writeFile "output/negative-signs/checked-source.sha256" hash.stdout
    IO.FS.writeFile "output/negative-signs/checked.tsv" report
    IO.println s!"{count} checked conditional lower bounds: analytic rank ≥ 1. No exact rank-one claims."
  else
    IO.println s!"{count} lower-bound candidates emitted; run with --check to verify them."
  return 0
