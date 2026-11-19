import Lean.Data.Json
import VerifiedLcalc.Regression
import VerifiedLcalc.EllipticCurve.DerivativeCore
import VerifiedLcalc.EllipticCurve.WildRootCore
open Lean VerifiedLcalc VerifiedLcalc.EllipticCurve

private def parseInput (j : Json) : Except String Regression.CurveInput := do
  let label ← j.getObjValAs? String "label"
  let N ← j.getObjValAs? Nat "conductor"
  let a ← (← j.getObjVal? "ainvs").getArr?
  if a.size != 5 then throw "Expected five integral Weierstrass coefficients"
  return ⟨label,N,← a[0]!.getInt?,← a[1]!.getInt?,← a[2]!.getInt?,← a[3]!.getInt?,← a[4]!.getInt?⟩

private def flat [Repr α] (x : α) : String := (reprStr x).replace "\n" " "
private def audit (ns name : String) : String := "\n#print axioms " ++ ns ++ "." ++ name ++ "\n"
private def addComponent (ns name statement proof : String) : String :=
  "theorem " ++ name ++ " : " ++ statement ++ " := " ++ proof ++ "\n" ++ audit ns name

/-- Untrusted candidate production. The JSON reader consumes `inputs` only;
reference ranks are stored in a different file and are unavailable here. -/
def main (args : List String) : IO UInt32 := do
  let [inputPath, conductorText, moduleName, outputDir] := args
    | IO.eprintln "Usage: conductor-certificates INPUTS.json CONDUCTOR MODULE OUTPUT_DIR"; return 2
  let some N := conductorText.toNat? | return 2
  if N == 0 || !(moduleName.startsWith "VerifiedLcalc.Certificates.ConductorRuns.") ||
      !(moduleName.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then return 2
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile inputPath))
  let records ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "inputs")).getArr?)
  let inputs ← IO.ofExcept (records.toList.mapM parseInput)
  let cases := inputs.filter (·.conductor == N)
  if cases.isEmpty then throw (IO.userError "Conductor has no inputs")
  if (cases.map (·.label)).eraseDups.length != cases.length then throw (IO.userError "Duplicate inputs")
  let start ← IO.monoMsNow
  let mut source := "module\npublic import VerifiedLcalc.Assumptions.DerivativeCertification\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nset_option pp.fullNames true\n"
  let mut rows : List Json := []
  let mut numericSources : List (DerivativeResult × String) := []
  let primes := (List.range (N+1)).filter isPrime
  for input in cases do
    let curveStart ← IO.monoMsNow
    let e := input.equation
    let ns := moduleName ++ ".C" ++ input.label.replace "." "_"
    let mut components : List String := ["nonsingular"]
    source := source ++ "\nnamespace " ++ ns ++ "\nopen VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions\n" ++
      "def equation : Artifacts.CurveEquation := " ++ flat e ++ "\n" ++
      "def label : String := " ++ reprStr input.label ++ "\ndef inputConductor : Nat := " ++ toString N ++ "\n" ++
      addComponent ns "nonsingular" "discriminant equation ≠ 0" "by decide +kernel"
    let v := minimalityWitness? e primes
    let d := wildData? e
    let mut status := "minimality-unresolved"
    let mut rank : Option Nat := none
    let mut lower : Option Nat := none
    let mut bits : Option Nat := none
    let mut terms : Option Nat := none
    let mut steps : Option Nat := none
    let mut cutoff : Option Nat := none
    if let some w := v then
      source := source ++ "def minimality : MinimalityWitness := " ++ flat w ++ "\n" ++
        addComponent ns "minimality_valid" "minimality.Valid equation" "by decide +kernel" ++
        addComponent ns "globally_minimal" "GloballyMinimalInput equation" "minimal_of_witness equation minimality minimality_valid"
      components := components ++ ["minimality_valid","globally_minimal"]
      status := "wild-transcript-unresolved"
    if let some localWitness := d then
      source := source ++ "def localData : WildData := " ++ flat localWitness ++ "\n" ++
        addComponent ns "local_data_valid" "localData.Valid equation" "by decide +kernel"
      components := components ++ ["local_data_valid"]
      let badPrimes := primes.filter (fun (p : Nat) => discriminant e % (p : Int) == 0)
      let (level,sign) := wildConductorRootFromPrimes e localWitness badPrimes
      source := source ++ addComponent ns "conductor_formula" ("wildLevel equation localData = " ++ toString level)
        "(wildLevel_eq_fast equation localData).trans (by decide +kernel)" ++
        addComponent ns "root_formula" ("wildSign equation localData = " ++ flat sign)
        "(wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)"
      components := components ++ ["conductor_formula","root_formula"]
      if v.isSome then
        status := if level != N then "conductor-mismatch" else "interval-not-separated"
        if sign == -1 then
          source := source ++ addComponent ns "rank_lower_bound"
            "1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ)"
            "rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)"
          components := components ++ ["rank_lower_bound"]
          lower := some 1
        if level == N then
          if sign == 1 then
            let mut result : Option CentralResult := none
            for b in [53,80,106] do
              for M in [1,2,3,4,6,8,12,16,24,32,48,64,96,128] do
                if result.isNone then
                  if let some r := evaluateCentral e N 1 M ⟨b⟩ then
                    if r.box.excludesZero then result := some r
            if let some r := result then
              let rem := (squareTailBound r.geometricUpper r.termLimit).getD 0
              source := source ++ "def result : CentralResult := " ++ flat r ++ "\n" ++
                addComponent ns "payload_correct" "CentralPayloadCorrect result"
                  ("by\n  unfold CentralPayloadCorrect\n  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, " ++ flat rem ++ ", by decide +kernel, by decide +kernel, by decide +kernel⟩") ++
                addComponent ns "analytic_rank" "analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0"
                  "certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)"
              components := components ++ ["payload_correct","analytic_rank"]
              rank := some 0; bits := some r.policy.precisionBits; terms := some r.termLimit
              status := "proposed-exact-rank-zero"
          else if sign == -1 then
            let mut result : Option DerivativeResult := none
            for (s,T) in [(1,8),(2,8),(1,16),(4,8),(2,16),(1,32),(8,8),(4,16),(2,32),(1,64),(8,16),(4,32),(2,64),(8,32),(4,64),(16,32)] do
              for M in [8,12,16,24,40,64,96,128] do
                if result.isNone then
                  if let some r := evaluateDerivative e N M s T then
                    if r.box.excludesZero then result := some r
            if let some r := result then
              let reused := numericSources.find? (fun p => {p.1 with equation := e} == r)
              let proof := match reused with
                | none => "by decide +kernel"
                | some (_,prev) => "by\n  have h := " ++ prev ++ ".payload_correct\n  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩"
              numericSources := numericSources ++ [(r,ns)]
              source := source ++ "def result : DerivativeResult := " ++ flat r ++ "\n" ++
                addComponent ns "payload_correct" "DerivativePayloadCorrect result" proof ++
                addComponent ns "analytic_rank" "analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1"
                  "certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)"
              components := components ++ ["payload_correct","analytic_rank"]
              rank := some 1; bits := some r.policy.precisionBits; terms := some r.termLimit
              steps := some r.stepsPerUnit; cutoff := some r.cutoff
              status := "proposed-exact-rank-one"
    if v.isSome then
      let M := terms.getD 8
      source := source ++ addComponent ns "coefficients_correct"
        ("modelCoefficients equation " ++ toString M ++ " = (List.range " ++ toString M ++ ").map (fun j => (weierstrass equation ℚ).LFunction (j+1))")
        ("minimal_prefix equation nonsingular globally_minimal " ++ toString M)
      components := components ++ ["coefficients_correct"]
    source := source ++ "end " ++ ns ++ "\n"
    rows := rows ++ [Json.mkObj [("label",toJson input.label),("conductor",toJson N),
      ("equation",toJson (flat e)),("namespace",toJson ns),("status",toJson status),
      ("proposed_rank",toJson rank),("lower_bound",toJson lower),("bits",toJson bits),
      ("terms",toJson terms),("steps",toJson steps),("cutoff",toJson cutoff),
      ("components",toJson components),("producer_milliseconds",toJson ((← IO.monoMsNow)-curveStart))]]
  let sourcePath : System.FilePath := moduleName.replace "." "/" ++ ".lean"
  if let some parent := sourcePath.parent then IO.FS.createDirAll parent
  let same ← if ← sourcePath.pathExists then pure ((← IO.FS.readFile sourcePath) == source) else pure false
  if !same then IO.FS.writeFile sourcePath source
  IO.FS.createDirAll outputDir
  IO.FS.writeFile (System.FilePath.mk outputDir / "proposals.json")
    ((Json.mkObj [("module",toJson moduleName),("conductor",toJson N),
      ("producer_milliseconds",toJson ((← IO.monoMsNow)-start)),("cases",toJson rows)]).pretty ++ "\n")
  return 0
