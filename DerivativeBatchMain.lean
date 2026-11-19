import VerifiedLcalc.EllipticCurve.DerivativeCore
import VerifiedLcalc.EllipticCurve.WildRootCore
import VerifiedLcalc.LmfdbSupplement
open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Untrusted candidate production only. The input projection discards reference
analytic ranks; every numerical, minimality and sign assertion is replayed. -/
def main : IO UInt32 := do
  IO.FS.createDirAll "VerifiedLcalc/Certificates/DerivativeBatch/Bundles"
  IO.FS.createDirAll "output/derivative"
  let mut groups : List (Nat × String) := []
  let mut numericalSources : List (DerivativeResult × String) := []
  let mut manifest := "label\tstatus\tmodule\tconductor\tequation\tbits\tterms\n"
  let mut count := 0
  let mut total := 0
  for input in Lmfdb.allCases.map (·.input) do
    let e := input.equation
    let primes := (List.range (input.conductor+1)).filter isPrime
    let some v := minimalityWitness? e primes | continue
    let some d := wildData? e | continue
    let ps := primes.filter (fun (p : Nat) => discriminant e % (p : Int) == 0)
    let (_,sign) := wildConductorRootFromPrimes e d ps
    if sign != -1 then continue
    total := total+1
    let mut chosen : Option DerivativeResult := none
    for (steps,cutoff) in [(1,8),(2,8),(1,16),(4,8),(2,16),(1,32),(8,8),(4,16),(2,32),(8,16),(4,32),(8,32),(16,32)] do
      for terms in [8,12,16,24,40] do
        if chosen.isNone then
          if let some r := evaluateDerivative e input.conductor terms steps cutoff then
            if r.box.excludesZero then chosen := some r
    if let some r := chosen then
      let short := "C" ++ input.label.replace "." "_"
      let ns := "VerifiedLcalc.Certificates.DerivativeBatch." ++ short
      let moduleName := "VerifiedLcalc.Certificates.DerivativeBatch.Bundles.N" ++ toString (input.conductor/32)
      let reused := numericalSources.find? (fun p => {p.1 with equation := r.equation} == r)
      let payloadProof := match reused with
        | none => "by decide +kernel\n"
        | some (_, previous) => "by\n  have h := " ++ previous ++ ".payload_correct\n" ++
            "  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩\n"
      numericalSources := numericalSources ++ [(r,ns)]
      let source := "\nnamespace " ++ ns ++ "\nopen VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions\n" ++
        "def result : DerivativeResult := " ++ (reprStr r).replace "\n" " " ++ "\n" ++
        "def minimality : MinimalityWitness := " ++ (reprStr v).replace "\n" " " ++ "\n" ++
        "def localData : WildData := " ++ (reprStr d).replace "\n" " " ++ "\n" ++
        "theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel\n" ++
        "theorem payload_correct : DerivativePayloadCorrect result := " ++ payloadProof ++
        "theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=\n" ++
        "  certifyDerivativeModel result nonsingular minimality (by decide +kernel)\n" ++
        "    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)\n" ++
        "def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩\n" ++
        "/-- info: '" ++ ns ++ ".analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/\n" ++
        "#guard_msgs (whitespace := lax) in\n#print axioms analytic_rank_one\nend " ++ ns ++ "\n"
      let bucket := input.conductor/32
      if groups.any (fun x => x.1 == bucket) then
        groups := groups.map (fun x => if x.1 == bucket then (x.1,x.2++source) else x)
      else groups := groups ++ [(bucket,source)]
      IO.FS.writeFile ("VerifiedLcalc/Certificates/DerivativeBatch/" ++ short ++ ".lean")
        ("module\npublic import " ++ moduleName ++ "\n")
      manifest := manifest ++ s!"{input.label}\tproposed\t{ns}\t{input.conductor}\t{(reprStr e).replace "\n" " "}\t{r.policy.precisionBits}\t{r.termLimit}\n"
      count := count+1
      IO.println s!"{input.label}: proposed exact rank one; steps={r.stepsPerUnit}; cutoff={r.cutoff}; terms={r.termLimit}"
    else
      manifest := manifest ++ s!"{input.label}\tderivative-interval-not-separated\t\t{input.conductor}\t{(reprStr e).replace "\n" " "}\t\t\n"
      IO.println s!"{input.label}: derivative inconclusive"
  for (bucket,body) in groups do
    let source := "module\npublic import VerifiedLcalc.Assumptions.DerivativeCertification\n@[expose] public section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nset_option pp.fullNames true\n" ++ body
    let path : System.FilePath := "VerifiedLcalc/Certificates/DerivativeBatch/Bundles/N" ++ toString bucket ++ ".lean"
    let unchanged ← if ← path.pathExists then pure ((← IO.FS.readFile path) == source) else pure false
    if !unchanged then IO.FS.writeFile path source
  IO.FS.writeFile "output/derivative/proposals.tsv" manifest
  IO.println s!"{count}/{total} negative-sign candidates; no rank-one claim is accepted before kernel replay."
  return 0
