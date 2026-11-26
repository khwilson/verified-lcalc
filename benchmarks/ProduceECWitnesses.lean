/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Certificate.Json
import VerifiedLcalc.Certificate.CurveDataJson

open Lean VerifiedLcalc VerifiedLcalc.EllipticCurve

/-! Explicit benchmark-only witness search. Its JSON output is untrusted input
for `certify_ec`; no theorem or certificate is produced by this executable.
The `--arithmetic` mode proposes evidence for one equation on stdout. -/

private def number (n : Int) : Json := .str (toString n)
private def natural (n : Nat) : Json := .str (toString n)
private def rational (q : Rat) : Json := .str s!"{q.num}/{q.den}"
private def interval (i : Rat × Rat) : Json := toJson [rational i.1, rational i.2]

private def tateJson : Option TateWitness → Json
  | none => .null
  | some w => Json.mkObj [
      ("r", number w.r), ("s", number w.s), ("t", number w.t),
      ("starT", number w.starT), ("cubicRoot", number w.cubicRoot),
      ("quadraticRoot", number w.quadraticRoot), ("chain", toJson (w.chain.map number)),
      ("kodaira", number w.kodaira)]

-- The witness checker verifies the full discriminant product for every candidate list.
private def proposeMinimality (e : WeierstrassCurve ℤ) (j : Json) : Option MinimalityWitness :=
  let badPrimes := (do
    let values ← j.getObjValAs? (Array Json) "bad_primes"
    values.toList.mapM CurveDataJson.nonnegativeInteger).toOption
  let hinted := badPrimes.bind fun ps => minimalityWitness? e ((ps.filter (1 < ·)).eraseDups)
  hinted.orElse fun _ =>
    let conductor := (j.getObjVal? "conductor" >>= CurveDataJson.nonnegativeInteger).toOption
    let hinted := conductor.bind fun n =>
      if n > 0 then minimalityWitness? e n.primeFactorsList.eraseDups else none
    hinted.orElse fun _ => minimalityWitness? e e.Δ.natAbs.primeFactorsList.eraseDups

-- Preserve every supported value so that the verifier still rejects a wrong coefficient.
private def partialNativeAp (e : WeierstrassCurve ℤ) (ainvs j : Json) : Option Json := do
  let values ← (j.getObjVal? "aplist").toOption
  let w ← (CurveDataJson.decode (Json.mkObj [("ainvs", ainvs), ("aplist", values)])).toOption
  let entries ← w.primeCoefficients
  let supported := entries.filter fun pa => modelMinimalAt e pa.1
  if supported.length == entries.length then none
  else some (toJson (supported.map fun (p, a) => [natural p, number a]))

private def proposeArithmetic (j : Json) : Except String Json := do
  let ainvs ← j.getObjVal? "ainvs"
  let e ← CurveDataJson.equationOfAinvs (← CurveDataJson.ainvs ainvs)
  if e.Δ = 0 then throw "singular_input"
  let m := proposeMinimality e j
  let (minimality, minimalityObligations) := match m with
    | some m => ([("minimality", toJson (m.primes.map natural))], ([] : List String))
    | none => ([], ["minimality_inconclusive"])
  let (localData, localObligations) := match wildData? e with
    | some d => ([("local_data", Json.mkObj
        [("at_two", tateJson d.atTwo), ("at_three", tateJson d.atThree)])],
        ([] : List String))
    | none => ([], ["wild_reduction_inconclusive"])
  let partialAp := if m.isNone then partialNativeAp e ainvs j else none
  let (coefficients, coefficientObligations) := match partialAp with
    | some ap => ([("ap", ap)], ["aplist_minimality_inconclusive"])
    | none => ([], [])
  return Json.mkObj [
    ("evidence", Json.mkObj (minimality ++ localData ++ coefficients)),
    ("obligations", toJson (minimalityObligations ++ localObligations ++ coefficientObligations))]

private def encodeWitness (w : EllipticWitness) : Except String Json := do
  let some m := w.minimality | throw "Missing minimality data"
  let some d := w.localData | throw "Missing local reduction data"
  let (e, N, bits, terms, steps, cutoff, cs, al, ah, tail, box, evaluator, m, d, rank) ←
    match w.centralResult, w.derivativeResult with
    | some r, none =>
      pure (r.equation, r.conductor, r.policy.precisionBits, r.termLimit, 0, 0,
       r.coefficients, r.alphaLo, r.alphaHi, r.tail, r.box,
       [("geometric_upper", rational r.geometricUpper)], m, d, "0")
    | none, some r =>
      pure (r.equation, r.conductor, r.policy.precisionBits, r.termLimit,
       r.stepsPerUnit, r.cutoff, r.coefficients, r.alphaLo, r.alphaHi, r.tail, r.box,
       [("finite", interval r.finite)], m, d, "1")
    | _, _ => throw "Expected exactly one numerical rank payload"
  return Json.mkObj [
    ("schema", .str "lcalc.ec-rank.v1"),
    ("subject", Json.mkObj [
      ("ainvs", toJson ([e.a₁, e.a₂, e.a₃, e.a₄, e.a₆].map number)),
      ("conductor", natural N)]),
    ("parameters", Json.mkObj [
      ("precision_bits", natural bits), ("terms", natural terms),
      ("steps_per_unit", natural steps), ("cutoff", natural cutoff)]),
    ("rank", .str rank), ("coefficients", toJson (cs.map number)),
    ("arithmetic", Json.mkObj [
      ("minimality", toJson (m.primes.map natural)),
      ("at_two", tateJson d.atTwo), ("at_three", tateJson d.atThree)]),
    ("enclosure", Json.mkObj [
      ("real", interval (box.reLo, box.reHi)), ("imag", interval (box.imLo, box.imHi))]),
    ("evaluator", Json.mkObj
      ([("alpha", interval (al, ah)), ("tail", rational tail)] ++ evaluator))]

private def propose (e : WeierstrassCurve ℤ) (N : Nat) : Except String EllipticWitness := do
  if e.Δ = 0 then throw "singular_input"
  let ps := N.primeFactorsList.eraseDups
  let some m := minimalityWitness? e ps | throw "minimality_inconclusive"
  let some d := wildData? e | throw "wild_reduction_inconclusive"
  let (level, sign) := wildConductorRootFromPrimes e d ps
  unless level == N do throw "conductor_mismatch"
  if sign = 1 then
    for terms in [4, 8, 16, 24, 32, 48, 64, 96, 128] do
      if let some r := evaluateCentral e N sign terms then
        if r.box.excludesZero then return .central r m d
    throw "central_enclosure_inconclusive"
  else if sign = -1 then
    for (terms, steps, cutoff) in
        [(24, 1, 8), (32, 1, 12), (48, 1, 16), (64, 2, 16), (96, 4, 24), (128, 8, 32)] do
      if let some r := evaluateDerivative e N terms steps cutoff then
        if r.box.excludesZero then return .derivative r m d
    throw "derivative_enclosure_inconclusive"
  else throw "root_number_inconclusive"

private def parseInput (j : Json) : Except String (String × WeierstrassCurve ℤ × Nat) := do
  let label ← j.getObjValAs? String "label"
  let N ← j.getObjValAs? Nat "conductor"
  let a ← j.getObjValAs? (Array Int) "ainvs"
  unless a.size == 5 do throw "Expected five Weierstrass coefficients"
  return (label, ⟨a[0]!, a[1]!, a[2]!, a[3]!, a[4]!⟩, N)

/-- Propose arithmetic evidence on stdout or write rank benchmark witnesses to a directory. -/
def main (args : List String) : IO UInt32 := do
  if let ["--arithmetic", input] := args then
    let raw ← IO.FS.readFile input
    let evidence ← IO.ofExcept ((Json.parse raw).bind proposeArithmetic)
    IO.println evidence.compress
    return 0
  let [input, output] := args |
    throw (IO.userError "Usage: INPUT.json OUTPUT_DIR | --arithmetic INPUT.json")
  IO.FS.createDirAll output
  let raw ← IO.FS.readFile input
  let entries ← IO.ofExcept do
    let j ← Json.parse raw
    j.getObjValAs? (Array Json) "inputs"
  let stdout ← IO.getStdout
  for i in [:entries.size] do
    let (label, e, N) ← IO.ofExcept (parseInput entries[i]!)
    let start ← IO.monoNanosNow
    let result := propose e N
    -- Force the untrusted search before recording elapsed time.
    let encoded := match result with
      | .ok w => (encodeWitness w).map (fun j => (w, j))
      | .error reason => Except.error reason
    let report ← match encoded with
      | .error reason => pure (Json.mkObj [
          ("index", toJson i), ("label", .str label), ("status", .str "inconclusive"),
          ("reason", .str reason)])
      | .ok (w, j) => do
        -- Serializer regression only; mathematical validation is a separate process.
        match CertificateJson.decode j with
        | .error reason => pure (Json.mkObj [
            ("index", toJson i), ("label", .str label), ("status", .str "generation_error"),
            ("reason", .str ("witness_encoding_error: " ++ reason))])
        | .ok decoded =>
          if decoded != w then
            pure (Json.mkObj [
              ("index", toJson i), ("label", .str label), ("status", .str "generation_error"),
              ("reason", .str "witness_serializer_round_trip_mismatch")])
          else do
            let file := s!"{i}.json"
            IO.FS.writeFile (System.FilePath.mk output / file) (j.compress ++ "\n")
            pure (Json.mkObj [
              ("index", toJson i), ("label", .str label), ("status", .str "proposed"),
              ("file", .str file), ("conductor", toJson N),
              ("rank", ← IO.ofExcept (j.getObjValAs? String "rank")),
              ("parameters", ← IO.ofExcept (j.getObjVal? "parameters"))])
    let elapsed := (← IO.monoNanosNow) - start
    let report := Json.mkObj [("result", report), ("generation_ns", toJson elapsed)]
    stdout.putStrLn report.compress
    stdout.flush
  return 0
