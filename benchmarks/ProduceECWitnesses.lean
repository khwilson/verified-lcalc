/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Certificate.Json
import VerifiedLcalc.Certificate.CurveDataJson
import VerifiedLcalc.EllipticCurve.TorsionBound
import VerifiedLcalc.EllipticCurve.TwoFactorTorsion
import VerifiedLcalc.Verification.CurveData
import VerifiedLcalc.Verification.AbcQuality

/-! Explicit benchmark-only witness search. Its JSON output is untrusted input
for `certify_ec`; no theorem or certificate is produced by this executable.
The `--arithmetic` mode proposes evidence for one equation on stdout. -/

open Lean VerifiedLcalc VerifiedLcalc.EllipticCurve

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

-- Factor the same integer used by the verifier. Preserve the reported center,
-- including when its asserted radius will fail verification.
private def proposeAbcQuality (e : WeierstrassCurve ℤ) (j : Json) :
    Except String (List (String × Json) × List String) := do
  let .ok claim := j.getObjVal? "abc_quality" | return ([], [])
  if claim == .null then return ([], [])
  let invariant := Certification.abcJ e
  if invariant = 0 || invariant = 1728 then
    return ([], ["abc_quality_undefined"])
  let _ ← CurveDataJson.exactReportedDecimal claim
  let product := Certification.abcProduct invariant
  -- Mathlib uses trial division. Leave larger products for supplied evidence.
  if product > 10 ^ 12 then
    return ([], ["abc_quality_factorization_inconclusive"])
  let factors := product.primeFactorsList
  return ([("abc_quality_evidence", Json.mkObj [
    ("error", rational (1 / 10 ^ 12)), ("factors", toJson (factors.map natural))])], [])

-- Retain a single pair with the smallest positive gcd of the reduced point counts.
private def proposeTorsionBound (e : WeierstrassCurve ℤ) : Option TorsionBoundWitness := Id.run do
  let primes := ((List.range 100).drop 3).filter fun p => isPrime p && goodReduction e p
  let counts := primes.map fun p => (p, computePointCount e p)
  let mut best : Option TorsionBoundWitness := none
  for (p, a) in counts do
    for (q, b) in counts do
      if p < q then
        let bound := a.gcd b
        if bound > 0 && best.all (fun w => bound < w.bound) then
          if bound == 1 then return some ⟨p, q, bound⟩
          best := some ⟨p, q, bound⟩
  return best

private def torsionPoint? (W : WeierstrassCurve ℚ) [W.IsElliptic] (xy : Rat × Rat) :
    Option W.toAffine.Point :=
  if h : EllipticWitness.affineCoordinatesValid W [xy] = true then
    some (.mk (EllipticWitness.affineCoordinatesValid_sound W [xy] h xy.1 xy.2 (by simp)))
  else none

private def proposeTorsion (e : WeierstrassCurve ℤ) (hne : e.Δ ≠ 0) (j : Json) :
    List (String × Json) × List String := Id.run do
  let present := fun field => ((j.getObjVal? field).toOption.filter (· != .null)).isSome
  let cardinalityRequested := ["torsion", "torsion_structure", "torsion_primes",
    "intrinsic_torsion"].any present
  let generatorsRequested := present "torsion_generators"
  if !cardinalityRequested && !generatorsRequested then return ([], [])
  let W := e.baseChange ℚ
  letI : W.IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (e.Δ : ℚ) ≠ 0 by exact_mod_cast hne)⟩
  let points := (j.getObjVal? "torsion_generators" >>= CurveDataJson.weightedCoordinates).toOption
    |>.bind (·.mapM (torsionPoint? W))
  let bound := proposeTorsionBound e
  let candidates := ((List.range 257).drop 1).filter fun n =>
    bound.all fun b => b.bound % n == 0
  let orders := points.bind (·.mapM fun point =>
    candidates.find? (EllipticWitness.exactOrderCheck point))
  let boundEvidence := bound.toList.map fun b => ("torsion_bound", Json.mkObj
    [("first_prime", natural b.firstPrime), ("second_prime", natural b.secondPrime),
     ("bound", natural b.bound)])
  let orderEvidence := orders.toList.map fun ns =>
    ("torsion_generator_orders", toJson (ns.map natural))
  let factors := (do
    let xs ← j.getObjValAs? (Array Json) "torsion_structure"
    xs.toList.mapM CurveDataJson.nonnegativeInteger).toOption
  let claimedOrder := (j.getObjVal? "torsion" >>= CurveDataJson.nonnegativeInteger).toOption
    |>.orElse (fun _ => factors.map List.prod)
  let trivial := (bound.map (·.bound)) == some 1
  let exact := trivial || (match bound, claimedOrder, orders, points with
    | some b, some n, some (k :: ks), some (P :: Qs) =>
      b.bound == n && (k == n ||
        (match ks, Qs with
        | l :: _, Q :: _ => factors == some [2, l] && l % 2 == 0 &&
            k == 2 && n == 2 * l && outsideCyclicCheck P Q l
        | _, _ => false))
    | _, _, _, _ => false)
  let obligations := (if bound.isNone then ["torsion_bound_inconclusive"] else []) ++
    (if generatorsRequested && orders.isNone
      then ["torsion_generator_orders_inconclusive"] else []) ++
    (if !exact then ["torsion_presentation_inconclusive"] else []) ++
    (if present "intrinsic_torsion" && !trivial then ["intrinsic_torsion_inconclusive"] else [])
  return (boundEvidence ++ orderEvidence, obligations)

private def proposeArithmetic (j : Json) : Except String Json := do
  let ainvs ← j.getObjVal? "ainvs"
  let e ← CurveDataJson.equationOfAinvs (← CurveDataJson.ainvs ainvs)
  if h : e.Δ = 0 then throw "singular_input" else
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
  let (abcQuality, abcObligations) ← proposeAbcQuality e j
  let (torsion, torsionObligations) := proposeTorsion e h j
  return Json.mkObj [
    ("evidence", Json.mkObj (minimality ++ localData ++ coefficients ++ abcQuality ++ torsion)),
    ("obligations", toJson
      (minimalityObligations ++ localObligations ++ coefficientObligations ++ abcObligations ++
        torsionObligations))]

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

-- The last displayed decimal place determines the requested rounding tolerance.
private def displayedHalfUnit (j : Json) : Except String Rat := do
  let text ← match j with
    | .str s => pure s
    | .obj _ => j.getObjValAs? String "data"
    | _ =>
      let number ← j.getNum?
      return 1 / (2 * (10 : Rat) ^ number.exponent)
  let (digits, power) ← match text.toLower.splitOn "e" with
    | [digits] => pure (digits, (0 : Int))
    | [digits, exponent] =>
      let exponent := if exponent.startsWith "+" then exponent.drop 1 |>.toString else exponent
      let some power := exponent.toInt? | throw "Invalid reported decimal exponent"
      unless power.natAbs ≤ 512 do throw "Oversized reported decimal exponent"
      pure (digits, power)
    | _ => throw "Invalid reported decimal"
  let places := match digits.splitOn "." with
    | [_, fractional] => fractional.length
    | _ => 0
  let scale := power - (places : Int)
  return if scale < 0 then 1 / (2 * (10 : Rat) ^ scale.natAbs)
    else (10 : Rat) ^ scale.natAbs / 2

private def proposeSpecialValue (j : Json) (w : EllipticWitness) :
    Except String (List (String × Json) × List String) := do
  let some raw := CurveDataJson.optionalData j "special_value" | return ([], [])
  let reported ← CurveDataJson.exactReportedDecimal raw
  let halfUnit ← displayedHalfUnit raw
  let (lo, hi) ← match w.centralResult, w.derivativeResult with
    | some r, none => pure (r.box.reLo, r.box.reHi)
    | none, some r => pure r.realDerivativeBounds
    | _, _ => throw "Expected exactly one rank-zero or rank-one enclosure"
  -- Both supported Taylor coefficients have factorial one.
  let radius := max |lo - reported| |hi - reported|
  let disjoint := decide (reported + halfUnit < lo ∨ hi < reported - halfUnit)
  let (error, obligations) :=
    if disjoint then (halfUnit, ["special_value_disagrees_with_enclosure"])
    else if radius > halfUnit then (radius, ["special_value_precision_inconclusive"])
    else (radius, [])
  return ([("special_value_evidence", Json.mkObj [("error", rational error)])], obligations)

private def proposeNativeAnalytic (j : Json) :
    Except String (List (String × Json) × List String) := do
  if (CurveDataJson.optionalData j "analytic_rank").isNone &&
      (CurveDataJson.optionalData j "special_value").isNone then return ([], [])
  let e ← CurveDataJson.equation j
  let some rawConductor := CurveDataJson.optionalData j "conductor" |
    return ([], ["analytic_witness_requires_conductor"])
  let conductor ← CurveDataJson.nonnegativeInteger rawConductor
  -- Search the equation's independently computed sign; the native ranks are never used.
  match propose e conductor with
  | .error reason => return ([], ["analytic_witness_inconclusive:" ++ reason])
  | .ok witness => do
    let rank ← encodeWitness witness
    let (specialEvidence, obligations) ← proposeSpecialValue j witness
    return (("analytic_witness", rank) :: specialEvidence, obligations)

private def proposeSingleCurve (j : Json) : Except String Json := do
  let arithmetic ← proposeArithmetic j
  let (analytic, analyticObligations) ← proposeNativeAnalytic j
  let evidence ← (← arithmetic.getObjVal? "evidence").getObj?
  let obligations ← arithmetic.getObjValAs? (List String) "obligations"
  return Json.mkObj [
    ("evidence", Json.mkObj (evidence.toList ++ analytic)),
    ("obligations", toJson (obligations ++ analyticObligations))]

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
    let evidence ← IO.ofExcept ((Json.parse raw).bind proposeSingleCurve)
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
