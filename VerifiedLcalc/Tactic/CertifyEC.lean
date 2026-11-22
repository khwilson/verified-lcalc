module

public import VerifiedLcalc.Certification.DerivativeCertification
public import VerifiedLcalc.Tactic.CertifyECData
public import VerifiedLcalc.Tactic.CertifyECPoints
public import VerifiedLcalc.Tactic.CertifyECInvariants
public meta import Lean

/-!
# Certify optional elliptic-curve facts

Every input method uses one `EllipticWitness` record. The integral
`WeierstrassCurve` equation is required. Prime coefficients, integer coordinates,
central or derivative rank payloads, minimality, and local-reduction data are
`Option` fields defaulting to `none`. `infiniteOrderPoints` requests exact
infinite-order checks at supplied point indices; `independentPoints` selects
an algebraic-rank family and requires a `with_independence proof` clause.
This clause is available for all three input forms and the programmatic API.
`none` is absence; `some []` is an explicit empty list and makes no completeness
claim. `EllipticWitness.central` and
`.derivative` are convenience functions returning this same record.

* `certify_ec Name from witness` accepts direct Lean records or definitions.
* `certify_ec Name from_json "file.json"` reads relative to the containing source.
* `certify_ec Name from_json_string "..."` accepts inline exact JSON.

All three forms, and `CertifyEC.certify` / `certifyAtomic`, use the same checker.
Optional stored invariants include b/c values, equation discriminant and sign,
j-invariant and its integrality, everywhere potential good reduction, minimal absolute
discriminant, bad-prime set/count, anlist, conductor and global root number.
Prerequisite-dependent claims without the required evidence are reported as unverified. See
`docs/LMFDB_INVARIANTS.md` for the exact mathematical outputs and trust boundary.
JSON can supply `ainvs`, `ap` or `aplist`, and `integral_points` or
`xcoord_integral_points`; unrelated metadata carries no claim. The legacy rank
JSON layout is decoded into the same flat record. Bare stored ranks never
become theorems. A caller controls any computation inside a supplied Lean term;
the certifier performs no analytic-witness search or network requests.

## Point and algebraic-rank output

An infinite-order request produces `Name.infinite_order_indices` and
`Name.infiniteOrder.point0`, `.point1`, …, each with an `infinite_order` theorem
about its actual supplied point. A nonempty list also gives
`Name.algebraic_rank_lower_bound` proving rank at least one.

An independence request produces `Name.algebraic.indices`, `.points`, and
`.points_independent`. Its supplied proof is checked against
`LinearIndependent ℤ Name.algebraic.points`. The root
`Name.algebraic_rank_lower_bound` then uses this family's size. These facts
need only standard Lean axioms. A failure in any component rolls back the
whole `certify_ec` command. No separate public point/rank command is needed.

## Output

`Name.witness` has type `EllipticWitness`; `Name.supplied` aliases that record
for every input. `Name.curve` and `Name.nonsingular` identify its integral model.
The arithmetic theorems `prime_coefficients_valid`, `ap_correct`,
`integral_coordinates_valid`, and `points_on_curve` quantify over the supplied
lists (`getD []` when absent). `point i` and `point_integral i` construct the
corresponding rational points in TauCeti's `curve.integralPoints`. Neither list
certifies completeness or algebraic rank.

When supplied, minimality and local data produce their named definitions,
`minimality_eq` / `local_data_eq`, and `minimality_valid` / `local_data_valid`.
A numerical payload produces `result`, `witness_eq`, `result_curve_eq`,
`payload_correct`, and `excludes_zero`. Both rank-zero and rank-one candidates
in the same input are rejected. Missing arithmetic witnesses are reported;
the numeric checks alone do not produce an analytic-rank theorem.

With a complete candidate the command additionally checks `conductor_valid`
and `root_number_valid`, then exports `analytic_rank`, `curve_analytic_rank`,
and the proof-carrying `certifiedRank`. They assert exact order zero or one at
`1` for `(Modularity.modularWitness Name.curve Name.nonsingular).formL`.
These analytic facts retain the explicit `ellipticModularity` assumption;
arithmetic and numeric checks allow only standard Lean axioms.

Finite checks use `decide +kernel`, every theorem's dependencies are audited,
and failures roll back all generated declarations. Compilation stores ordinary
importable theorems in the containing module's `.olean`. Use a `public section`
with Lean's `module` syntax to export them. See `examples/certify_ec/` and the
compiled consumers under `tests/consumers/`.
-/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve NumberField

/-- Independently check supplied arithmetic witnesses, even without rank data. -/
def certifyLocalData (base : Name) : CommandElabM Unit := do
  let w := rootIdent (base ++ `witness)
  let curve := rootIdent (base ++ `curve)
  if let some input ← optionalInput (base ++ `witness) `minimality then
    let m := rootIdent (base ++ `minimality)
    emit (← `(def $m : MinimalityWitness := $input))
    checked (base ++ `minimality_eq) (← `(($w).minimality = some $m)) (← `(by rfl))
    checked (base ++ `minimality_valid) (← `(($m).Valid $curve)) (← `(by decide +kernel))
    let hm := rootIdent (base ++ `minimality_valid)
    checked (base ++ `global_minimal)
      (← `(WeierstrassCurve.IsGlobalMinimal (NumberField.RingOfIntegers ℚ)
        (($curve).baseChange ℚ)))
      (← `(globalMinimal_of_witness $curve $m $hm))
  if let some input ← optionalInput (base ++ `witness) `localData then
    let d := rootIdent (base ++ `localData)
    emit (← `(def $d : WildData := $input))
    checked (base ++ `local_data_eq) (← `(($w).localData = some $d)) (← `(by rfl))
    checked (base ++ `local_data_valid) (← `(($d).Valid $curve)) (← `(by decide +kernel))

/-- Verify the supplied numerical candidate; derive rank only when all of its
arithmetic prerequisites were supplied and checked. -/
def certifyAnalytic (base : Name) (central : Bool) (input : TSyntax `term) : CommandElabM Unit := do
  let w := rootIdent (base ++ `witness)
  let curve := rootIdent (base ++ `curve)
  let hn := rootIdent (base ++ `nonsingular)
  let r := rootIdent (base ++ `result)
  if central then emit (← `(def $r : CentralResult := $input))
  else emit (← `(def $r : DerivativeResult := $input))
  let binding ← if central then `(($w).centralResult = some $r)
    else `(($w).derivativeResult = some $r)
  checked (base ++ `witness_eq) binding (← `(by rfl))
  checked (base ++ `result_curve_eq) (← `(($r).equation = $curve)) (← `(by rfl))
  let hp := rootIdent (base ++ `payload_correct)
  let finiteCheck ← `(by dsimp only [$r:term]; decide +kernel)
  if central then
    checked (base ++ `payload_correct) (← `(CentralPayloadCorrect $r)) (← `(by
      unfold CentralPayloadCorrect
      exact ⟨$finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck,
        (squareTailBound ($r).geometricUpper ($r).termLimit).getD 0,
        $finiteCheck, $finiteCheck, $finiteCheck⟩))
  else
    checked (base ++ `payload_correct) (← `(DerivativePayloadCorrect $r)) (← `(by
      unfold DerivativePayloadCorrect
      exact ⟨$finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck⟩))
  let hz := rootIdent (base ++ `excludes_zero)
  checked (base ++ `excludes_zero) (← `(($r).box.excludesZero = true)) (← `(by decide +kernel))
  let minimality ← optionalInput (base ++ `witness) `minimality
  let localData ← optionalInput (base ++ `witness) `localData
  unless minimality.isSome && localData.isSome do
    logInfo m!"Verified {base}.payload_correct; no analytic rank without minimality and local data"
    return
  let m := rootIdent (base ++ `minimality)
  let hm := rootIdent (base ++ `minimality_valid)
  let d := rootIdent (base ++ `localData)
  let hd := rootIdent (base ++ `local_data_valid)
  let hN := rootIdent (base ++ `conductor_valid)
  checked (base ++ `conductor_valid) (← `(wildLevelFast $curve $d = ($r).conductor))
    (← `(by decide +kernel))
  let hw := rootIdent (base ++ `root_number_valid)
  let sign ← if central then `(($r).rootNumber) else `((-1 : Int))
  checked (base ++ `root_number_valid) (← `(wildSignFast $curve $d = $sign))
    (← `(by decide +kernel))
  let rank : TSyntax `term ← if central then `(0) else `(1)
  let rankType ← `(analyticOrderAt
    (Modularity.modularWitness $curve $hn).formL (1 : ℂ) = $rank)
  let proof ← if central then
    `(Certification.certifyWildCentralModel $r $hn $m $hm $d $hd $hN $hw $hp $hz)
    else `(Certification.certifyDerivativeModel $r $hn $m $hm $d $hd $hN $hw $hp $hz)
  checked (base ++ `analytic_rank) rankType proof true
  let rankTheorem := rootIdent (base ++ `analytic_rank)
  checked (base ++ `curve_analytic_rank) rankType (← `($rankTheorem)) true
  let certifiedRank := rootIdent (base ++ `certifiedRank)
  emit (← `(def $certifiedRank : {n : Nat // analyticOrderAt
    (Modularity.modularWitness $curve $hn).formL (1 : ℂ) = n} := ⟨$rank, $rankTheorem⟩))
  logInfo m!"Certified {base}.analytic_rank; conditional on ellipticModularity"

/-- Dispatch point facts from the same witness as all other curve data. -/
def certifyPointFields (name : Name) (independence : Option (TSyntax `term)) :
    CommandElabM Unit := do
  let name := name.eraseMacroScopes
  let base := (← getCurrNamespace) ++ name
  let curve := rootIdent (base ++ `curve)
  let witness := rootIdent (base ++ `witness)
  let mut firstInfinite : Option Name := none
  if let some input ← optionalInput (base ++ `witness) `infiniteOrderPoints then
    let ix := rootIdent (base ++ `infinite_order_indices)
    emit (← `(def $ix : List Nat := $input))
    checked (base ++ `infinite_order_points_eq)
      (← `(($witness).infiniteOrderPoints = some $ix)) (← `(by rfl))
    let count ← liftTermElabM do
      let size ← Term.elabTerm (← `(($ix).length)) (some (mkConst ``Nat))
      let some n ← (evalNat (← whnf size)).run
        | throwError "Expected closed infinite-order point indices"
      return n
    let countTerm : TSyntax `term := ⟨Syntax.mkNumLit (toString count)⟩
    checked (base ++ `infinite_order_count_eq) (← `(($ix).length = $countTerm))
      (← `(by decide +kernel))
    for i in [:count] do
      let position : TSyntax `term := ⟨Syntax.mkNumLit (toString i)⟩
      let index ← `(($ix)[$position]'(by decide +kernel))
      let child := name ++ `infiniteOrder ++ Name.mkSimple s!"point{i}"
      certifyInfiniteOrder child (rootIdent base) index
      if firstInfinite.isNone then firstInfinite := some ((← getCurrNamespace) ++ child)
  if let some indices ← optionalInput (base ++ `witness) `independentPoints then
    let some proof := independence
      | throwError "independentPoints requires a with_independence proof"
    certifyRankLowerBound (name ++ `algebraic) (rootIdent base) indices proof
    let ix := rootIdent (base ++ `algebraic ++ `indices)
    checked (base ++ `independent_points_eq)
      (← `(($witness).independentPoints = some $ix)) (← `(by rfl))
    let h := rootIdent (base ++ `algebraic ++ `algebraic_rank_lower_bound)
    checked (base ++ `algebraic_rank_lower_bound)
      (← `((($ix).length : Cardinal) ≤ Module.rank ℤ (($curve).baseChange ℚ).toAffine.Point))
      (← `($h))
  else
    if independence.isSome then
      throwError "with_independence requires independentPoints in the supplied witness"
    if let some child := firstInfinite then
      let h := rootIdent (child ++ `algebraic_rank_lower_bound)
      checked (base ++ `algebraic_rank_lower_bound)
        (← `((1 : Cardinal) ≤ Module.rank ℤ (($curve).baseChange ℚ).toAffine.Point)) (← `($h))

/-- The single verification path for all input methods. -/
def certifyFields (name : Name) (input : TSyntax `term)
    (independence : Option (TSyntax `term) := none) : CommandElabM Unit := do
  let name := name.eraseMacroScopes
  let base := (← getCurrNamespace) ++ name
  CertifyECData.certify name input false
  let w := rootIdent (base ++ `witness)
  let supplied := rootIdent (base ++ `supplied)
  emit (← `(def $supplied : EllipticWitness := $w))
  let central ← optionalInput (base ++ `witness) `centralResult
  let derivative ← optionalInput (base ++ `witness) `derivativeResult
  if central.isSome && derivative.isSome then
    throwError "Conflicting rank candidates: supply at most one central or derivative result"
  certifyPointFields name independence
  certifyLocalData base
  certifyStoredInvariants base
  if let some result := central then certifyAnalytic base true result
  if let some result := derivative then certifyAnalytic base false result
  logInfo m!"Certified {base}.ap_correct and {base}.point_integral for the supplied lists"

/-- Programmatic entry point; failed components leave no declarations behind. -/
def certify (name : Name) (input : TSyntax `term)
    (independence : Option (TSyntax `term) := none) : CommandElabM Unit :=
  atomic (certifyFields name input independence)

/-- Run the programmatic certificate check with atomic declaration emission. -/
def certifyAtomic (name : Name) (input : TSyntax `term)
    (independence : Option (TSyntax `term) := none) : CommandElabM Unit :=
  certify name input independence

/-- Parse an exact JSON witness into Lean syntax for programmatic certification. -/
def jsonInput (text : String) : CommandElabM (TSyntax `term) :=
  CertifyECData.jsonInput text

/-- JSON supplies the same record as direct Lean input; metadata is not a claim. -/
def certifyJson (name : Name) (text : String)
    (independence : Option (TSyntax `term) := none) : CommandElabM Unit := atomic do
  let input ← jsonInput text
  certifyFields name input independence
  if let .ok j := Json.parse text then
    if let .ok object := j.getObj? then
      let base := (← getCurrNamespace) ++ name.eraseMacroScopes
      let checkedRank := (← getEnv).contains (base ++ `analytic_rank)
      let rankKeys := ["subject", "parameters", "rank", "coefficients", "arithmetic", "enclosure",
        "evaluator", "analytic_witness"]
      let localKeys := CurveDataJson.localReductionFields
      let known := ["schema", "ainvs", "ap", "aplist", "integral_points", "xcoord_integral_points",
        "minimality", "local_data", "infinite_order_points", "independent_points", "binvs", "cinvs",
        "discriminant", "jinv", "signD", "absD", "conductor", "global_root_number", "anlist",
        "bad_primes", "num_bad_primes", "semistable", "squarefree_disc", "local_invariants",
        "j_integral", "potential_good_reduction"] ++
        localKeys ++ if localKeys.any (fun key => (CurveDataJson.optionalData j key).isSome)
          then ["prime"] else []
      let skipped := object.toList.filterMap fun (key, _) =>
        if known.contains key || (checkedRank && rankKeys.contains key) then none else some key
      unless skipped.isEmpty do
        logInfo m!"Unverified metadata (no claim emitted): {skipped}"

/-- Verify a supplied Lean witness. -/
syntax (name := certifyECTerm) "certify_ec " ident " from " term : command
/-- Read and verify a witness from an exact JSON file. -/
syntax (name := certifyECJson) "certify_ec " ident " from_json " str : command
/-- Read and verify a witness from an exact JSON string. -/
syntax (name := certifyECJsonString) "certify_ec " ident " from_json_string " str : command

/-- Elaborate a certificate from a Lean witness term. -/
@[command_elab certifyECTerm] def elabCertifyECTerm : CommandElab := fun stx => do
  let `(certify_ec $name:ident from $input:term) := stx | throwUnsupportedSyntax
  certify name.getId input

/-- Elaborate a certificate from a JSON witness file. -/
@[command_elab certifyECJson] def elabCertifyECJson : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json $file:str) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← read).fileName
  let path := source.parent.getD "." / file.getString
  let text ← IO.FS.readFile path
  certifyJson name.getId text

/-- Elaborate a certificate from an inline JSON witness. -/
@[command_elab certifyECJsonString] def elabCertifyECJsonString : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json_string $text:str) := stx | throwUnsupportedSyntax
  certifyJson name.getId text.getString

-- The same optional proof clause is available for every input form.
/-- Verify a Lean witness and a proof of independence of its selected points. -/
syntax (name := certifyECTermIndependent)
  "certify_ec " ident " from " term " with_independence " term : command
/-- Verify a JSON file witness and a proof of independence of its selected points. -/
syntax (name := certifyECJsonIndependent)
  "certify_ec " ident " from_json " str " with_independence " term : command
/-- Verify an inline JSON witness and a proof of independence of its selected points. -/
syntax (name := certifyECJsonStringIndependent)
  "certify_ec " ident " from_json_string " str " with_independence " term : command

/-- Elaborate a Lean witness with an explicit point independence proof. -/
@[command_elab certifyECTermIndependent]
def elabCertifyECTermIndependent : CommandElab := fun stx => do
  let `(certify_ec $name:ident from $input:term with_independence $proof:term) := stx
    | throwUnsupportedSyntax
  certify name.getId input (some proof)

/-- Elaborate a JSON file witness with an explicit point independence proof. -/
@[command_elab certifyECJsonIndependent]
def elabCertifyECJsonIndependent : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json $file:str with_independence $proof:term) := stx
    | throwUnsupportedSyntax
  let source := System.FilePath.mk (← read).fileName
  let path := source.parent.getD "." / file.getString
  certifyJson name.getId (← IO.FS.readFile path) (some proof)

/-- Elaborate an inline JSON witness with an explicit point independence proof. -/
@[command_elab certifyECJsonStringIndependent]
def elabCertifyECJsonStringIndependent : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json_string $text:str with_independence $proof:term) := stx
    | throwUnsupportedSyntax
  certifyJson name.getId text.getString (some proof)

end VerifiedLcalc.CertifyEC
