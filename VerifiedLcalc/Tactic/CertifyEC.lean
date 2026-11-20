module

public import VerifiedLcalc.Certification.DerivativeCertification
public import VerifiedLcalc.Certificate.Json
public import VerifiedLcalc.Tactic.CertifyECData
public meta import VerifiedLcalc.Certificate.Json
public meta import Lean

/-!
# Certifying elliptic-curve arithmetic and analytic-rank witnesses

`certify_ec` turns supplied exact witness data into named Lean definitions and
kernel-checked theorems for an integral `WeierstrassCurve`. Arithmetic witnesses
certify prime coefficients and integral-point membership without a modularity
assumption. Analytic witnesses support exact
analytic rank zero, using a central-value enclosure excluding zero, and exact
analytic rank one, using root number `-1` and a first-derivative enclosure
excluding zero. The analytic conclusions are conditional on the project's
explicit `VerifiedLcalc.Assumptions.ellipticModularity` axiom.

## Input forms

* `certify_ec Name from witness` accepts a Lean term of type `CurveDataWitness`
  or `EllipticWitness`. The latter has constructor `EllipticWitness.central`
  or `EllipticWitness.derivative`; arithmetic records may be supplied directly.
* `certify_ec Name from_json "curve.json"` reads exact witness JSON from a local
  file, resolving the path relative to the Lean source file containing the command.
* `certify_ec Name from_json_string "..."` accepts the same JSON format inline.

All input methods use one optional-facts pipeline. JSON fields are inspected
independently of optional schema metadata: `ainvs` (or `subject.ainvs`) anchors
the model; `ap` or LMFDB `aplist` supplies coefficients; `integral_points` or
`xcoord_integral_points` supplies point data. Complete rank-zero/one witness
fields, at the top level or under `analytic_witness`, additionally request
analytic certification. Other metadata is reported as unverified. A bare
`rank` or `analytic_rank` value never supplies a proof witness.

An analytic witness supplies the equation, claimed conductor, numerical parameters,
coefficients, interval and tail data, minimality evidence, and local reduction
data. JSON parsing uses `CertificateJson.parse` and its bounded exact-data profile.
The command verifies these supplied data; it performs no witness search or network
request. A caller using the Lean-term form controls any computation in that term.

## Arithmetic-data declarations

A `CurveDataWitness` supplies the equation, optional prime/value pairs in
`primeCoefficients`, optional integer pairs in `integralCoordinates`, and
optional `analyticWitness : Option EllipticWitness`. Both lists default to empty
and the analytic witness defaults to `none`. Existing `EllipticWitness` inputs
are wrapped into this same record. `Name.supplied` retains the common record
for every input method. When analytic data is present, it is checked along with
the arithmetic fields and a kernel-checked equation equality prevents mixing
facts about different curves. Arithmetic helper declarations then also live
under `Name.data`, with the main facts re-exported at `Name`.
For arithmetic-only data the command exports `Name.witness`, `Name.curve`, `Name.nonsingular`,
`Name.prime_coefficients_valid`, and `Name.ap_correct`, identifying each listed
coefficient with the actual rational curve's `LFunction p`, including supported
bad primes. It also exports `Name.integral_coordinates_valid`,
`Name.points_on_curve`, `Name.curve_isElliptic`, `Name.point`, and
`Name.point_integral`, constructing rational points and proving their membership
in TauCeti's `curve.integralPoints`. These certify membership only; they make no
completeness or algebraic-rank claim. All these proofs use standard Lean axioms
only. See `CertifiedCurves/Data.lean` for complete input and import examples.

## Analytic-rank declarations

With command name `Name` in namespace `Outer`, declarations live under
`Outer.Name`. The data definitions are:

* `witness : EllipticWitness`, the supplied witness;
* `result : CentralResult` or `DerivativeResult`, its numerical result record;
* `minimality : MinimalityWitness` and `localData : WildData`, its arithmetic data;
* `curve : WeierstrassCurve ℤ`, the equation from `result`.

Each verification step produces a separate theorem:

* `witness_eq` identifies the witness with the generated component definitions;
* `nonsingular` proves that `curve.Δ ≠ 0`;
* `minimality_valid` and `local_data_valid` validate the supplied arithmetic data;
* `conductor_valid` matches `wildLevelFast curve localData` to the claimed conductor;
* `root_number_valid` checks the computed sign against the central witness's sign,
  or against `-1` for a derivative witness;
* `payload_correct` proves `CentralPayloadCorrect result` or
  `DerivativePayloadCorrect result`, checking the coefficients and numerical bounds;
* `excludes_zero` proves that the certified output interval excludes zero.

The main exported theorem is `analytic_rank`, also available as
`curve_analytic_rank`. Its type is

```lean
analyticOrderAt
  (Modularity.modularWitness Name.curve Name.nonsingular).formL (1 : ℂ) = r
```

where `r` is `0` or `1`. `certifiedRank` packages that natural number together
with its proof as a subtype value. The conductor/sign checks above are arithmetic
identities; their interpretation for the curve's L-function uses the documented
modularity assumption in the final analytic theorem.

## Checking and reuse

Finite checks use `decide +kernel`. Every generated theorem's axiom dependencies
are audited: finite checks allow only `propext`, `Classical.choice`, and `Quot.sound`;
the final analytic theorems additionally allow `ellipticModularity`. A rejected
command rolls back all its generated declarations and reports the failure.

Successful commands log the exported theorem names and the analytic witness's
conditional status when applicable.
Compiling the containing Lean module produces the `.olean` containing these
declarations. Other proofs import that module and use `Name.analytic_rank` or
`Name.certifiedRank` directly. With Lean's `module` syntax, put the command in a
`public section` to export the declarations. See `examples/certify_ec/` for complete
examples and `tests/consumers/CertifiedECConsumer.lean` for compiled-proof reuse.
-/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve

/-- Elaborate the supplied witness; reducing its outer constructor does not search. -/
def certifyAnalytic (name : Name) (input : TSyntax `term) (announce := true) : CommandElabM Unit := do
  let name := name.eraseMacroScopes
  let base := (← getCurrNamespace) ++ name
  let w := rootIdent (base ++ `witness)
  emit (← `(def $w : EllipticWitness := $input))
  let value ← liftTermElabM <| whnf (mkConst (base ++ `witness))
  let ctor := value.getAppFn.constName?
  let args := value.getAppArgs
  unless (ctor == some ``EllipticWitness.central || ctor == some ``EllipticWitness.derivative) && args.size == 3 do
    throwError "Expected a supplied central or derivative EllipticWitness constructor"
  let central := ctor == some ``EllipticWitness.central
  let r := rootIdent (base ++ `result)
  let v := rootIdent (base ++ `minimality)
  let d := rootIdent (base ++ `localData)
  let result ← literalSyntax args[0]!
  let minimality ← literalSyntax args[1]!
  let localData ← literalSyntax args[2]!
  if central then
    emit (← `(def $r : CentralResult := $result))
  else
    emit (← `(def $r : DerivativeResult := $result))
  emit (← `(def $v : MinimalityWitness := $minimality))
  emit (← `(def $d : WildData := $localData))
  let expected ← if central then `(EllipticWitness.central $r $v $d)
    else `(EllipticWitness.derivative $r $v $d)
  checked (base ++ `witness_eq) (← `($w = $expected)) (← `(by rfl))
  let curve := rootIdent (base ++ `curve)
  emit (← `(def $curve : (WeierstrassCurve ℤ) := ($r).equation))
  let hn := rootIdent (base ++ `nonsingular)
  checked (base ++ `nonsingular) (← `(WeierstrassCurve.Δ $curve ≠ 0)) (← `(by decide +kernel))
  let hv := rootIdent (base ++ `minimality_valid)
  checked (base ++ `minimality_valid) (← `(($v).Valid $curve)) (← `(by decide +kernel))
  let hd := rootIdent (base ++ `local_data_valid)
  checked (base ++ `local_data_valid) (← `(($d).Valid $curve)) (← `(by decide +kernel))
  let hN := rootIdent (base ++ `conductor_valid)
  checked (base ++ `conductor_valid) (← `(wildLevelFast $curve $d = ($r).conductor)) (← `(by decide +kernel))
  let hw := rootIdent (base ++ `root_number_valid)
  let hp := rootIdent (base ++ `payload_correct)
  -- Give identical numerical obligations identical types before decide's
  -- per-module auxiliary-lemma cache is consulted. Curve arithmetic remains
  -- a separate obligation for every supplied equation.
  let finiteCheck ← `(by dsimp only [$r:term]; decide +kernel)
  if central then
    checked (base ++ `root_number_valid) (← `(wildSignFast $curve $d = ($r).rootNumber)) (← `(by decide +kernel))
    checked (base ++ `payload_correct) (← `(CentralPayloadCorrect $r)) (← `(by
      unfold CentralPayloadCorrect
      exact ⟨$finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck,
        (squareTailBound ($r).geometricUpper ($r).termLimit).getD 0,
        $finiteCheck, $finiteCheck, $finiteCheck⟩))
  else
    checked (base ++ `root_number_valid) (← `(wildSignFast $curve $d = -1)) (← `(by decide +kernel))
    checked (base ++ `payload_correct) (← `(DerivativePayloadCorrect $r)) (← `(by
      unfold DerivativePayloadCorrect
      exact ⟨$finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck,
        $finiteCheck, $finiteCheck, $finiteCheck⟩))
  let hz := rootIdent (base ++ `excludes_zero)
  checked (base ++ `excludes_zero) (← `(($r).box.excludesZero = true)) (← `(by decide +kernel))
  let rank : TSyntax `term ← if central then `(0) else `(1)
  let rankType ← `(analyticOrderAt
    (Modularity.modularWitness $curve $hn).formL (1 : ℂ) = $rank)
  let rankProof ← if central then
    `(Certification.certifyWildCentralModel $r $hn $v $hv $d $hd $hN $hw $hp $hz)
    else `(Certification.certifyDerivativeModel $r $hn $v $hv $d $hd $hN $hw $hp $hz)
  checked (base ++ `analytic_rank) rankType rankProof true
  let rankTheorem := rootIdent (base ++ `analytic_rank)
  checked (base ++ `curve_analytic_rank) rankType (← `($rankTheorem)) true
  let certifiedRank := rootIdent (base ++ `certifiedRank)
  emit (← `(def $certifiedRank : {n : Nat // analyticOrderAt
    (Modularity.modularWitness $curve $hn).formL (1 : ℂ) = n} := ⟨$rank, $rankTheorem⟩))
  if announce then logInfo m!"Certified {base}.analytic_rank (rank {if central then "0" else "1"}); conditional on ellipticModularity"

/-- Decode the supported supplied facts, as for every JSON entry point. -/
def jsonInput (text : String) : CommandElabM (TSyntax `term) :=
  CertifyECData.jsonInput text

/-- Probe only the input's type, restoring elaboration state afterwards.
Arithmetic records can therefore use the same `from` syntax as rank witnesses. -/
def isRankInput (input : TSyntax `term) : CommandElabM Bool := do
  let saved ← get
  let result ← try
    let isExpected ← liftTermElabM do
      let e ← Term.elabTerm input (some (mkConst ``EllipticWitness))
      isDefEq (← inferType e) (mkConst ``EllipticWitness)
    pure (isExpected && !(← get).messages.hasErrors)
  catch _ => pure false
  set saved
  return result

/-- Re-export arithmetic facts alongside a rank certificate for the same equation. -/
def exposeDataFacts (base : Name) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  let dataCurve := rootIdent (base ++ `data ++ `curve)
  let supplied := rootIdent (base ++ `supplied)
  checked (base ++ `data_curve_eq) (← `($dataCurve = $curve)) (← `(by rfl))
  for field in [`prime_coefficients_valid, `integral_coordinates_valid] do
    let original := rootIdent (base ++ `data ++ field)
    let type ← if field == `prime_coefficients_valid then
      `(($supplied).primeCoefficientsValid = true)
      else `(($supplied).integralCoordinatesValid = true)
    checked (base ++ field) type (← `($original))
  let ap := rootIdent (base ++ `data ++ `ap_correct)
  checked (base ++ `ap_correct)
    (← `(∀ (p : Nat) (a : Int), (p, a) ∈ ($supplied).primeCoefficients →
      (($curve).baseChange ℚ).LFunction p = a)) (← `($ap))
  let points := rootIdent (base ++ `data ++ `points_on_curve)
  checked (base ++ `points_on_curve)
    (← `(∀ (x y : Int), (x, y) ∈ ($supplied).integralCoordinates →
      ($curve).toAffine.Equation x y)) (← `($points))
  let instanceName := rootIdent (base ++ `curve_isElliptic)
  let originalInstance := rootIdent (base ++ `data ++ `curve_isElliptic)
  emit (← `(instance $instanceName:ident : (($curve).baseChange ℚ).IsElliptic :=
    $originalInstance))
  let point := rootIdent (base ++ `point)
  let originalPoint := rootIdent (base ++ `data ++ `point)
  emit (← `(def $point (i : Fin ($supplied).integralCoordinates.length) :
    (($curve).baseChange ℚ).toAffine.Point := $originalPoint i))
  let membership := rootIdent (base ++ `data ++ `point_integral)
  checked (base ++ `point_integral)
    (← `(∀ i : Fin ($supplied).integralCoordinates.length,
      $point i ∈ ($curve).integralPoints)) (← `($membership))

/-- All input methods reach this optional-facts pipeline. Every supplied
supported witness is checked; conflicting equations reject the whole command. -/
def certifyFields (name : Name) (input : TSyntax `term) : CommandElabM Unit := do
  let name := name.eraseMacroScopes
  let base := (← getCurrNamespace) ++ name
  let supplied := rootIdent (base ++ `supplied)
  emit (← `(def $supplied : CurveDataWitness := $input))
  let value ← liftTermElabM <| whnf
    (mkApp (mkConst ``CurveDataWitness.analyticWitness) (mkConst (base ++ `supplied)))
  match value.getAppFn.constName? with
  | some ``Option.none => CertifyECData.certify name supplied false
  | some ``Option.some =>
    let rank ← literalSyntax value.getAppArgs.back!
    certifyAnalytic name rank false
    CertifyECData.certify (name ++ `data) supplied false
    exposeDataFacts base
  | _ => throwError "Expected supplied optional analytic-witness data"
  logInfo m!"Certified {base}.ap_correct and {base}.point_integral for the supplied lists"
  if value.getAppFn.constName? == some ``Option.some then
    logInfo m!"Certified {base}.analytic_rank; conditional on ellipticModularity"

/-- Existing rank inputs and optional-facts records share the same command. -/
def certifyInput (name : Name) (input : TSyntax `term) : CommandElabM Unit :=
  atomic do
    let input ← if ← isRankInput input then
      `(CurveDataWitness.ofAnalyticWitness $input) else pure input
    certifyFields name input

/-- Programmatic entry point with the same optional-facts behavior as the command. -/
def certify (name : Name) (input : TSyntax `term) : CommandElabM Unit :=
  certifyInput name input

/-- Backward-compatible name for the same atomic, field-driven entry point. -/
def certifyAtomic (name : Name) (input : TSyntax `term) : CommandElabM Unit :=
  certify name input

/-- Decode supported fields, report metadata, and use the same pipeline as
direct Lean records. A bare stored rank does not constitute a rank witness. -/
def certifyJson (name : Name) (text : String) : CommandElabM Unit := atomic do
  let input ← jsonInput text
  certifyFields name input
  if let .ok j := Json.parse text then
    if let .ok object := j.getObj? then
      let rankKeys := ["subject", "parameters", "rank", "coefficients", "arithmetic", "enclosure", "evaluator", "analytic_witness"]
      let checkedRank := (CurveDataJson.parse text).toOption.bind (·.analyticWitness) |>.isSome
      let known := ["schema", "ainvs", "ap", "aplist", "integral_points", "xcoord_integral_points"]
      let skipped := object.toList.filterMap fun (key, _) =>
        if known.contains key || (checkedRank && rankKeys.contains key) then none else some key
      unless skipped.isEmpty do
        logInfo m!"Unverified metadata (no claim emitted): {skipped}"

syntax (name := certifyECTerm) "certify_ec " ident " from " term : command
syntax (name := certifyECJson) "certify_ec " ident " from_json " str : command
syntax (name := certifyECJsonString) "certify_ec " ident " from_json_string " str : command

@[command_elab certifyECTerm] def elabCertifyECTerm : CommandElab := fun stx => do
  let `(certify_ec $name:ident from $input:term) := stx | throwUnsupportedSyntax
  certifyInput name.getId input

@[command_elab certifyECJson] def elabCertifyECJson : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json $file:str) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← read).fileName
  let path := source.parent.getD "." / file.getString
  let text ← IO.FS.readFile path
  certifyJson name.getId text

@[command_elab certifyECJsonString] def elabCertifyECJsonString : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json_string $text:str) := stx | throwUnsupportedSyntax
  certifyJson name.getId text.getString

end VerifiedLcalc.CertifyEC
