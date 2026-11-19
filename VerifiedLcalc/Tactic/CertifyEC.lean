module

public import VerifiedLcalc.Assumptions.DerivativeCertification
public import VerifiedLcalc.Certificate.Json
public meta import VerifiedLcalc.Certificate.Json
public meta import Lean
public meta import Mathlib.Tactic.ToExpr

/-! Verify supplied elliptic-curve witnesses and export ordinary named theorems.
No producer, evaluator search, network call, Python service or native_decide is used. -/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve

deriving instance ToExpr for Artifacts.CurveEquation
deriving instance ToExpr for PrecisionPolicy
deriving instance ToExpr for Box
deriving instance ToExpr for TateWitness
deriving instance ToExpr for WildData
deriving instance ToExpr for MinimalityWitness
deriving instance ToExpr for CentralResult
deriving instance ToExpr for DerivativeResult
deriving instance ToExpr for EllipticWitness

/-- Reify supplied data using Lean syntax, with no source-string interpolation. -/
def literalSyntax (e : Expr) : CommandElabM (TSyntax `term) :=
  liftTermElabM <| withOptions (fun o => o.setBool `pp.fullNames true) <|
    Lean.PrettyPrinter.delab e

/-- Stop on elaboration errors instead of continuing with recovered sorry terms. -/
def emit (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then
    throwError "certify_ec stopped: a generated declaration failed to check"

/-- Give every obligation a named declaration and audit its proof dependencies. -/
def checked (name : Name) (type : TSyntax `term) (proof : TSyntax `term)
    (modularity := false) : CommandElabM Unit := do
  emit (← `(theorem $(mkIdent name) : $type := $proof))
  let axioms ← liftTermElabM <| Lean.collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        (modularity && axiomName == ``Assumptions.ellipticModularity) do
      throwError "certify_ec rejected {name}: unexpected axiom {axiomName}"

/-- Elaborate the supplied witness; reducing its outer constructor does not search. -/
def certify (name : Name) (input : TSyntax `term) : CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ name
  let w := mkIdent (base ++ `witness)
  emit (← `(def $w : EllipticWitness := $input))
  let value ← liftTermElabM <| whnf (mkConst (base ++ `witness))
  let ctor := value.getAppFn.constName?
  let args := value.getAppArgs
  unless (ctor == some ``EllipticWitness.central || ctor == some ``EllipticWitness.derivative) && args.size == 3 do
    throwError "Expected a supplied central or derivative EllipticWitness constructor"
  let central := ctor == some ``EllipticWitness.central
  let r := mkIdent (base ++ `result)
  let v := mkIdent (base ++ `minimality)
  let d := mkIdent (base ++ `localData)
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
  let curve := mkIdent (base ++ `curve)
  emit (← `(def $curve : Artifacts.CurveEquation := ($r).equation))
  let hn := mkIdent (base ++ `nonsingular)
  checked (base ++ `nonsingular) (← `(discriminant $curve ≠ 0)) (← `(by decide +kernel))
  let hv := mkIdent (base ++ `minimality_valid)
  checked (base ++ `minimality_valid) (← `(($v).Valid $curve)) (← `(by decide +kernel))
  let hd := mkIdent (base ++ `local_data_valid)
  checked (base ++ `local_data_valid) (← `(($d).Valid $curve)) (← `(by decide +kernel))
  let hN := mkIdent (base ++ `conductor_valid)
  checked (base ++ `conductor_valid) (← `(wildLevelFast $curve $d = ($r).conductor)) (← `(by decide +kernel))
  let hw := mkIdent (base ++ `root_number_valid)
  let hp := mkIdent (base ++ `payload_correct)
  if central then
    checked (base ++ `root_number_valid) (← `(wildSignFast $curve $d = ($r).rootNumber)) (← `(by decide +kernel))
    checked (base ++ `payload_correct) (← `(CentralPayloadCorrect $r)) (← `(by
      unfold CentralPayloadCorrect
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel,
        (squareTailBound ($r).geometricUpper ($r).termLimit).getD 0,
        by decide +kernel, by decide +kernel, by decide +kernel⟩))
  else
    checked (base ++ `root_number_valid) (← `(wildSignFast $curve $d = -1)) (← `(by decide +kernel))
    checked (base ++ `payload_correct) (← `(DerivativePayloadCorrect $r)) (← `(by decide +kernel))
  let hz := mkIdent (base ++ `excludes_zero)
  checked (base ++ `excludes_zero) (← `(($r).box.excludesZero = true)) (← `(by decide +kernel))
  let rank : TSyntax `term ← if central then `(0) else `(1)
  let rankType ← `(analyticOrderAt
    (Assumptions.modularWitness $curve $hn).formL (1 : ℂ) = $rank)
  let rankProof ← if central then
    `(Assumptions.certifyWildCentralModel $r $hn $v $hv $d $hd $hN $hw $hp $hz)
    else `(Assumptions.certifyDerivativeModel $r $hn $v $hv $d $hd $hN $hw $hp $hz)
  checked (base ++ `analytic_rank) rankType rankProof true
  let rankTheorem := mkIdent (base ++ `analytic_rank)
  checked (base ++ `curve_analytic_rank) rankType (← `($rankTheorem)) true
  let certifiedRank := mkIdent (base ++ `certifiedRank)
  emit (← `(def $certifiedRank : {n : Nat // analyticOrderAt
    (Assumptions.modularWitness $curve $hn).formL (1 : ℂ) = n} := ⟨$rank, $rankTheorem⟩))
  logInfo m!"Certified {base}.analytic_rank (rank {if central then "0" else "1"}); conditional on ellipticModularity"

/-- Roll back every generated declaration if any component fails. -/
def certifyAtomic (name : Name) (input : TSyntax `term) : CommandElabM Unit := do
  let saved ← get
  try
    certify name input
  catch error =>
    let messages := (← get).messages
    set { saved with messages }
    throw error

/-- Parse local exact JSON and emit its ordinary Lean witness value. -/
def jsonInput (text : String) : CommandElabM (TSyntax `term) := do
  match CertificateJson.parse text with
  | .error message => throwError "Invalid elliptic witness JSON: {message}"
  | .ok witness => literalSyntax (toExpr witness)

syntax (name := certifyECTerm) "certify_ec " ident " from " term : command
syntax (name := certifyECJson) "certify_ec " ident " from_json " str : command
syntax (name := certifyECJsonString) "certify_ec " ident " from_json_string " str : command

@[command_elab certifyECTerm] def elabCertifyECTerm : CommandElab := fun stx => do
  let `(certify_ec $name:ident from $input:term) := stx | throwUnsupportedSyntax
  certifyAtomic name.getId input

@[command_elab certifyECJson] def elabCertifyECJson : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json $file:str) := stx | throwUnsupportedSyntax
  let source := System.FilePath.mk (← read).fileName
  let path := source.parent.getD "." / file.getString
  let text ← IO.FS.readFile path
  certifyAtomic name.getId (← jsonInput text)

@[command_elab certifyECJsonString] def elabCertifyECJsonString : CommandElab := fun stx => do
  let `(certify_ec $name:ident from_json_string $text:str) := stx | throwUnsupportedSyntax
  certifyAtomic name.getId (← jsonInput text.getString)

end VerifiedLcalc.CertifyEC
