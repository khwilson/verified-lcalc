module

public import VerifiedLcalc.Certificate.Json
public meta import VerifiedLcalc.Certificate.FieldCatalogue
public meta import Lean
public meta import Mathlib.Tactic.ToExpr

/-! Shared syntax reification, atomic declaration emission and proof-dependency
checks for the elliptic-curve certificate commands. These helpers produce proof
obligations; mathematical assertions are checked by Lean's kernel. -/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve

/-- Root qualification keeps generated declarations in the intended namespace. -/
def rootIdent (name : Name) : Ident := mkIdent (`_root_ ++ name.eraseMacroScopes)

/-- Resolve the emitted proof record for a catalogued witness field. -/
def catalogueFactName (base field : Name) : CommandElabM Name := do
  let some output := FieldCatalogue.outputFact field
    | throwError "No certificate output registered for {field}"
  return base ++ output

/-- Resolve the soundness lemma used by a catalogue-backed check. -/
def catalogueChecker (field : Name) : CommandElabM Ident := do
  let some checker := FieldCatalogue.checker field
    | throwError "No certificate checker registered for {field}"
  return rootIdent checker

deriving instance ToExpr for WeierstrassCurve
deriving instance ToExpr for PrecisionPolicy
deriving instance ToExpr for Box
deriving instance ToExpr for TateWitness
deriving instance ToExpr for WildData
deriving instance ToExpr for MinimalityWitness
deriving instance ToExpr for CentralResult
deriving instance ToExpr for DerivativeResult
deriving instance ToExpr for TamagawaTypeIIIShift
deriving instance ToExpr for TamagawaTypeIIShift
deriving instance ToExpr for TypeIVTamagawaResidue
deriving instance ToExpr for TamagawaTypeIVEvidence
deriving instance ToExpr for LocalReductionClaim
deriving instance ToExpr for AbcQualityClaim
deriving instance ToExpr for RegulatorClaim
deriving instance ToExpr for PadicRegulatorClaim
deriving instance ToExpr for DecimalEnclosureClaim
deriving instance ToExpr for SpecialLValueClaim
deriving instance ToExpr for TorsionBoundWitness
deriving instance ToExpr for IsogenyEdgeClaim
deriving instance ToExpr for AdelicGeneratorsClaim
deriving instance ToExpr for TorsionGrowthFieldClaim
deriving instance ToExpr for CanonicalHeightsClaim
deriving instance ToExpr for Sum
deriving instance ToExpr for EllipticWitness


/-- Display omissions must never become holes in generated witness data. -/
partial def hasDisplayOmission (stx : Syntax) : Bool :=
  (stx.isAtom && stx.getAtomVal == "⋯") || stx.getArgs.any hasDisplayOmission

/-- Reify supplied data using Lean syntax, independently of display truncation
settings. The budget supports the bounded JSON profile; exhaustion is an error. -/
def literalSyntax (e : Expr) : CommandElabM (TSyntax `term) := do
  let stx ← liftTermElabM <| withOptions (fun o =>
      o.setBool `pp.fullNames true |>.setBool `pp.deepTerms true
        |>.setBool `pp.proofs true |>.set `pp.maxSteps (1000000 : Nat)) <|
    Lean.PrettyPrinter.delab e
  if hasDisplayOmission stx.raw then
    throwError "certify_ec cannot serialize this witness without a display omission"
  return stx

/-- Stop on elaboration errors instead of continuing with recovered sorry terms. -/
def emit (command : Syntax) : CommandElabM Unit := do
  -- Certificates are audited immediately. Finish generated proof elaboration
  -- before inspecting errors or dependencies, including caller-supplied tactics.
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) do
    elabCommand command
  if (← get).messages.hasErrors then
    throwError "certify_ec stopped: a generated declaration failed to check"

/-- Audit transitive dependencies of an emitted certificate declaration. -/
def auditAxioms (name : Name) (modularity := false) : CommandElabM Unit := do
  let axioms ← liftTermElabM <| Lean.collectAxioms name
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
        (modularity && axiomName == `VerifiedLcalc.Assumptions.ellipticModularity) do
      throwError "certify_ec rejected {name}: unexpected axiom {axiomName}"

/-- Give every obligation a named declaration and audit its proof dependencies. -/
def checked (name : Name) (type : TSyntax `term) (proof : TSyntax `term)
    (modularity := false) : CommandElabM Unit := do
  let name := name.eraseMacroScopes
  try
    emit (← `(theorem $(rootIdent name) : $type := $proof))
  catch error =>
    throwError "certify_ec failed checking {name}: {error.toMessageData}"
  auditAxioms name modularity

/-- Roll back every generated declaration if any component of a certificate fails. -/
def atomic (action : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← get
  try
    action
  catch error =>
    let messages := (← get).messages
    set { saved with messages }
    throw error

/-- Inspect one optional component of the already elaborated, closed record. -/
def optionalInput (w : Name) (field : Name) : CommandElabM (Option (TSyntax `term)) := do
  let value ← liftTermElabM <| whnf
    (mkApp (mkConst (``EllipticWitness ++ field)) (mkConst w))
  match value.getAppFn.constName? with
  | some ``Option.none => return none
  | some ``Option.some => return some (← literalSyntax value.getAppArgs.back!)
  | _ => throwError "Expected closed optional data for {field}"


/-- Bind an optional raw value and prove its equality with the submitted field. -/
def bindStored (base field label : Name) (type : TSyntax `term) :
    CommandElabM (Option Ident) := do
  let some input ← optionalInput (base ++ `witness) field | return none
  let value := rootIdent (base ++ Name.mkSimple s!"claimed_{label}")
  emit (← `(def $value : $type := $input))
  let w := rootIdent (base ++ `witness)
  let projection := rootIdent (``EllipticWitness ++ field)
  checked (base ++ Name.mkSimple s!"{label}_input_eq")
    (← `($projection $w = some $value)) (← `(by rfl))
  return some value

/-- Inspect an optional proof attachment in the current section, including its local instances. -/
def hasOptionalProof (term : TSyntax `term) (label : Name) : CommandElabM Bool :=
  runTermElabM fun _ => do
    let expr ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← whnf (← instantiateMVars expr)
    match value.getAppFn.constName? with
    | some ``Option.none => pure false
    | some ``Option.some => pure true
    | _ => throwError "Expected a known option constructor for {label}"

/-- Select optional proof evidence from the shared curve-indexed attachment. -/
def attachedFact (attachment : Option Ident) (field : Name) :
    CommandElabM (Option (TSyntax `term)) := do
  let some attachment := attachment | return none
  let projection := mkIdent field
  let selected ← `(($attachment).$projection)
  if ← hasOptionalProof selected field then
    some <$> `(($selected).get (by rfl))
  else pure none

end VerifiedLcalc.CertifyEC
