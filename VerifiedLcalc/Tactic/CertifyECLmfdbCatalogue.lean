/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! Internal elaboration of the LMFDB conductor roster and within-class ordering checks. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command Meta EllipticCurve

/-- Select the full reduced minimal ordering already attached for the subject's class. -/
private def orderedCurveClass (base : Name) : CommandElabM (Option (TSyntax `term)) := do
  let attached := base ++ `isogeny_class_evidence
  unless (← getEnv).contains attached do return none
  let evidence := rootIdent attached
  let ordering ← `(($evidence).ordering)
  unless ← hasOptionalProof ordering `lmfdb_number do return none
  some <$> `(⟨($evidence).model, ($ordering).get (by rfl)⟩)

/-- Select the supplied conductor roster for the given equation. -/
private def orderedRoster (base : Name) (curve : Ident) : CommandElabM (Option Ident) := do
  let attached := base ++ `integral_proofs
  unless (← getEnv).contains attached do return none
  let some roster ← attachedFact (some (rootIdent attached)) `conductorClassRoster | return none
  let name := base ++ `lmfdb_conductor_class_roster
  emit (← `(def $(rootIdent name) : ConductorClassRoster $curve := $roster))
  auditAxioms name
  return some (rootIdent name)

/-- Expose a literal formatting argument even when its record also carries local proofs.
The generated equality checks that the literal is definitionally equal to the projection. -/
private def catalogueNumeral (input : TSyntax `term) : CommandElabM (Option (TSyntax `term)) :=
  runTermElabM fun _ => do
    let term ← Term.elabTerm input (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let term ← withTransparency .all <| Meta.reduce (← instantiateMVars term)
    return (← getNatValue? term).map fun n => quote n

/-- Compare a supplied value with the value computed from its mathematical order proof. -/
private def catalogueValue (base field : Name) (claim : Option Ident)
    (expected : Option (TSyntax `term)) (evidence : String)
    (normalized : Option (TSyntax `term) := none) :
    CommandElabM (TSyntax `term) := do
  let some claim := claim | return ← `(none)
  let some expected := expected | do
    logInfo m!"Unverified {base} {field}: supply {evidence}"
    return ← `(none)
  let valid := base ++ field
  let proof ← if let some closed := normalized then
    `(by
      first
      | rfl
      | change $closed = $claim
        unfold $claim
        apply String.toList_injective
        first | rw [lmfdbIsoLabel] | rw [lmfdbCurveLabel]
        all_goals simp [lmfdbIsoLabelChars, lmfdbClassCodeChars,
          Nat.toDigits_eq_ite (by decide : 1 < 10)])
  else `(by first | rfl | decide +kernel)
  checked valid (← `($expected = $claim)) proof
  `(some ⟨$claim, congrArg some $(rootIdent valid)⟩)

/-- Check each supplied LMFDB catalogue field against the proof of its required order. -/
def certifyLmfdbCatalogue (base : Name) : CommandElabM Unit := do
  let numberClaim ← bindStored base `lmfdbNumber `lmfdb_number (← `(Nat))
  let indexClaim ← bindStored base `isoNlabel `iso_nlabel (← `(Nat))
  let isoClaim ← bindStored base `lmfdbIso `lmfdb_iso (← `(String))
  let curveClaim ← bindStored base `lmfdbLabel `lmfdb_label (← `(String))
  unless numberClaim.isSome || indexClaim.isSome || isoClaim.isSome || curveClaim.isSome do return
  let curve := rootIdent (base ++ `curve)
  let classProof ← if numberClaim.isSome || curveClaim.isSome then orderedCurveClass base
    else pure none
  let roster ← if indexClaim.isSome || isoClaim.isSome || curveClaim.isSome then
    orderedRoster base curve
    else pure none
  let className := rootIdent (base ++ `lmfdb_ordered_class)
  if let some ordered := classProof then
    emit (← `(def $className : Σ m : IsogenyClassModel $curve,
        IsogenyClassOrdering m.representatives := $ordered))
  let numberExpression ← classProof.mapM fun _ => `(($className).1.curveIndex.val + 1)
  let indexExpression ← roster.mapM fun r => `(($r).classIndex.val)
  let isoExpression ← roster.mapM fun r => `(lmfdbIsoLabel ($r).conductor ($r).classIndex.val)
  let curveExpression ← if let (some r, some n) := (roster, numberExpression) then
    some <$> `(lmfdbCurveLabel ($r).conductor ($r).classIndex.val $n)
  else pure none
  let normalizedRoster ←
    if let (some r, true) := (roster, isoClaim.isSome || (curveClaim.isSome && classProof.isSome))
    then do
      let conductor ← catalogueNumeral (← `(($r).conductor))
      let index ← catalogueNumeral (← `(($r).classIndex.val))
      pure (conductor.bind fun c => index.map (c, ·))
    else pure none
  let normalizedIso ← normalizedRoster.mapM fun (conductor, index) =>
    `(lmfdbIsoLabel $conductor $index)
  let normalizedCurve ←
    if let (some (conductor, index), some n, true) :=
        (normalizedRoster, numberExpression, curveClaim.isSome) then
      let number ← catalogueNumeral n
      number.mapM fun m => `(lmfdbCurveLabel $conductor $index $m)
    else pure none
  let number ← catalogueValue base `lmfdb_number numberClaim numberExpression
    "the complete reduced minimal curve order"
  let index ← catalogueValue base `iso_nlabel indexClaim indexExpression
    "the ordered conductor roster"
  let iso ← catalogueValue base `lmfdb_iso isoClaim isoExpression "the ordered conductor roster"
    normalizedIso
  let label ← catalogueValue base `lmfdb_label curveClaim curveExpression
    "the conductor roster and curve order" normalizedCurve
  let rosterTerm ← if let some r := roster then `(some $r) else `(none)
  let classTerm ← if classProof.isSome then `(some $className) else `(none)
  let fact := rootIdent (base ++ `lmfdb_catalogue)
  emit (← `(def $fact : LmfdbCatalogueFacts $curve :=
    { roster := $rosterTerm, orderedClass := $classTerm, number := $number,
      classIndex := $index, isoLabel := $iso, curveLabel := $label }))

end VerifiedLcalc.CertifyEC
