/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECLmfdbCatalogue
public meta import Lean

/-! Internal dispatch for the order-independent singleton Cremona cases. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command EllipticCurve

/-- Check the exact serialization of a proved singleton label. -/
private def checkCremonaString (name : Name) (claim formatter witness : Ident) :
    CommandElabM Unit := do
  let conductor ← `(($witness).conductor.val)
  let proof ← if let some n ← catalogueNumeral conductor then
    `(by
      first
      | rfl
      | change $formatter $n = $claim
        unfold $formatter $claim
        apply String.toList_injective
        simp [Nat.toDigits_eq_ite (by decide : 1 < 10)])
  else `(by first | rfl | decide +kernel)
  checked name (← `($formatter $conductor = $claim)) proof

/-- Check only requested Cremona fields whose actual indexing sets have one element. -/
def certifyCremona (base : Name) : CommandElabM Unit := do
  let isoClaim ← bindStored base `cremonaIso `Ciso (← `(String))
  let labelClaim ← bindStored base `cremonaLabel `Clabel (← `(String))
  let numberClaim ← bindStored base `cremonaNumber `Cnumber (← `(Nat))
  unless isoClaim.isSome || labelClaim.isSome || numberClaim.isSome do return
  let attachment := base ++ `integral_proofs
  let proof ← if (← getEnv).contains attachment then
    attachedFact (some (rootIdent attachment)) `cremonaSingleton
  else pure none
  let some proof := proof | do
    logInfo m!"Unverified {base} Cremona labels: supply supported singleton evidence"
    return
  let curve := rootIdent (base ++ `curve)
  let evidence := base ++ `cremona_singleton_evidence
  let witness := rootIdent evidence
  emit (← `(def $witness : CremonaSingletonEvidence $curve := $proof))
  auditAxioms evidence
  let onlyClass ← hasOptionalProof (← `(($witness).onlyClass)) `cremona_class
  let onlyCurve ← hasOptionalProof (← `(($witness).onlyCurve)) `cremona_curve
  let iso ← if let (some claim, true) := (isoClaim, onlyClass) then
    let name := base ++ `Ciso
    checkCremonaString name claim (mkIdent ``cremonaSingletonClassLabel) witness
    `(some ⟨$claim, by rfl, $(rootIdent name)⟩)
  else do
    if isoClaim.isSome then logInfo m!"Unverified {base} Ciso: supply a singleton conductor roster"
    `(none)
  let label ← if let (some claim, true, true) := (labelClaim, onlyClass, onlyCurve) then
    let name := base ++ `Clabel
    checkCremonaString name claim (mkIdent ``cremonaSingletonCurveLabel) witness
    `(some ⟨$claim, by rfl, by rfl, $(rootIdent name)⟩)
  else do
    if labelClaim.isSome then
      logInfo m!"Unverified {base} Clabel: supply both singleton orderings"
    `(none)
  let number ← if let (some claim, true) := (numberClaim, onlyCurve) then
    let name := base ++ `Cnumber
    checked name (← `($claim = 1)) (← `(by decide +kernel))
    `(some ⟨$claim, by rfl, $(rootIdent name)⟩)
  else do
    if numberClaim.isSome then logInfo m!"Unverified {base} Cnumber: supply a singleton class"
    `(none)
  let fact := rootIdent (← catalogueFactName base `cremonaLabel)
  emit (← `(def $fact : CremonaSingletonFacts $curve :=
    { evidence := $witness, isoLabel := $iso, curveLabel := $label, number := $number }))

end VerifiedLcalc.CertifyEC
