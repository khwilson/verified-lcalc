/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Verification.Iwasawa

/-! # Check prime-indexed Iwasawa data and the infinite good-prime threshold -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command Meta

/-- Certify exactly the submitted rows with supported interpolation evidence and,
separately, a positive threshold backed by a universal arithmetic hypothesis. -/
def certifyIwasawa (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  let rows ← bindStored base `iwasawaData `iwdata (← `(List (ℕ × Sum String (List ℕ))))
  let threshold ← bindStored base `iwasawaThreshold `iwp0 (← `(ℕ))
  if rows.isNone && threshold.isNone then return
  let some supplied ← attachedFact attachment `iwasawa |
    logInfo m!"Unverified {base} Iwasawa data: supply normalized interpolation or threshold evidence"
  let curve := rootIdent (base ++ `curve)
  let evidenceName := base ++ `iwasawa_evidence
  let evidence := rootIdent evidenceName
  emit (← `(noncomputable def $evidence : IwasawaFacts $curve := $supplied))
  auditAxioms evidenceName
  let mut selected := #[]
  if let some reported := rows then
    checked (base ++ `iwdata_distinct) (← `((($reported).map Prod.fst).Nodup))
      (← `(by decide +kernel))
    let count ← liftTermElabM do
      let size ← Term.elabTerm (← `(($reported).length)) (some (mkConst ``Nat))
      let some n ← (evalNat (← whnf size)).run
        | throwError "Expected closed Iwasawa rows"
      return n
    for i in [:count] do
      let index := quote i
      let raw ← `((($reported)[$index]?).getD (0, Sum.inl "o?"))
      let row ← `(($evidence).rowFor ($raw).1)
      unless ← hasOptionalProof row `iwdata do
        logInfo m!"Unverified {base} iwdata entry {i}: supply exact information for this prime"
        continue
      let chosen ← `(($row).get (by rfl))
      let encoded ← `(($chosen).encoding)
      unless ← hasOptionalProof encoded `iwdata do
        logInfo m!"Unverified {base} iwdata entry {i}: no numeric or additive evidence"
        continue
      if ← hasOptionalProof (← `(if ($raw).2 = Sum.inl "o?" ∨
          ($raw).2 = Sum.inl "s?" then some () else none)) `iwdata then
        logInfo m!"Unverified {base} iwdata entry {i}: producer status is unknown"
        continue
      let indexName := base ++ `iwdata ++ Name.mkSimple s!"entry{i}"
      checked (indexName ++ `prime) (← `(($chosen).prime.val = ($raw).1)) (← `(by rfl))
      checked (indexName ++ `value) (← `($encoded = some ($raw).2))
        (← `(by first | rfl | decide +kernel))
      selected := selected.push chosen
  let mut checkedThreshold ← `(none)
  let mut hasThreshold := false
  if let some reported := threshold then
    if ← hasOptionalProof (← `(if $reported = 0 then some () else none)) `iwp0 then
      logInfo m!"Unverified {base} iwp0: producer supplied the zero sentinel"
    else if ← hasOptionalProof (← `(($evidence).threshold)) `iwp0 then
      let bound ← `((($evidence).threshold).get (by rfl))
      checked (base ++ `iwp0) (← `(($bound).prime.val = $reported))
        (← `(by first | rfl | decide +kernel))
      checkedThreshold ← `(some $bound)
      hasThreshold := true
    else
      logInfo m!"Unverified {base} iwp0: supply evidence for every good prime in range"
  if selected.isEmpty && !hasThreshold then return
  let name := base ++ `iwasawa_fact
  let result := rootIdent name
  emit (← `(noncomputable def $result : IwasawaFacts $curve := {
    symbols := ($evidence).symbols
    rows := [$[$selected],*]
    threshold := $checkedThreshold }))
  auditAxioms name

end VerifiedLcalc.CertifyEC
