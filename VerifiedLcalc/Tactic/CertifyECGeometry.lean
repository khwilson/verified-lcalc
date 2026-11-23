/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Verification.ModifiedSzpiroRatio

/-! Verify geometric and modified Szpiro claims against curve-indexed evidence. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command

private def certifyCM (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let claim ← bindStored base `complexMultiplication `cm (← `(Int))
  let some fact ← attachedFact attachment `complexMultiplication |
    if claim.isSome then logInfo m!"Unverified {base} cm: supply the geometric endomorphism ring"
    return
  let name := base ++ `cm_fact
  let cm := rootIdent name
  emit (← `(def $cm : ComplexMultiplicationFacts $curve := $fact))
  auditAxioms name
  if let some d := claim then
    checked (base ++ `cm) (← `(($cm).discriminant = $d))
      (← `(by first | rfl | decide +kernel))

private def certifyMinimumTwist (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let equation ← bindStored base `minimumTwistEquation `min_quad_twist_ainvs
    (← `(WeierstrassCurve ℤ))
  let disc ← bindStored base `minimumTwistDiscriminant `min_quad_twist_disc (← `(Int))
  let some fact ← attachedFact attachment `minimumQuadraticTwist |
    if equation.isSome || disc.isSome then
      logInfo m!"Unverified {base} quadratic twist: supply minimum-conductor twist evidence"
    return
  let evidenceName := base ++ `minimum_quadratic_twist_evidence
  let evidence := rootIdent evidenceName
  emit (← `(def $evidence : MinimumQuadraticTwistEvidence $curve := $fact))
  auditAxioms evidenceName
  let name := base ++ `minimum_quadratic_twist_fact
  let twist := rootIdent name
  emit (← `(def $twist : MinimumQuadraticTwistFacts $curve := ($evidence).minimum))
  auditAxioms name
  if let some w := equation then
    checked (base ++ `min_quad_twist_ainvs) (← `(($twist).equation = $w))
      (← `(by first | rfl | apply WeierstrassCurve.ext <;> decide +kernel))
  if let some d := disc then
    checked (base ++ `min_quad_twist_disc) (← `(($twist).discriminant = $d))
      (← `(by first | rfl | decide +kernel))

private def certifyModifiedSzpiroRatio (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `modifiedSzpiroRatio `szpiro_ratio
    (← `(DecimalEnclosureClaim)) | return
  unless ← hasOptionalProof (← `(($report).error)) `szpiro_ratio do
    logInfo m!"Unverified {base} szpiro_ratio: supply an absolute error radius"
    return
  let error ← `(($report).error.getD 0)
  checked (base ++ `szpiro_ratio_error_nonnegative) (← `(0 ≤ $error))
    (← `(by decide +kernel))
  let some arithmetic ← attachedFact attachment `modifiedSzpiroRatio |
    logInfo m!"Unverified {base} szpiro_ratio: supply a minimal model and conductor identification"
    return
  let hvalid := rootIdent (base ++ `szpiro_ratio_valid)
  checked (base ++ `szpiro_ratio_valid)
    (← `(Certification.modifiedSzpiroRatioValid $curve ($arithmetic).conductor
      ($report).reported $error = true))
    (← `(by decide +kernel))
  let name := base ++ `szpiro_ratio_fact
  let fact := rootIdent name
  emit (← `(def $fact : ModifiedSzpiroRatioFacts $curve :=
    Certification.modifiedSzpiroRatioFactsOfCheck $curve $arithmetic ($report).reported
      $error $hvalid))
  auditAxioms name

/-- Compare optional geometry claims to the shared proof attachment and check any
modified Szpiro enclosure with an explicit radius. -/
def certifyGeometryFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  certifyCM base curve attachment
  certifyMinimumTwist base curve attachment
  certifyModifiedSzpiroRatio base curve attachment

end VerifiedLcalc.CertifyEC
