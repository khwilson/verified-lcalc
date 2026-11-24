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

private def checkPeriodEnclosure (base input label field : Name) (fact : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base input label (← `(DecimalEnclosureClaim)) | return
  checked (base ++ Name.mkSimple s!"{label}_error_nonnegative")
    (← `(0 ≤ ($report).error.getD 0)) (← `(by decide +kernel))
  let some geometry := fact |
    logInfo m!"Unverified {base} {label}: supply a proved enclosure on a globally minimal equation"
    return
  let projection := mkIdent field
  let enclosure ← `(($geometry).$projection)
  unless ← hasOptionalProof enclosure label do
    logInfo m!"Unverified {base} {label}: supply a proved enclosure on a globally minimal equation"
    return
  checked (base ++ label)
    (← `(∃ value, $enclosure = some value ∧ value.reported = ($report).reported ∧
      ($report).error.getD value.error.val = value.error.val))
    (← `(by refine ⟨_, rfl, ?_, ?_⟩ <;> first | rfl | decide +kernel))

private def certifyPeriodGeometry (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let geometry ← if let some fact ← attachedFact attachment `periodGeometry then do
    let name := base ++ `period_geometry_fact
    let geometry := rootIdent name
    emit (← `(noncomputable def $geometry : PeriodGeometryFacts $curve := $fact))
    auditAxioms name
    pure (some geometry)
  else pure none
  checkPeriodEnclosure base `area `area `area geometry
  checkPeriodEnclosure base `faltingsHeight `faltings_height `height geometry
  checkPeriodEnclosure base `stableFaltingsHeight `stable_faltings_height `stableHeight geometry
  let some report ← bindStored base `faltingsRatio `faltings_ratio (← `(ℕ)) | return
  checked (base ++ `faltings_ratio_positive) (← `(0 < $report)) (← `(by decide +kernel))
  let some geometry := geometry |
    logInfo m!"Unverified {base} faltings_ratio: supply a complete class and exact area ratio"
    return
  let ratio ← `(($geometry).ratio)
  unless ← hasOptionalProof ratio `faltings_ratio do
    logInfo m!"Unverified {base} faltings_ratio: supply a complete class and exact area ratio"
    return
  checked (base ++ `faltings_ratio)
    (← `(∃ value, $ratio = some value ∧ value.ratio.val = $report))
    (← `(by
      refine ⟨_, rfl, ?_⟩
      first | rfl | decide +kernel))

/-- Check geometric, period and Faltings claims against the shared proof attachment
and verify any modified Szpiro enclosure with an explicit radius. -/
def certifyGeometryFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  certifyCM base curve attachment
  certifyMinimumTwist base curve attachment
  certifyModifiedSzpiroRatio base curve attachment
  certifyPeriodGeometry base curve attachment

end VerifiedLcalc.CertifyEC
