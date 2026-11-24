/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Verification.ModifiedSzpiroRatio
public import VerifiedLcalc.Verification.PeriodGeometry

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
  let name ← catalogueFactName base `complexMultiplication
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
  let evidenceName ← catalogueFactName base `minimumTwistEquation
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
  let name ← catalogueFactName base `modifiedSzpiroRatio
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
    let name ← catalogueFactName base `area
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

private def certifyFaltingsIndex (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let report ← bindStored base `faltingsIndex `faltings_index (← `(ℕ))
  let some evidence ← attachedFact attachment `faltingsIndex |
    if report.isSome then
      logInfo m!"Unverified {base} faltings_index: supply the exact Faltings order in the class"
    return
  let name ← catalogueFactName base `faltingsIndex
  let fact := rootIdent name
  emit (← `(def $fact : FaltingsIndexFact $curve := $evidence))
  auditAxioms name
  if let some value := report then
    checked (base ++ `faltings_index) (← `(($fact).index = $value))
      (← `(by first | rfl | decide +kernel))

private def certifyModularParametrization (base : Name) (curve : Ident)
    (attachment : Option Ident) : CommandElabM Unit := do
  let degree ← bindStored base `modularDegree `degree (← `(ℕ))
  let manin ← bindStored base `maninConstant `manin_constant (← `(ℕ))
  let optimality ← bindStored base `optimality `optimality (← `(ℕ))
  let some supplied ← attachedFact attachment `modularParametrization |
    if degree.isSome || manin.isSome || optimality.isSome then
      logInfo m!"Unverified {base} modular parametrization: supply the minimum modular map"
    return
  let evidenceName := base ++ `modular_parametrization_evidence
  let evidence := rootIdent evidenceName
  emit (← `(noncomputable def $evidence : ModularParametrizationFacts $curve := $supplied))
  auditAxioms evidenceName
  let degreeMatch ← if let some report := degree then do
    let name := base ++ `modular_degree
    checked name
      (← `(($evidence).degree.val = $report))
      (← `(by first | rfl | decide +kernel))
    let proof := rootIdent name
    `(some ⟨$report, $proof⟩)
  else `(none)
  let maninMatch ← if let some report := manin then do
    let name := base ++ `manin_constant
    checked name (← `(($evidence).maninConstant.val = $report))
      (← `(by first | rfl | decide +kernel))
    let proof := rootIdent name
    `(some ⟨$report, $proof⟩)
  else `(none)
  let optimalityMatch ← if let some report := optimality then do
    if !(← hasOptionalProof (← `(if $report ≤ 1 then some () else none)) `optimality) then
      logInfo m!"Unverified {base} optimality: the producer reports an ambiguous candidate set"
      `(none)
    else if !(← hasOptionalProof (← `(($evidence).optimal)) `optimality) then
      logInfo m!"Unverified {base} optimality: supply the full period image comparison"
      `(none)
    else
      let name := base ++ `optimality
      checked name
        (← `(∃ status, ($evidence).optimal = some status ∧
          Modularity.optimalityStatusCode status.val = $report))
        (← `(by
          refine ⟨_, rfl, ?_⟩
          rfl))
      let proof := rootIdent name
      `(some ⟨$report, $proof⟩)
  else `(none)
  let name ← catalogueFactName base `modularDegree
  let result := rootIdent name
  emit (← `(noncomputable def $result : CertifiedModularParametrization $curve :=
    ⟨$evidence, $degreeMatch, $maninMatch, $optimalityMatch⟩))
  auditAxioms name

/-- Check geometric, period and Faltings claims against the shared proof attachment
and verify any modified Szpiro enclosure with an explicit radius. -/
def certifyGeometryFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  certifyCM base curve attachment
  certifyMinimumTwist base curve attachment
  certifyModifiedSzpiroRatio base curve attachment
  certifyPeriodGeometry base curve attachment
  certifyFaltingsIndex base curve attachment
  certifyModularParametrization base curve attachment

end VerifiedLcalc.CertifyEC
