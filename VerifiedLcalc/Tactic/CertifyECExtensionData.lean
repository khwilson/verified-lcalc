/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Certificate.Support.ExtensionData
import Mathlib.Data.List.OfFn

/-! Check number-field presentations, extension torsion and ordered height enclosures. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command

private def certifyTorsionGrowthFactors (base : Name) (curve report factors : Ident)
    (full : TSyntax `term) : CommandElabM Unit := do
  let equal := rootIdent (base ++ `torsion_growth_polynomial_matches)
  let factorsEq := rootIdent (base ++ `torsion_growth_factors_match)
  checked (base ++ `torsion_growth_factors_match)
    (← `(List.ofFn ($full).factor = $factors)) (← `(by first | rfl | decide +kernel))
  let output ← catalogueFactName base `torsionGrowthFactors
  let degreeEq := rootIdent (base ++ `torsion_growth_degree_matches)
  emit (← `(def $(rootIdent output) : StoredTorsionGrowthFact $curve where
    field := $report
    factors := $factors
    presentation := $full
    polynomial_eq := $equal
    degree_eq := $degreeEq
    factors_eq := $factorsEq))
  auditAxioms output

private def certifyTorsionGrowthField (base : Name) (proofs : Option Ident) :
    CommandElabM Unit := do
  let factors ← bindStored base `torsionGrowthFactors `torsion_growth_factors (← `(List ℕ))
  let some report ← bindStored base `torsionGrowthField `torsion_growth_field
      (← `(TorsionGrowthFieldClaim)) | do
    if factors.isSome then
      throwError "torsion growth invariant factors require a field and degree"
    return
  if let some factors := factors then
    checked (base ++ `torsion_growth_factors_shape)
      (← `((∀ a ∈ $factors, 2 ≤ a) ∧ List.Pairwise (· ∣ ·) $factors))
      (← `(by decide +kernel))
  let shape := rootIdent (base ++ `torsion_growth_field_shape)
  checked (base ++ `torsion_growth_field_shape)
    (← `(($report).coefficients.length = ($report).degree + 1 ∧
      (($report).coefficients[($report).degree]?).getD 0 ≠ 0))
    (← `(by decide +kernel))
  checked (base ++ `torsion_growth_polynomial_degree)
    (← `(($report).polynomial.natDegree = ($report).degree))
    (← `(($report).natDegree_eq ($shape).1 ($shape).2))
  let degree := rootIdent (base ++ `torsion_growth_polynomial_degree)
  checked (base ++ `torsion_growth_finrank)
    (← `(Module.finrank ℚ (AdjoinRoot ($report).polynomial) = ($report).degree))
    (← `(finrank_quotient_span_eq_natDegree.trans $degree))
  let full ← if factors.isSome then attachedFact proofs `torsionGrowth else pure none
  let fieldProof ← match full with
    | some full => some <$> `(($full).toTorsionGrowthFieldFact)
    | none => attachedFact proofs `torsionGrowthField
  if factors.isSome && full.isNone then
    logInfo m!"Unverified {base} torsion_growth.torsion: supply the full torsion equivalence"
  let some evidence := fieldProof |
    logInfo m!"Unverified {base} torsion growth field: supply a proof of strict torsion growth"
    return
  let curve := rootIdent (base ++ `curve)
  let equal := rootIdent (base ++ `torsion_growth_polynomial_matches)
  checked (base ++ `torsion_growth_polynomial_matches)
    (← `(($evidence).polynomial = ($report).polynomial)) (← `(by rfl))
  let fact := rootIdent (← catalogueFactName base `torsionGrowthField)
  emit (← `(def $fact : TorsionGrowthFieldFact $curve := $evidence))
  checked (base ++ `torsion_growth_degree_matches)
    (← `(($fact).degree = ($report).degree))
    (← `((congrArg Polynomial.natDegree $equal).trans $degree))
  if let (some full, some factors) := (full, factors) then
    certifyTorsionGrowthFactors base curve report factors full

private def certifyCanonicalHeights (base : Name) (proofs : Option Ident) : CommandElabM Unit := do
  let some report ← bindStored base `canonicalHeights `heights
      (← `(CanonicalHeightsClaim)) | return
  let coordinatesName := base ++ `generators.coordinates
  unless (← getEnv).contains coordinatesName do
    throwError "heights requires the ordered generator list gens"
  let coordinates := rootIdent coordinatesName
  checked (base ++ `heights_shape)
    (← `(($report).reported.length = ($coordinates).length ∧
      ($report).errors.all (fun errors =>
        errors.length == ($coordinates).length &&
          errors.all (fun radius => decide (0 ≤ radius))) = true))
    (← `(by decide +kernel))
  let some evidence ← attachedFact proofs `canonicalHeights |
    logInfo m!"Unverified {base} heights: supply proved canonical height enclosures"
    return
  let points := rootIdent (base ++ `generators.point)
  let onCurve := rootIdent (base ++ `generators.points_on_curve)
  let equal := rootIdent (base ++ `heights_points_match)
  checked (base ++ `heights_points_match)
    (← `(List.ofFn (CanonicalHeightFacts.pointCoordinates ∘ ($evidence).1.2) =
      ($coordinates).map some))
    (← `(by first | rfl | decide +kernel))
  checked (base ++ `heights_report_matches)
    (← `(List.ofFn ($evidence).2.reported = ($report).reported ∧
      ($report).errors.getD (List.ofFn ($evidence).2.error) = List.ofFn ($evidence).2.error))
    (← `(by constructor <;> first | rfl | decide +kernel))
  let outputName ← catalogueFactName base `canonicalHeights
  let fact := rootIdent outputName
  emit (← `(def $fact : CanonicalHeightFacts $points :=
    CanonicalHeightFacts.ofPointListEq
      (source := ($evidence).1) (target := ⟨($coordinates).length, $points⟩)
      ($evidence).2 (($equal).trans
        (CanonicalHeightFacts.pointCoordinates_ofFn_mk $coordinates $onCurve).symm)))
  auditAxioms outputName

/-- Check the supplied field and canonical height claims using the same proof attachment. -/
def certifyExtensionData (base : Name) (proofs : Option Ident) : CommandElabM Unit := do
  certifyTorsionGrowthField base proofs
  certifyCanonicalHeights base proofs

end VerifiedLcalc.CertifyEC
