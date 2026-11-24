/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Certificate.Support.ExtensionData
import Mathlib.Data.List.OfFn

/-! Check number-field presentations and ordered height enclosures with Lean evidence. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command

private def certifyTorsionGrowthField (base : Name) (proofs : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `torsionGrowthField `torsion_growth_field
      (← `(TorsionGrowthFieldClaim)) | return
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
  let some evidence ← attachedFact proofs `torsionGrowthField |
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
