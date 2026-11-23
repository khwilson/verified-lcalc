/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Tactic.CertifyECIntegralPoints

/-! Verify Lean rank evidence and bind it to the raw claims for the same equation. -/

public meta section

namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve

private def pointRankLowerBound (base : Name) :
    CommandElabM (Option (TSyntax `term × Ident)) := do
  let env ← getEnv
  let independent := base ++ `algebraic.indices
  let infinite := base ++ `infiniteOrder.point0.algebraic_rank_lower_bound
  if env.contains independent then
    let n ← `(($(rootIdent independent)).length)
    let empty ← liftTermElabM do
      let size ← Lean.Elab.Term.elabTerm n (some (mkConst ``Nat))
      Meta.isDefEq size (mkNatLit 0)
    unless empty do
      return some (n, rootIdent (base ++ `algebraic_rank_lower_bound))
  if env.contains infinite then
    return some (← `(1), rootIdent infinite)
  return none

private def checkRawRankConsistency (base : Name) (claim interval : Option (TSyntax `term))
    (point : Option (TSyntax `term × Ident)) : CommandElabM Unit := do
  if let some bounds := interval then
    checked (base ++ `algebraic_rank_input_order)
      (← `(($bounds).1 ≤ ($bounds).2)) (← `(by decide +kernel))
    if let some n := claim then
      checked (base ++ `algebraic_rank_in_input_bounds)
        (← `(($bounds).1 ≤ $n ∧ $n ≤ ($bounds).2)) (← `(by decide +kernel))
    if let some (lower, _) := point then
      checked (base ++ `algebraic_rank_bounds_respect_points)
        (← `($lower ≤ ($bounds).2)) (← `(by decide +kernel))
  if let (some n, some (lower, _)) := (claim, point) then
    checked (base ++ `algebraic_rank_respects_points) (← `($lower ≤ $n)) (← `(by decide +kernel))

private def certifyRankClaims (base : Name) (curve : Ident) (attachment : Option Ident) :
    CommandElabM Unit := do
  let w := base ++ `witness
  let claim ← optionalInput w `algebraicRank
  let interval ← optionalInput w `algebraicRankBounds
  if claim.isNone && interval.isNone && attachment.isNone then return
  let point ← pointRankLowerBound base
  checkRawRankConsistency base claim interval point
  let fact ← if let some input := attachment then do
    let selected ← `(($input).algebraicRank)
    if ← hasOptionalProof selected `algebraic_rank then
      some <$> `(($selected).get (by decide +kernel))
    else pure none
  else pure none
  let some fact := fact |
    if claim.isSome || interval.isSome then
      logInfo m!"Unverified {base} Mordell–Weil rank: supply a proved rank interval"
    return
  let fact ← if let some (lower, h) := point then `(($fact).raiseLower $lower $h)
    else pure fact
  let finrank ← `(Module.finrank ℤ (($curve).baseChange ℚ).toAffine.Point)
  let value := rootIdent (base ++ `mordell_weil_bounds)
  let given ← interval.getDM `((($fact).lower, ($fact).upper))
  emit (← `(def $value : Nat × Nat := $given))
  checked (base ++ `algebraic_rank_bounds)
    (← `((($value).1 : Nat) ≤ $finrank ∧ $finrank ≤ (($value).2 : Nat)))
    (← `(by
      let bounds := ($fact).weaken ($value).1 ($value).2 (by decide +kernel) (by decide +kernel)
      exact ⟨bounds.lower_le_finrank, bounds.finrank_le_upper⟩))
  let hbounds := rootIdent (base ++ `algebraic_rank_bounds)
  let witness := rootIdent (base ++ `algebraic_rank_witness)
  emit (← `(def $witness : AlgebraicRankBounds (($curve).baseChange ℚ) :=
    ⟨($value).1, ($value).2, ($hbounds).1, ($hbounds).2⟩))
  let singleton ← liftTermElabM do
    let lower ← Lean.Elab.Term.elabTerm (← `(($fact).lower)) (some (mkConst ``Nat))
    let upper ← Lean.Elab.Term.elabTerm (← `(($fact).upper)) (some (mkConst ``Nat))
    Meta.isDefEq lower upper
  if let some n := claim then
    checked (base ++ `algebraic_rank_claim_consistent)
      (← `(($fact).lower ≤ $n ∧ $n ≤ ($fact).upper)) (← `(by decide +kernel))
  unless singleton do
    if claim.isSome then
      logInfo m!"Unverified {base} exact Mordell–Weil rank: interval is not a singleton"
    return
  let n := rootIdent (base ++ `mordell_weil_rank)
  let given ← claim.getDM `(($fact).lower)
  emit (← `(def $n : Nat := $given))
  checked (base ++ `algebraic_rank) (← `($finrank = $n))
    (← `(by
      have h : ($fact).lower = $n := by decide +kernel
      exact (($fact).rank_eq_of_equal (by decide +kernel)).trans h))

/-- Elaborate one shared proof attachment, check any rank data, and pass the equation proofs on. -/
def certifyProofAttachment (base : Name) (input : Option (TSyntax `term)) :
    CommandElabM (Option (TSyntax `term)) := do
  let curve := rootIdent (base ++ `curve)
  let attachment ← input.mapM fun raw => do
    let name := rootIdent (base ++ `integral_proofs)
    emit (← `(def $name : IntegralCurveProofs $curve := by
      first
      | exact $raw
      | exact { toEllipticProofs := $raw }))
    pure name
  certifyRankClaims base curve attachment
  let support ← if let some facts := attachment then do
    let selected ← `(($facts).integralXSupport)
    if ← hasOptionalProof selected `integral_x_support then
      some <$> `(($selected).get (by decide +kernel))
    else pure none
  else pure none
  let count ← optionalInput (base ++ `witness) `numIntegralPoints
  certifyCompleteIntegralPoints base support count
  attachment.mapM fun facts => `(($facts).toEllipticProofs)

end VerifiedLcalc.CertifyEC
