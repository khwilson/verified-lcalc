/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Verification.DegreeTwoIsogenyRaw
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! # Attach a checked degree-two rational edge to `certify_ec` -/

public meta section

namespace VerifiedLcalc.CertifyEC
open Lean Elab Command TauCeti

/-- Check the optional edge target and a proof indexed by the exact two equations. -/
def certifyIsogenyEdge (base : Name) (proof : Option (TSyntax `term)) : CommandElabM Unit := do
  let some input ← optionalInput (base ++ `witness) `isogenyEdge
    | if proof.isSome then throwError "with_isogeny requires an isogeny_edge claim" else return
  let witness := rootIdent (base ++ `witness)
  let source := rootIdent (base ++ `curve)
  let claim := rootIdent (base ++ `claimed_isogeny_edge)
  let target := rootIdent (base ++ `isogeny_target)
  let fact := rootIdent (base ++ `degree_two_isogeny)
  let validDegree := rootIdent (base ++ `isogeny_degree_valid)
  emit (← `(def $claim : IsogenyEdgeClaim := $input))
  checked (base ++ `isogeny_edge_eq)
    (← `(($witness).isogenyEdge = some $claim)) (← `(by rfl))
  checked (base ++ `isogeny_degree_valid)
    (← `(($claim).degree = 2)) (← `(by decide +kernel))
  emit (← `(def $target : WeierstrassCurve ℤ := ($claim).target))
  let kernel ← liftTermElabM do
    let value ← Lean.Meta.whnf (mkApp (mkConst ``IsogenyEdgeClaim.kernelX)
      (mkConst (base ++ `claimed_isogeny_edge)))
    match value.getAppFn.constName? with
    | some ``Option.some => pure true
    | some ``Option.none => pure false
    | _ => throwError "Expected a closed isogeny kernel option"
  let rawProof ← if kernel then do
    let x ← `((($claim).kernelX).get (by rfl))
    let term ← `(by
      letI : (($target).baseChange ℚ).IsElliptic :=
        ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩
      exact DegreeTwoIsogenyFact.ofZeroY $source $target $x (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by
          apply WeierstrassCurve.ext <;> decide +kernel) (by
          simp only [WeierstrassCurve.j_eq]
          decide +kernel))
    pure (some term)
  else pure none
  let some selected := proof.orElse (fun _ => rawProof)
    | throwError "isogeny_edge requires kernel_x or a with_isogeny proof"
  if let some raw := rawProof then
    if proof.isSome then
      let rawFact := rootIdent (base ++ `raw_degree_two_isogeny)
      emit (← `(noncomputable def $rawFact : DegreeTwoIsogenyFact $source $target := $raw))
      checked (base ++ `raw_isogeny_degree) (← `(($rawFact).isogeny.degree = 2))
        (← `(($rawFact).degree_eq))
  emit (← `(noncomputable def $fact : DegreeTwoIsogenyFact $source $target := $selected))
  checked (base ++ `isogeny_degree)
    (← `(($fact).isogeny.degree = ($claim).degree))
    (← `(($fact).degree_eq.trans ($validDegree).symm))
  checked (base ++ `isogeny_minimum_degree)
    (← `(IsLeast (Set.range fun φ :
      Isogeny (($source).baseChange ℚ).toAffine (($target).baseChange ℚ).toAffine => φ.degree) 2))
    (← `(($fact).isLeast_degree))

end VerifiedLcalc.CertifyEC
