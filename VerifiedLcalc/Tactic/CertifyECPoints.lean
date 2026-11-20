module

public import VerifiedLcalc.EllipticCurve.InfiniteOrder
public import VerifiedLcalc.EllipticCurve.PointIndependence
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-!
# Certifying infinite order and algebraic-rank lower bounds

These commands consume points already checked by `certify_ec`.

* `certify_ec_infinite_order Name for Curve at i` checks the Nagell–Lutz
  discriminant obstruction at the supplied integer point of index `i`. It
  exports `Name.point`, `Name.infinite_order`, and `Name.algebraic_rank_lower_bound`.
  A failed obstruction is inconclusive and rejects the command atomically.
* `certify_ec_rank Name for Curve from [i₁, …, iₙ] using proof` selects points
  by natural-number indices and checks a proof of their ℤ-linear independence.
  It exports `Name.points`, `Name.points_independent`, and
  `Name.algebraic_rank_lower_bound`. Indices are bounds-checked, never reduced
  modulo the point count. Independence is an actual proof obligation: point
  membership, pairwise distinctness, individual infinite order, and unverified
  LMFDB rank/generator metadata cannot replace it.

The conclusion uses Mathlib's cardinal-valued `Module.rank ℤ` on the rational
point group. No finite-generation assumption, modularity or BSD is needed.
These commands perform no search and audit every theorem against standard
Lean axioms. Compile their containing module for reusable `.olean` theorems.
-/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve

private def curveNames (curve : Ident) : CommandElabM (Ident × Ident × Ident × Ident) := do
  let resolved ← liftTermElabM <| Term.elabTerm (mkIdent (curve.getId ++ `witness)) none
  let some name := resolved.getAppFn.constName? | throwError "Expected a certified curve namespace"
  let base := name.getPrefix
  return (rootIdent (base ++ `witness), rootIdent (base ++ `curve), rootIdent (base ++ `point),
    rootIdent (base ++ `points_on_curve))

/-- Check infinite order of one previously certified integral point. -/
def certifyInfiniteOrder (name : Name) (curveName : Ident) (index : TSyntax `term) :
    CommandElabM Unit := atomic do
  let base := (← getCurrNamespace) ++ name.eraseMacroScopes
  let (w, curve, point, onCurve) ← curveNames curveName
  let ix := rootIdent (base ++ `index)
  emit (← `(def $ix : Nat := $index))
  let hb := rootIdent (base ++ `index_valid)
  checked (base ++ `index_valid)
    (← `($ix < (($w).integralCoordinates.getD []).length)) (← `(by decide +kernel))
  let hcheck := rootIdent (base ++ `infinite_order_valid)
  -- Explicit getElem proofs keep bounds separate from the finite arithmetic check.
  let x ← `(((($w).integralCoordinates.getD [])[$ix]'$hb).1)
  let y ← `(((($w).integralCoordinates.getD [])[$ix]'$hb).2)
  checked (base ++ `infinite_order_valid)
    (← `(infiniteOrderCheck $curve $x $y = true)) (← `(by decide +kernel))
  let p := rootIdent (base ++ `point)
  emit (← `(def $p := $point ⟨$ix, $hb⟩))
  let ht := rootIdent (base ++ `infinite_order)
  checked (base ++ `infinite_order) (← `(¬ IsOfFinAddOrder $p)) (← `(by
    exact infiniteOrderCheck_sound $curve $x $y
      ($onCurve _ _ (List.getElem_mem $hb)) $hcheck))
  checked (base ++ `algebraic_rank_lower_bound)
    (← `((1 : Cardinal) ≤ Module.rank ℤ (($curve).baseChange ℚ).toAffine.Point))
    (← `(algebraic_rank_pos_of_infinite_order $p $ht))
  logInfo m!"Certified {base}.infinite_order and {base}.algebraic_rank_lower_bound"

/-- Verify an independence proof for a selected family of supplied points. -/
def certifyRankLowerBound (name : Name) (curveName : Ident)
    (indices proof : TSyntax `term) : CommandElabM Unit := atomic do
  let base := (← getCurrNamespace) ++ name.eraseMacroScopes
  let (w, curve, point, _) ← curveNames curveName
  let ix := rootIdent (base ++ `indices)
  emit (← `(abbrev $ix : List Nat := $indices))
  let hb := rootIdent (base ++ `indices_valid)
  checked (base ++ `indices_valid)
    (← `(∀ i ∈ $ix, i < (($w).integralCoordinates.getD []).length))
    (← `(by decide +kernel))
  -- Give callers a concrete Fin n, so instance search can see empty and
  -- singleton families. The reified size is checked again in the kernel.
  let count ← liftTermElabM do
    let size ← Term.elabTerm (← `(($ix).length)) (some (mkConst ``Nat))
    let some n ← (evalNat (← whnf size)).run
      | throwError "Expected a closed list of point indices"
    return (⟨Syntax.mkNumLit (toString n)⟩ : TSyntax `term)
  checked (base ++ `point_count_eq) (← `(($ix).length = $count)) (← `(by decide +kernel))
  let ps := rootIdent (base ++ `points)
  emit (← `(def $ps (i : Fin $count) :
      (($curve).baseChange ℚ).toAffine.Point :=
    $point ⟨($ix)[i], $hb _ (List.getElem_mem i.isLt)⟩))
  let hi := rootIdent (base ++ `points_independent)
  checked (base ++ `points_independent) (← `(LinearIndependent ℤ $ps)) proof
  checked (base ++ `algebraic_rank_lower_bound)
    (← `((($ix).length : Cardinal) ≤ Module.rank ℤ (($curve).baseChange ℚ).toAffine.Point))
    (← `(algebraic_rank_lower_bound $ps $hi))
  logInfo m!"Certified {base}.algebraic_rank_lower_bound from an independent point family"

syntax (name := certifyECInfiniteOrder)
  "certify_ec_infinite_order " ident " for " ident " at " term : command
syntax (name := certifyECRank)
  "certify_ec_rank " ident " for " ident " from " term " using " term : command

@[command_elab certifyECInfiniteOrder] def elabCertifyECInfiniteOrder : CommandElab := fun stx => do
  let `(certify_ec_infinite_order $name:ident for $curve:ident at $index:term) := stx
    | throwUnsupportedSyntax
  certifyInfiniteOrder name.getId curve index

@[command_elab certifyECRank] def elabCertifyECRank : CommandElab := fun stx => do
  let `(certify_ec_rank $name:ident for $curve:ident from $indices:term using $proof:term) := stx
    | throwUnsupportedSyntax
  certifyRankLowerBound name.getId curve indices proof

end VerifiedLcalc.CertifyEC
