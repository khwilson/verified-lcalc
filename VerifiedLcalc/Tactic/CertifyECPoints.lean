module

public import VerifiedLcalc.EllipticCurve.InfiniteOrder
public import VerifiedLcalc.EllipticCurve.PointIndependence
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-!
# Internal point-certification components for `certify_ec`

The public interface is `VerifiedLcalc.Tactic.CertifyEC`. These helpers verify
infinite order at an integral-point index and integer independence of a selected
family. `certify_ec` dispatches to them from its single optional-field witness,
using the same pipeline for Lean, JSON, and programmatic inputs.

Every mathematical claim uses the actual rational point group and Mathlib's
module rank. No finite-generation, modularity or BSD assumption is needed.
A failed Nagell–Lutz obstruction is inconclusive; independence of a family
requires an actual proof, rather than distinctness or individual infinite order.
All generated theorems are checked and audited against standard Lean axioms.
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

end VerifiedLcalc.CertifyEC
