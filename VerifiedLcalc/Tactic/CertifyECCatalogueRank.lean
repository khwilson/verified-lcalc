/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECRecord
public meta import Lean

/-! # Compare an optional catalogue value with the typed analytic rank -/

public meta section

namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Modularity

/-- Bind a native analytic-rank field to the independently checked typed rank. -/
def certifyCatalogueRank (base : Name) : CommandElabM Unit := do
  let some input ← optionalInput (base ++ `witness) `catalogueAnalyticRank | return
  unless (← getEnv).contains (base ++ `analytic_rank) do
    logInfo m!"Unverified {base} analytic_rank: supply a complete checked analytic payload"
    return
  let witness := rootIdent (base ++ `witness)
  let curve := rootIdent (base ++ `curve)
  let certificate := rootIdent (base ++ `certificate)
  let val := rootIdent (base ++ `claimed_analytic_rank)
  let fact := rootIdent (base ++ `catalogue_rank)
  let hSome := rootIdent (base ++ `catalogue_rank_available)
  let hVal := rootIdent (base ++ `catalogue_rank_value_eq)
  emit (← `(def $val : Nat := $input))
  checked (base ++ `catalogue_rank_input_eq)
    (← `(($witness).catalogueAnalyticRank = some $val)) (← `(by rfl))
  checked (base ++ `catalogue_rank_available)
    (← `((($certificate).analytic.rank).isSome = true)) (← `(by rfl))
  emit (← `(def $fact : ConditionalAnalyticRank $curve :=
    (($certificate).analytic.rank).get $hSome))
  checked (base ++ `catalogue_rank_value_eq)
    (← `(($fact).val = $val)) (← `(by decide +kernel))
  checked (base ++ `catalogue_analytic_rank)
    (← `(∀ (m : ArithmeticModularRealization $curve),
      analyticOrderAt m.formL (1 : ℂ) = $val))
    (← `(fun m => by rw [← $hVal:term]; exact ($fact).correct m))

end VerifiedLcalc.CertifyEC
