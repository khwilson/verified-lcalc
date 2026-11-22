/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.ConditionalAnalyticRank
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! # Attach the native analytic-rank reference value to a checked payload -/

public meta section

namespace VerifiedLcalc.CertifyEC
open Lean Elab Command EllipticCurve Modularity

/-- Check a native catalogue value only against a previously proved analytic rank. -/
def certifyCatalogueRank (base : Name) (central : Bool) : CommandElabM Unit := do
  let some input ← optionalInput (base ++ `witness) `catalogueAnalyticRank | return
  let witness := rootIdent (base ++ `witness)
  let curve := rootIdent (base ++ `curve)
  let val := rootIdent (base ++ `claimed_analytic_rank)
  let fact := rootIdent (base ++ `catalogue_rank)
  let hVal := rootIdent (base ++ `catalogue_rank_value_eq)
  let hn := rootIdent (base ++ `nonsingular)
  let r := rootIdent (base ++ `result)
  let v := rootIdent (base ++ `minimality)
  let hv := rootIdent (base ++ `minimality_valid)
  let d := rootIdent (base ++ `localData)
  let hd := rootIdent (base ++ `local_data_valid)
  let hN := rootIdent (base ++ `conductor_valid)
  let hw := rootIdent (base ++ `root_number_valid)
  let hp := rootIdent (base ++ `payload_correct)
  let hz := rootIdent (base ++ `excludes_zero)
  let rank ← if central then `(0) else `(1)
  emit (← `(def $val : Nat := $input))
  checked (base ++ `catalogue_rank_input_eq)
    (← `(($witness).catalogueAnalyticRank = some $val)) (← `(by rfl))
  checked (base ++ `catalogue_rank_value_eq)
    (← `($val = $rank)) (← `(by decide +kernel))
  let rankProof ← if central then
    `(ConditionalAnalyticRank.central $r $hn $v $hv $d $hd $hN $hw $hp $hz)
    else `(ConditionalAnalyticRank.derivative $r $hn $v $hv $d $hd $hN $hw $hp $hz)
  emit (← `(def $fact : ConditionalAnalyticRank $curve :=
    ⟨$val, fun m => by rw [$hVal:term]; exact $rankProof m⟩))
  checked (base ++ `catalogue_analytic_rank)
    (← `(∀ (m : ArithmeticModularRealization $curve),
      analyticOrderAt m.formL (1 : ℂ) = $val))
    (← `(($fact).correct))

end VerifiedLcalc.CertifyEC
