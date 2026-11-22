/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! # Assemble typed numerical evidence from verified certificate declarations -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command EllipticCurve

/-- Collect the checked payload and the proof that takes an explicit arithmetic realization. -/
def analyticFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let env ← getEnv
  let resultName := base ++ `result
  let some result := env.find? resultName
    | return ← `(({ } : AnalyticFacts $curve))
  let resultId := rootIdent resultName
  let hcurve := rootIdent (base ++ `result_curve_eq)
  let hp := rootIdent (base ++ `payload_correct)
  let hz := rootIdent (base ++ `excludes_zero)
  let central := result.type.isConstOf ``CentralResult
  let hNName := base ++ `conductor_valid
  let rank ← if env.contains hNName then do
    let hn := rootIdent (base ++ `nonsingular)
    let v := rootIdent (base ++ `minimality)
    let hv := rootIdent (base ++ `minimality_valid)
    let d := rootIdent (base ++ `localData)
    let hd := rootIdent (base ++ `local_data_valid)
    let hN := rootIdent hNName
    let hw := rootIdent (base ++ `root_number_valid)
    if central then
      `(some ⟨0, fun m => CentralNumericalFact.rank_with_realization
        (⟨$resultId, $hcurve, $hp, $hz⟩ : CentralNumericalFact $curve)
        $hn $v $hv $d $hd $hN $hw m⟩)
    else
      `(some ⟨1, fun m => DerivativeNumericalFact.rank_with_realization
        (⟨$resultId, $hcurve, $hp, $hz⟩ : DerivativeNumericalFact $curve)
        $hn $v $hv $d $hd $hN $hw m⟩)
  else `(none)
  if central then
    `(({ central := some ⟨$resultId, $hcurve, $hp, $hz⟩, rank := $rank } : AnalyticFacts $curve))
  else
    `(({ derivative := some ⟨$resultId, $hcurve, $hp, $hz⟩, rank := $rank } : AnalyticFacts $curve))

end VerifiedLcalc.CertifyEC
