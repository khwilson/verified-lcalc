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
  let numeric ← if central then
    `(({ result := $resultId, result_curve := $hcurve, payload := $hp, excludes_zero := $hz } :
      CentralNumericalFact $curve))
  else
    `(({ result := $resultId, result_curve := $hcurve, payload := $hp, excludes_zero := $hz } :
      DerivativeNumericalFact $curve))
  let hNName := base ++ `conductor_valid
  let (rank, enclosure) ← if env.contains hNName then do
    let hn := rootIdent (base ++ `nonsingular)
    let v := rootIdent (base ++ `minimality)
    let hv := rootIdent (base ++ `minimality_valid)
    let d := rootIdent (base ++ `localData)
    let hd := rootIdent (base ++ `local_data_valid)
    let hN := rootIdent hNName
    let hw := rootIdent (base ++ `root_number_valid)
    if central then
      let rank ← `(some ⟨0, fun m => CentralNumericalFact.rank_with_realization
        $numeric $hn $v $hv $d $hd $hN $hw m⟩)
      let enclosure ← `(some ⟨fun m => CentralNumericalFact.contains_with_realization
        $numeric $hn $v $hv $d $hd $hN $hw m⟩)
      pure (rank, enclosure)
    else
      let rank ← `(some ⟨1, fun m => DerivativeNumericalFact.rank_with_realization
        $numeric $hn $v $hv $d $hd $hN $hw m⟩)
      let enclosure ← `(some ⟨fun m => DerivativeNumericalFact.contains_with_realization
        $numeric $hn $v $hv $d $hd $hN $hw m⟩)
      pure (rank, enclosure)
  else pure (← `(none), ← `(none))
  let numeric ← `(some { $numeric with enclosure := $enclosure })
  if central then
    `(({ central := $numeric, rank := $rank } : AnalyticFacts $curve))
  else
    `(({ derivative := $numeric, rank := $rank } : AnalyticFacts $curve))

end VerifiedLcalc.CertifyEC
