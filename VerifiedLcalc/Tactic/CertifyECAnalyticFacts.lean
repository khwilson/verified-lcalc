/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.Verification.SpecialValue
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! # Assemble typed numerical evidence from verified certificate declarations -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command EllipticCurve

/-- Collect the checked payload and the proof that takes an explicit arithmetic realization. -/
def analyticFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let env ← getEnv
  let w := rootIdent (base ++ `witness)
  let specialInput ← optionalInput (base ++ `witness) `specialLValue
  let specialClaimId ← if let some specialClaim := specialInput then do
    let claim := rootIdent (base ++ `claimed_special_value)
    emit (← `(def $claim : SpecialLValueClaim := $specialClaim))
    checked (base ++ `special_value_input_eq)
      (← `(($w).specialLValue = some $claim)) (← `(by rfl))
    checked (base ++ `special_value_error_nonnegative)
      (← `(0 ≤ ($claim).error)) (← `(by decide +kernel))
    pure (some claim)
  else pure none
  let resultName := base ++ `result
  let some result := env.find? resultName
    | do
      if specialInput.isSome then
        logInfo m!"Unverified {base}.special_value: no checked analytic payload"
      return ← `(({ } : AnalyticFacts $curve))
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
  let specialValue ← if let some claim := specialClaimId then
    if !env.contains hNName then
      logInfo m!"Unverified {base}.special_value: no checked arithmetic realization"
      `(none)
    else
      let order ← if central then `(0) else `(1)
      let bounds ← if central then `((($resultId).box.reLo, ($resultId).box.reHi))
        else `(($resultId).realDerivativeBounds)
      checked (base ++ `special_value_valid)
        (← `(($claim).Valid $order $bounds = true)) (← `(by decide +kernel))
      let rankValue ← `(($rank).get (by rfl))
      let enclosureValue ← `(($enclosure).get (by rfl))
      let fact ← if central then
        `(SpecialLValueFacts.ofCentralEnclosure $curve $claim $resultId $rankValue
          (by rfl) $enclosureValue $(rootIdent (base ++ `special_value_valid)))
        else
        `(SpecialLValueFacts.ofDerivativeEnclosure $curve $claim $resultId $rankValue
          (by rfl) $enclosureValue $(rootIdent (base ++ `special_value_valid)))
      `(some $fact)
  else `(none)
  if central then
    `(({ central := $numeric, rank := $rank, specialValue := $specialValue } :
      AnalyticFacts $curve))
  else
    `(({ derivative := $numeric, rank := $rank, specialValue := $specialValue } :
      AnalyticFacts $curve))

end VerifiedLcalc.CertifyEC
