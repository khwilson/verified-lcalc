/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certification.IntegralPointCount
public import VerifiedLcalc.Tactic.CertifyECCommon

/-! Verify complete integral counts from checked fibers and supplied abscissa support. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command

/-- Compare the supplied count with the complete union of the checked fibers. -/
def certifyCompleteIntegralPoints (base : Name) (support count : Option (TSyntax `term)) :
    CommandElabM Unit := do
  if let some claimed := count then
    let listedRoots ← optionalInput (base ++ `witness) `integralFiberRoots
    let witness := rootIdent (base ++ `witness)
    let curve := rootIdent (base ++ `curve)
    let observed := rootIdent (base ++ `listed_integral_coordinates)
    if let some roots := listedRoots then
      emit (← `(def $observed : Finset (ℤ × ℤ) :=
        (($witness).integralCoordinates.getD []).toFinset ∪ integralFiberSolutions $curve $roots))
    else
      emit (← `(def $observed : Finset (ℤ × ℤ) :=
        (($witness).integralCoordinates.getD []).toFinset))
    checked (base ++ `listed_integral_count_lower_bound)
      (← `(($observed).card ≤ $claimed)) (← `(by decide +kernel))
  let some input := support |
    if count.isSome then
      logInfo m!"Unverified {base} num_int_pts: supply exhaustive abscissa support"
    return
  let validName := base ++ `integral_fiber_roots_valid
  unless (← getEnv).contains validName do
    logInfo m!"Unverified {base} num_int_pts: supply the checked integral fiber roots"
    return
  let curve := rootIdent (base ++ `curve)
  let evidence := rootIdent (base ++ `integral_x_support)
  let roots := rootIdent (base ++ `integral_fiber_roots)
  let valid := rootIdent validName
  emit (← `(def $evidence : IntegralXSupport $curve := $input))
  let supported := rootIdent (base ++ `integral_x_support_checked)
  checked (base ++ `integral_x_support_checked)
    (← `((($evidence).xs.all (fun x => decide (x ∈ ($roots).map Prod.fst))) = true))
    (← `(by decide +kernel))
  let covers ← `(fun x hx => of_decide_eq_true (List.all_eq_true.mp $supported x hx))
  let coordinates := rootIdent (base ++ `complete_integral_coordinates)
  emit (← `(def $coordinates := integralFiberSolutions $curve $roots))
  let complete := rootIdent (base ++ `integral_points_complete)
  checked (base ++ `integral_points_complete)
    (← `(∀ p : ℤ × ℤ, p ∈ $coordinates ↔ ($curve).toAffine.Equation p.1 p.2))
    (← `(mem_integralFiberSolutions_iff $valid $evidence $covers))
  let value := rootIdent (base ++ `integral_points_count)
  let inputCount ← count.getDM `(($coordinates).card)
  emit (← `(def $value : ℕ := $inputCount))
  let coordinateCard := rootIdent (base ++ `integral_coordinates_count)
  checked (base ++ `integral_coordinates_count)
    (← `(($coordinates).card = $value)) (← `(by decide +kernel))
  let exactCard ← `(integralPoints_finite_and_natCard_eq_fiber_count $valid $evidence $covers)
  let groupCard := rootIdent (base ++ `num_int_pts)
  checked (base ++ `num_int_pts) (← `(Nat.card ($curve).integralPoints = $value))
    (← `(($exactCard).2.trans $coordinateCard))
  let result := rootIdent (base ++ `integral_point_certificate)
  emit (← `(def $result : CompleteIntegralPointFacts $curve :=
    ⟨$evidence, $coordinates, $complete, $value, $coordinateCard, ($exactCard).1, $groupCard⟩))

end VerifiedLcalc.CertifyEC
