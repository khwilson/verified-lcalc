import CertifiedCurves.Direct
import Lean

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Exact computational checks; failure of this sufficient test is inconclusive.
example : infiniteOrderCheck DirectPoints.curve 6 14 = true := by decide +kernel
example : infiniteOrderCheck DirectPoints.curve 0 0 = false := by decide +kernel

-- A genuine size-two independence certificate for the general linear-algebra
-- engine. The images are actual vectors, rather than unrelated numeric data.
example : LinearIndependent ℤ (fun i : Fin 2 => Pi.single i (1 : ℚ)) := by
  apply independent_of_separating_matrix _
    (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℤ] (Fin 2 → ℚ))
  norm_num [Matrix.det_fin_two, Pi.single_apply]

example : ¬ IsOfFinAddOrder DirectPoints.infiniteOrder.point0.point := DirectPoints.infiniteOrder.point0.infinite_order
example : (1 : Cardinal) ≤ Module.rank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectPoints.algebraic_rank_lower_bound

example : DirectPoints.witness.infiniteOrderPoints = some DirectPoints.infinite_order_indices :=
  DirectPoints.infinite_order_points_eq
example : DirectPoints.witness.independentPoints = some DirectPoints.algebraic.indices :=
  DirectPoints.independent_points_eq

certify_ec EmptyFamily from
  { equation := DirectPoints.curve, independentPoints := some [] }
  with_independence (by exact linearIndependent_empty_type)

certify_ec JSONFamily from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"integral_points":[[6,14]],"infinite_order_points":[0],"independent_points":[0]}"#
  with_independence (by
    apply LinearIndependent.of_subsingleton' (0 : Fin 1)
    intro a ha
    have hp : a • JSONFamily.infiniteOrder.point0.point = 0 := by
      simpa [JSONFamily.algebraic.points, JSONFamily.algebraic.indices,
        JSONFamily.infiniteOrder.point0.point, JSONFamily.infiniteOrder.point0.index,
        JSONFamily.infinite_order_indices] using ha
    by_contra hn
    exact JSONFamily.infiniteOrder.point0.infinite_order
      (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, hp⟩))

example : (1 : Cardinal) ≤ Module.rank ℤ (JSONFamily.curve.baseChange ℚ).toAffine.Point :=
  JSONFamily.algebraic_rank_lower_bound

run_cmd do
  IO.FS.writeFile ".lake/unified-point-requests.json"
    r#"{"ainvs":[0,0,1,-1,0],"independent_points":[]}"#

certify_ec FileFamily from_json "../.lake/unified-point-requests.json"
  with_independence (by exact linearIndependent_empty_type)

certify_ec MultipleOrders from
  { equation := DirectPoints.curve, integralCoordinates := some [(6, 14), (6, -15)],
    infiniteOrderPoints := some [0, 1] }

example : ¬ IsOfFinAddOrder (MultipleOrders.point ⟨1, by decide⟩) :=
  MultipleOrders.infiniteOrder.point1.infinite_order

run_cmd do
  let input ← CertifyEC.jsonInput
    r#"{"ainvs":[0,0,1,-1,0],"integral_points":[[6,14]],"infinite_order_points":[0]}"#
  CertifyEC.certifyAtomic `ProgrammaticOrder input
  let family ← CertifyEC.jsonInput r#"{"ainvs":[0,0,1,-1,0],"independent_points":[]}"#
  CertifyEC.certifyAtomic `ProgrammaticFamily family
    (some (← `(by exact linearIndependent_empty_type)))

certify_ec TorsionData from
  { equation := ⟨0, -1, 1, -10, -20⟩
    integralCoordinates := some [(5, 5)] }

meta def expectPointRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Invalid point certificate accepted: {name}"
  for suffix in [`witness, `supplied, `curve, `point, `infinite_order_indices,
      `infinite_order_count_eq, `infinite_order_points_eq, `independent_points_eq,
      `index, `index_valid, `infinite_order_valid, `infinite_order,
      `indices, `indices_valid, `point_count_eq, `points, `points_independent,
      `algebraic_rank_lower_bound] do
    if env.contains (name ++ suffix) then
      throwError "Rejected point certificate leaked {name ++ suffix}"
  for child in [`infiniteOrder.point0, `algebraic] do
    for suffix in [`index, `point, `indices, `points, `points_independent,
        `algebraic_rank_lower_bound] do
      if env.contains (name ++ child ++ suffix) then
        throwError "Rejected curve certificate leaked a point component"

run_cmd do
  expectPointRejected `TorsionRejected
    (← `(certify_ec TorsionRejected from
      { TorsionData.witness with infiniteOrderPoints := some [0] }))
  expectPointRejected `IndexRejected
    (← `(certify_ec IndexRejected from
      { equation := DirectPoints.curve, integralCoordinates := some [(6, 14)],
        infiniteOrderPoints := some [1] }))
  expectPointRejected `InsufficientTest
    (← `(certify_ec InsufficientTest from
      { equation := DirectPoints.curve, integralCoordinates := some [(0, 0)],
        infiniteOrderPoints := some [0] }))
  expectPointRejected `DuplicateFamily
    (← `(certify_ec DuplicateFamily from
      { equation := DirectPoints.curve, integralCoordinates := some [(6, 14)],
        independentPoints := some [0, 0] }
      with_independence DirectPoints.algebraic.points_independent))
  expectPointRejected `FamilyIndexRejected
    (← `(certify_ec FamilyIndexRejected from
      { equation := DirectPoints.curve, independentPoints := some [2] }
      with_independence DirectPoints.algebraic.points_independent))
  expectPointRejected `CombinedFailure
    (← `(certify_ec CombinedFailure from
      { equation := DirectPoints.curve, integralCoordinates := some [(6, 14)],
        infiniteOrderPoints := some [0], independentPoints := some [0, 0] }
      with_independence DirectPoints.algebraic.points_independent))
  expectPointRejected `MissingIndependence
    (← `(certify_ec MissingIndependence from
      { equation := DirectPoints.curve, integralCoordinates := some [(6, 14)],
        independentPoints := some [0] }))
  expectPointRejected `UnusedProof
    (← `(certify_ec UnusedProof from { equation := DirectPoints.curve }
      with_independence DirectPoints.algebraic.points_independent))

-- JSON uses the very same dispatch, including namespaced output.
namespace ScopedPoints
certify_ec Order from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"integral_points":[[6,14]],"infinite_order_points":[0]}"#
end ScopedPoints

run_cmd do
  for name in [``infiniteOrderCheck_sound, ``algebraic_rank_lower_bound,
      ``algebraic_finrank_lower_bound, ``independent_singleton_of_infinite_order,
      ``independent_of_separating_matrix, ``algebraic_rank_lower_bound_of_separating_matrix,
      `DirectPoints.infiniteOrder.point0.infinite_order, `DirectPoints.infiniteOrder.point0.algebraic_rank_lower_bound,
      `DirectPoints.algebraic.points_independent, `DirectPoints.algebraic_rank_lower_bound,
      `ScopedPoints.Order.infiniteOrder.point0.infinite_order,
      `MultipleOrders.infiniteOrder.point1.infinite_order,
      `JSONFamily.algebraic_rank_lower_bound, `ProgrammaticFamily.algebraic_rank_lower_bound,
      `FileFamily.algebraic_rank_lower_bound, `ProgrammaticOrder.algebraic_rank_lower_bound] do
    for ax in ← liftTermElabM <| Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected point/rank certificate axiom: {ax}"

#eval show IO Unit from do
  for indices in ["[-1]", "[8192]", "[1.5]"] do
    let text := "{\"ainvs\":[0,0,1,-1,0],\"infinite_order_points\":" ++ indices ++ "}"
    match CurveDataJson.parse text with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "Invalid point indices accepted")
