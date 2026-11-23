import CertifiedCurves.Data
import CertifiedCurves.Json
import Lean

/-! # Verification and rollback tests for stored elliptic-curve data -/

open Lean Elab Command VerifiedLcalc

set_option maxRecDepth 100000

-- Ordinary mathematical coefficients, including split/nonsplit bad primes.
example : (Data11.curve.baseChange ℚ).LFunction 2 = -2 :=
  Data11.ap_correct 2 (-2) (by decide +kernel)
example : (Data11.curve.baseChange ℚ).LFunction 11 = 1 :=
  Data11.ap_correct 11 1 (by decide +kernel)
example : (Data37.curve.baseChange ℚ).LFunction 37 = -1 :=
  Data37.ap_correct 37 (-1) (by decide +kernel)
example : (Data37.curve.baseChange ℚ).LFunction 97 = 4 :=
  Data37.ap_correct 97 4 (by decide +kernel)

-- Membership on precisely the given model, using TauCeti's point type and set.
example : Data37.curve.toAffine.Equation 6 (-15) :=
  Data37.points_on_curve 6 (-15) (by decide +kernel)
example : Data37.point ⟨9, by decide⟩ ∈ Data37.curve.integralPoints :=
  Data37.point_integral _

-- Direct Lean data, an additive bad prime, and empty lists are supported.
certify_ec AdditiveData from
  { equation := ⟨0, 0, 0, -1, 0⟩, primeCoefficients := some [(2, 0)],
    integralCoordinates := some [(0, 0)] }
example : (AdditiveData.curve.baseChange ℚ).LFunction 2 = 0 :=
  AdditiveData.ap_correct 2 0 (by decide +kernel)

certify_ec EmptyData from_json_string
  r#"{"schema":"lcalc.ec-data.v1","ainvs":["0","0","1","-1","0"],
      "ap":[],"integral_points":[]}"#

-- No schema, no empty sections, raw LMFDB fields and unrelated metadata.
certify_ec RawData from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"aplist":[-2,-3,-2],"xcoord_integral_points":[-1,0,1,2,6],
      "lmfdb_label":"37.a1","analytic_rank":1,"unrelated":{"note":"metadata"}}"#
example : (RawData.curve.baseChange ℚ).LFunction 3 = -3 :=
  RawData.ap_correct 3 (-3) (by decide +kernel)
example : RawData.curve.toAffine.Equation 6 14 :=
  RawData.points_on_curve 6 14 (by decide +kernel)

-- The odd linear term gives the two unequal roots 14 and -15 at x = 6.
example : RawData.integral_y_fiber ⟨4, by decide⟩ = ({14, -15} : Finset ℤ) := by
  decide +kernel
example (y : ℤ) : y ∈ RawData.integral_y_fiber ⟨0, by decide⟩ ↔
    RawData.curve.toAffine.Equation (-1) y :=
  RawData.integral_y_fiber_complete _ y

certify_ec EmptyFibers from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"xcoord_integral_points":[]}"#
example : EmptyFibers.witness.integralFiberRoots = some [] := rfl
example : EmptyData.witness.integralFiberRoots = none := rfl

certify_ec DirectDoubleRoot from
  { equation := ⟨0, 0, 0, -1, 0⟩, integralFiberRoots := some [(0, 0)] }
example : DirectDoubleRoot.integral_y_fiber ⟨0, by decide⟩ = ({0} : Finset ℤ) := by
  decide +kernel

-- Match the LMFDB exponent convention even when the third coordinate is negative.
certify_ec RationalGenerators from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"gens":[[1,5,-2]],"ngens":1,"torsion_generators":[]}"#
example : RationalGenerators.generators.coordinates.length = 1 :=
  RationalGenerators.generators.count_valid

certify_ec EmptyGeneratorCount from
  { equation := ⟨0, 0, 1, -1, 0⟩, generatorCoordinates := some [], generatorCount := some 0 }
example : EmptyGeneratorCount.generators.coordinates.length = 0 :=
  EmptyGeneratorCount.generators.count_valid

example : EmptyGeneratorCount.certificate.algebraic.generatorCount = some 0 := rfl

certify_ec UnwitnessedGeneratorCount from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"ngens":1}"#
example : UnwitnessedGeneratorCount.certificate.algebraic.generatorCount = none := rfl

run_cmd do
  if (← getEnv).contains `UnwitnessedGeneratorCount.generators.count_valid then
    throwError "An unsupported generator count became a theorem"

example : RationalGenerators.generators.coordinates = [(1 / 4, -5 / 8)] := by decide +kernel
example : (RationalGenerators.curve.baseChange ℚ).toAffine.Equation (1 / 4) (-5 / 8) :=
  RationalGenerators.generators.points_on_curve _ _ (by decide +kernel)
example : RationalGenerators.torsion_generators.coordinates = [] := rfl
example : (RationalGenerators.curve.baseChange ℚ).toAffine.Point :=
  RationalGenerators.generators.point ⟨0, by decide⟩

certify_ec TorsionGeneratorCoordinates from
  { equation := ⟨0, -1, 1, -10, -20⟩, torsionGeneratorCoordinates := some [(5, 5)] }
example : (TorsionGeneratorCoordinates.curve.baseChange ℚ).toAffine.Equation 5 5 :=
  TorsionGeneratorCoordinates.torsion_generators.points_on_curve _ _ (by decide +kernel)

certify_ec TorsionOrderThree from_json_string
  r#"{"ainvs":[0,0,1,0,0],"torsion_generators":[[0,0,1]],"torsion_generator_orders":[3]}"#
example : addOrderOf (TorsionOrderThree.torsion_generators.point ⟨0, by decide⟩) = 3 :=
  TorsionOrderThree.torsion_generators.exact_order _

certify_ec TorsionOrderFour from
  { equation := ⟨1, -1, -1, 0, 0⟩, torsionGeneratorCoordinates := some [(0, 0)],
    torsionGeneratorOrders := some [4] }
example : addOrderOf (TorsionOrderFour.torsion_generators.point ⟨0, by decide⟩) = 4 :=
  TorsionOrderFour.torsion_generators.exact_order _

private def membershipOnly := TorsionGeneratorCoordinates.certificate.torsion
private def submittedPoints := membershipOnly.generators.get (by decide +kernel)

example : submittedPoints.1 = 1 := rfl
example : submittedPoints.2 ⟨0, by decide +kernel⟩ =
    TorsionGeneratorCoordinates.torsion_generators.point ⟨0, by decide +kernel⟩ := rfl
example : membershipOnly.orders.isNone := by decide +kernel
example : membershipOnly.generation.isNone := by decide +kernel
example : membershipOnly.presentation.isNone := by decide +kernel

private def ordersOnly := TorsionOrderThree.certificate.torsion

example : ((ordersOnly.orders.get (by decide +kernel) ⟨0, by decide +kernel⟩).val : ℕ) = 3 :=
  rfl
example : ordersOnly.generation.isNone := by decide +kernel
example : ordersOnly.presentation.isNone := by decide +kernel

certify_ec OnlyAP from
  { equation := ⟨0, 0, 1, -1, 0⟩, primeCoefficients := some [(2, -2)] }
certify_ec OnlyPoints from
  { equation := ⟨0, 0, 1, -1, 0⟩, integralCoordinates := some [(0, 0)] }
example : OnlyAP.witness.integralCoordinates = none := rfl
example : EmptyData.witness.integralCoordinates = some [] := rfl
example : OnlyPoints.witness.primeCoefficients = none := rfl
certify_ec Mixed from
  { Curve37.witness with
    primeCoefficients := some [(37, -1)]
    integralCoordinates := some [(0, 0)] }
example : (Mixed.curve.baseChange ℚ).LFunction 37 = -1 :=
  Mixed.ap_correct 37 (-1) (by decide +kernel)
example : Mixed.certifiedRank.val = 1 := rfl
example : Mixed.point ⟨0, by decide⟩ ∈ Mixed.curve.integralPoints := Mixed.point_integral _

-- Optional components are checked independently, without manufacturing missing data.
certify_ec ArithmeticOnly from
  { equation := Curve37.curve, minimality := some Curve37.minimality,
    localData := some Curve37.localData }
certify_ec NumericOnly from
  { equation := Curve37.curve, derivativeResult := some Curve37.result }
example : NumericOnly.result.equation = NumericOnly.curve := NumericOnly.result_curve_eq

-- A complete rank JSON can carry arithmetic claims and metadata in the same object.
run_cmd do
  let text ← IO.FS.readFile "data/witnesses/37a1.json"
  let .ok j := Json.parse text | throwError "Could not parse fixture"
  let .ok object := j.getObj? | throwError "Expected fixture object"
  let combined := Json.mkObj (object.toList ++ [
    ("ap", toJson ([[37, -1]] : List (List Int))),
    ("integral_points", toJson ([[0, 0]] : List (List Int))),
    ("lmfdb_label", .str "37.a1")])
  let literal := Syntax.mkStrLit combined.compress
  elabCommand (← `(certify_ec MixedJSON from_json_string $literal:str))
example : MixedJSON.certifiedRank.val = 1 := rfl
example : (MixedJSON.curve.baseChange ℚ).LFunction 37 = -1 :=
  MixedJSON.ap_correct 37 (-1) (by decide +kernel)

/-- Assert that failed arithmetic verification leaves no generated declarations. -/
meta def expectDataRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let savedMessages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages := savedMessages }
  unless failed do throwError "Invalid curve data accepted: {name}"
  for suffix in [`supplied, `witness, `curve, `nonsingular, `prime_coefficients_valid,
      `ap_correct, `integral_coordinates_valid, `points_on_curve, `curve_isElliptic,
      `point, `point_integral, `integral_fiber_roots, `integral_fiber_roots_eq,
      `integral_fiber_roots_valid, `integral_y_fiber, `integral_y_fiber_complete,
      `generators.point, `torsion_generators.point, `generators.count,
      `generators.count_eq_input, `generators.count_valid,
      `torsion_generators.orders, `torsion_generators.orders_eq, `torsion_generators.orders_length,
      `torsion_generators.orders_in_range, `torsion_generators.orders_valid,
      `torsion_generators.exact_order] do
    if env.contains (name ++ suffix) then
      throwError "Failed curve-data certification leaked {name ++ suffix}"
    if env.contains (name ++ `data ++ suffix) then
      throwError "Failed combined certification leaked arithmetic declarations"

run_cmd do
  expectDataRejected `WrongAP (← `(certify_ec WrongAP from
    { Data37.witness with primeCoefficients := some [(2, 999)] }))
  expectDataRejected `CompositeIndex (← `(certify_ec CompositeIndex from
    { Data37.witness with primeCoefficients := some [(4, 0)] }))
  expectDataRejected `Nonminimal (← `(certify_ec Nonminimal from
    { equation := ⟨0, 0, 8, -16, 0⟩, primeCoefficients := some [(2, 0)],
      integralCoordinates := some [] }))
  expectDataRejected `OffCurve (← `(certify_ec OffCurve from
    { Data37.witness with integralCoordinates := some [(0, 1)] }))
  expectDataRejected `InvalidWeightedPoint (← `(certify_ec InvalidWeightedPoint from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],"torsion_generators":[[1,1,1]]}"#))
  expectDataRejected `WrongGeneratorCount (← `(certify_ec WrongGeneratorCount from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],"ngens":2}"#))
  expectDataRejected `WrongOrder (← `(certify_ec WrongOrder from
    { TorsionOrderFour.witness with torsionGeneratorOrders := some [8] }))
  expectDataRejected `MissingOrder (← `(certify_ec MissingOrder from
    { TorsionOrderFour.witness with torsionGeneratorOrders := some [] }))
  expectDataRejected `MissingTorsionPoint (← `(certify_ec MissingTorsionPoint from_json_string
    r#"{"ainvs":[0,0,1,0,0],"torsion_generator_orders":[3]}"#))
  expectDataRejected `ZeroOrder (← `(certify_ec ZeroOrder from
    { TorsionOrderFour.witness with torsionGeneratorOrders := some [0] }))
  expectDataRejected `OversizedOrder (← `(certify_ec OversizedOrder from
    { TorsionOrderFour.witness with torsionGeneratorOrders := some [257] }))
  expectDataRejected `MalformedOrder (← `(certify_ec MalformedOrder from_json_string
    r#"{"ainvs":[0,0,1,0,0],"torsion_generators":[[0,0,1]],"torsion_generator_orders":[-3]}"#))
  expectDataRejected `ZeroWeight (← `(certify_ec ZeroWeight from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"gens":[[1,5,0]]}"#))
  expectDataRejected `ShortWeightedPoint (← `(certify_ec ShortWeightedPoint from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0]]}"#))
  expectDataRejected `Singular (← `(certify_ec Singular from
    { equation := ⟨0, 0, 0, 0, 0⟩, primeCoefficients := some [], integralCoordinates := some [] }))
  expectDataRejected `Malformed (← `(certify_ec Malformed from_json_string "{}"))
  expectDataRejected `BadX (← `(certify_ec BadX from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"xcoord_integral_points":[3]}"#))
  expectDataRejected `NegativeDiscriminantX (← `(certify_ec NegativeDiscriminantX from_json_string
    r#"{"ainvs":[0,0,0,-1,0],"xcoord_integral_points":[-2]}"#))
  expectDataRejected `NonintegralX (← `(certify_ec NonintegralX from_json_string
    r#"{"ainvs":[0,0,0,-1,0],"xcoord_integral_points":[0.5]}"#))
  expectDataRejected `WrongFiberRoot (← `(certify_ec WrongFiberRoot from
    { equation := ⟨0, 0, 0, -1, 0⟩, integralFiberRoots := some [(0, 1)] }))
  expectDataRejected `ConflictingCurve (← `(certify_ec ConflictingCurve from
    { equation := Data11.curve, derivativeResult := some Curve37.result }))
  expectDataRejected `MixedBadAP (← `(certify_ec MixedBadAP from
    { Mixed.supplied with primeCoefficients := some [(37, 999)] }))
  expectDataRejected `ConflictingRanks (← `(certify_ec ConflictingRanks from
    { Curve37.witness with centralResult := some Curve11.result }))


certify_ec DataAfterFailure from
  { equation := ⟨0, 0, 1, -1, 0⟩, primeCoefficients := some [(2, -2)],
    integralCoordinates := some [(0, 0)] }

run_cmd do
  elabCommand (← `(certify_ec QuotedDirect from
    { equation := ⟨0, 0, 1, -1, 0⟩, primeCoefficients := some [(2, -2)] }))
example : (QuotedDirect.curve.baseChange ℚ).LFunction 2 = -2 :=
  QuotedDirect.ap_correct 2 (-2) (by decide +kernel)

run_cmd do
  CertifyEC.certify `DirectAPI (← `(
    { equation := ⟨0, 0, 1, -1, 0⟩, integralCoordinates := some [(0, 0)] }))
  let input ← CertifyEC.jsonInput
    r#"{"ainvs":[0,0,1,-1,0],"ap":[[2,-2]]}"#
  CertifyEC.certifyAtomic `DecodedAPI input
example : DirectAPI.curve.toAffine.Equation 0 0 :=
  DirectAPI.points_on_curve 0 0 (by decide +kernel)
example : (DecodedAPI.curve.baseChange ℚ).LFunction 2 = -2 :=
  DecodedAPI.ap_correct 2 (-2) (by decide +kernel)

run_cmd do
  for name in [`RawData, `OnlyAP, `OnlyPoints, `ArithmeticOnly, `NumericOnly] do
    if (← getEnv).contains (name ++ `analytic_rank) then
      throwError "A stored rank without a proof witness became a theorem"
  for suffix in [`generators.points_on_curve, `torsion_generators.points_on_curve] do
    if (← getEnv).contains (`OnlyAP ++ suffix) then
      throwError "Missing generator data became a theorem"
  if (← getEnv).contains `TorsionGeneratorCoordinates.torsion_generators.exact_order then
    throwError "Missing torsion orders became a theorem"
  if (← getEnv).contains `VerifiedLcalc.CurveDataWitness then
    throwError "The retired aggregate witness type is still present"

namespace Scoped
certify_ec Data from
  { equation := ⟨0, 0, 1, -1, 0⟩, primeCoefficients := some [(2, -2)],
    integralCoordinates := some [(0, 0)] }
end Scoped

example : (Scoped.Data.curve.baseChange ℚ).LFunction 2 = -2 :=
  Scoped.Data.ap_correct 2 (-2) (by decide +kernel)

-- Every accepted theorem remains independent of the modularity axiom.
run_cmd do
  for name in [`Data11, `Data37, `AdditiveData, `EmptyData, `DataAfterFailure,
      `Scoped.Data, `RawData, `OnlyAP, `OnlyPoints, `Mixed, `MixedJSON,
      `DirectAPI, `DecodedAPI] do
    for suffix in [`nonsingular, `prime_coefficients_valid, `ap_correct,
        `integral_coordinates_valid, `points_on_curve, `curve_isElliptic,
        `point, `point_integral] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      for axiomName in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected arithmetic-certificate axiom: {axiomName}"

run_cmd do
  for name in [`RationalGenerators.generators, `RationalGenerators.torsion_generators,
      `TorsionGeneratorCoordinates.torsion_generators] do
    for suffix in [`points_on_curve, `point] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      for axiomName in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected rational-point certificate axiom: {axiomName}"

run_cmd do
  for name in [`TorsionOrderThree.torsion_generators, `TorsionOrderFour.torsion_generators] do
    for suffix in [`orders_valid, `exact_order] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      for axiomName in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected exact-order certificate axiom: {axiomName}"

run_cmd do
  for text in [r#"{"ainvs":[0,0,1,-1,0]}"#,
      r#"{"ainvs":[0,0,1,-1,0],"ap":null,"integral_points":null,
          "gens":null,"torsion_generators":null,"xcoord_integral_points":null}"#] do
    match CurveDataJson.parse text with
    | .ok w =>
      unless w.primeCoefficients.isNone && w.integralCoordinates.isNone &&
          w.integralFiberRoots.isNone && w.generatorCoordinates.isNone &&
          w.torsionGeneratorCoordinates.isNone &&
          w.centralResult.isNone && w.derivativeResult.isNone &&
          w.minimality.isNone && w.localData.isNone &&
          w.infiniteOrderPoints.isNone && w.independentPoints.isNone do
        throwError "Missing optional data was manufactured"
    | .error reason => throwError reason
  let good ← IO.FS.readFile "data/curve-data/37a1.json"
  let malformed := [
    good.replace "\"97\"" "\"10001\"",
    good.replace "\"97\"" "\"097\"",
    good.replace "\"97\"" "\"97/1\"",
    good.replace "\"97\"" "97.5"
  ]
  for text in malformed do
    match CurveDataJson.parse text with
    | .error _ => pure ()
    | .ok _ => throwError "Malformed curve-data JSON accepted"
  for text in [good.replace "\"97\"" "97",
      good.replace "\"schema\":" "\"unknown\":true,\"schema\":"] do
    match CurveDataJson.parse text with
    | .ok _ => pure ()
    | .error reason => throwError s!"Supported partial data rejected: {reason}"
  let rankText ← IO.FS.readFile "data/witnesses/37a1.json"
  let .ok rankJson := Json.parse rankText | throwError "Invalid rank fixture"
  let nested := Json.mkObj [
    ("analytic_witness", rankJson),
    ("subject", Json.mkObj [("label", .str "unverified metadata")]),
    ("aplist", toJson ([-2, -3] : List Int))]
  match CurveDataJson.parse nested.compress with
  | .ok w =>
    unless w.derivativeResult.isSome && w.primeCoefficients == some [(2, -2), (3, -3)] do
      throwError "Nested supported facts were dropped"
  | .error reason => throwError reason
