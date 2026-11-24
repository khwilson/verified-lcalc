/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Fixtures.IsogenyClass
public import VerifiedLcalc.Verification.PeriodGeometry

/-! # Singleton class ratio for 37.a1, conditional on class completeness -/

@[expose] public section

namespace VerifiedLcalcTests.PeriodGeometry37

open VerifiedLcalc TauCeti IsogenyClass37

/-- The global minimality evidence used for the period normalization. -/
theorem minimal : WeierstrassCurve.IsGlobalMinimal ℤ (source.baseChange ℚ) :=
  WorkedExamples.isReducedMinimal_curve37a1.isGlobalMinimal

/-- In a complete singleton class the maximum is the area of the input curve. -/
def ratio (h : Exhaustive) : FaltingsRatioFact source where
  inputMinimal := minimal
  model := model h
  minimal _ := minimal
  maximizingIndex := (model h).curveIndex
  isMaximum _ := le_rfl
  ratio := ⟨1, by decide⟩
  area_eq := by
    simp only [model, Nat.cast_one, one_mul]

/-- Proof attachment with no numerical enclosures, for the exact ratio path. -/
def attachment (h : Exhaustive) : IntegralCurveProofs source :=
  { periodGeometry := some { minimal, ratio := some (ratio h) } }

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

certify_ec Period37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"area":7.3381327407895767390707210033,
      "faltings_height":-0.99654220763736714794656344357,
      "stable_faltings_height":-0.99654220763736714794656344357,"faltings_ratio":1}"#
  with_proofs (attachment h.complete)

end

end VerifiedLcalcTests.PeriodGeometry37
