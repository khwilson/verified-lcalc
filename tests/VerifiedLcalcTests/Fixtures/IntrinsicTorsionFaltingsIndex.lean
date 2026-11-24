/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Fixtures.IsogenyClass

/-! # The intrinsic order and Faltings index of 37.a1

Two finite point counts prove trivial rational torsion. The index uses
the explicit singleton-class completeness hypothesis of the class fixture.
The reported values are from the [LMFDB row](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1).
-/

@[expose] public section

namespace VerifiedLcalcTests.IntrinsicTorsionFaltingsIndex37

open VerifiedLcalc IsogenyClass37

/-- An exhaustive singleton class has no representatives preceding its input. -/
def indexFact (h : Exhaustive) : FaltingsIndexFact source where
  model := model h
  ordering := ordering
  predecessors := ∅
  mem_predecessors i := by
    have hsub : Subsingleton (Fin (model h).classSize) := by
      change Subsingleton (Fin 1)
      infer_instance
    have hi : i = (model h).curveIndex := hsub.elim _ _
    subst i
    simp [faltingsPrecedes]

/-- Supply the complete class and its Faltings index in the shared Lean attachment. -/
def withIndex (h : Exhaustive) : IntegralCurveProofs source :=
  { proofAttachment h with faltingsIndex := some (indexFact h) }

certify_ec Intrinsic37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"intrinsic_torsion":1,
      "torsion_bound":{"first_prime":3,"second_prime":5,"bound":1}}"#

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

certify_ec Index37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"faltings_index":0,"class_size":1}"#
  with_proofs (withIndex h.complete)

end

end VerifiedLcalcTests.IntrinsicTorsionFaltingsIndex37
