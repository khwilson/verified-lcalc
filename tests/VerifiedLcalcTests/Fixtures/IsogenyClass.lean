/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.Reduced

/-! # Conditional isogeny-class certificates for 37.a1

The fixture assumes exhaustivity as an explicit argument. The identity map supplies the
minimum degree and the reduced minimal model is checked independently.
-/

@[expose] public section

namespace VerifiedLcalcTests.IsogenyClass37

open VerifiedLcalc TauCeti

/-- The integral equation of 37.a1. -/
abbrev source : WeierstrassCurve ℤ := WorkedExamples.curve37a1

instance : (source.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Every rational curve isogenous to this representative is isomorphic to it. -/
def ExhaustiveAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
    Nonempty (Isogeny E.toAffine W.toAffine) →
      ∃ C : WeierstrassCurve.VariableChange ℚ, C • W = E

/-- The completeness hypothesis for the single proposed representative of 37.a1. -/
abbrev Exhaustive : Prop := ExhaustiveAt (source.baseChange ℚ)

/-- The class model supplied to the tests, conditional on exhaustivity. -/
def model (h : Exhaustive) : IsogenyClassModel source where
  classSize := 1
  representatives := fun _ => source.baseChange ℚ
  elliptic := fun _ => inferInstance
  curveIndex := 0
  curveChange := 1
  curveChange_eq := by simp
  distinct := fun _ _ _ _ => Subsingleton.elim _ _
  exhaustive W hW hIso := by
    obtain ⟨C, hC⟩ := h W hW hIso
    exact ⟨0, C, hC⟩
  isogenyMatrix := fun _ _ => 1
  attained := fun _ _ => ⟨Isogeny.id _, Isogeny.degree_id _⟩
  degree_min := fun _ _ φ => φ.degree_pos

/-- The canonical order of the singleton candidate. -/
def ordering : IsogenyClassOrdering (fun _ : Fin 1 => source.baseChange ℚ) where
  elliptic := fun _ => inferInstance
  reducedMinimal _ := WorkedExamples.isReducedMinimal_curve37a1
  ordered i j h := (lt_irrefl _ ((Subsingleton.elim j i) ▸ h)).elim

/-- Supply model evidence in a computable record without computing an isogeny. -/
def proofAttachment (h : Exhaustive) : IntegralCurveProofs source :=
  { isogenyClass := some ⟨model h, some ordering⟩ }

/-- The representative in a complete singleton presentation of 37.a1. -/
class SingletonModel (E : outParam (WeierstrassCurve ℚ)) : Prop where
  /-- The representative is the equation supplied to this fixture. -/
  equation_eq : E = source.baseChange ℚ
  /-- Every rational isogeny from this representative stays in its isomorphism class. -/
  exhaustive : ExhaustiveAt E

/-- Transport the fixture's completeness hypothesis to its integral input. -/
theorem SingletonModel.complete {E : WeierstrassCurve ℚ} (h : SingletonModel E) : Exhaustive :=
  (congrArg ExhaustiveAt h.equation_eq).mp h.exhaustive

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

certify_ec Class37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"discriminant":37,"class_size":1,"class_deg":1,
     "isogeny_matrix":[[1]],"isogeny_degrees":[1]}"#
  with_proofs (proofAttachment h.complete)

certify_ec Size37 from ({ equation := source, classSize := some 1 } : EllipticWitness)
  with_proofs ({ isogenyClass := some ⟨model h.complete, none⟩ } : IntegralCurveProofs source)

end

end VerifiedLcalcTests.IsogenyClass37
