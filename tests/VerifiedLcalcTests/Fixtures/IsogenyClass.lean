/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC

/-! # Conditional isogeny-class certificates for 37.a1

The fixture assumes exhaustivity as an explicit argument. The identity map supplies the
minimum degree and the reduced minimal model is checked independently.
-/

@[expose] public section

namespace VerifiedLcalcTests.IsogenyClass37

open VerifiedLcalc TauCeti

/-- The integral equation of 37.a1. -/
def source : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

instance : (source.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- The still-unproved exhaustivity premise for the single proposed representative. -/
def Exhaustive : Prop :=
  ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
    Nonempty (Isogeny (source.baseChange ℚ).toAffine W.toAffine) →
      ∃ C : WeierstrassCurve.VariableChange ℚ, C • W = source.baseChange ℚ

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
  reducedMinimal _ := by
    refine WeierstrassCurve.isReducedMinimal_iff.2
      ⟨WeierstrassCurve.isGlobalMinimal_baseChange_of_isCoprime (O := ℤ) source ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      decide +kernel
    · decide +kernel
  ordered i j h := (lt_irrefl _ ((Subsingleton.elim j i) ▸ h)).elim

/-- Supply model evidence in a computable record without computing an isogeny. -/
def proofAttachment (h : Exhaustive) : IntegralCurveProofs source :=
  { isogenyClass := some ⟨model h, some ordering⟩ }

section

set_option linter.concreteInstances false
set_option linter.unusedSectionVars false

variable [h : Fact Exhaustive]

certify_ec Class37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"discriminant":37,"class_size":1,"class_deg":1,
     "isogeny_matrix":[[1]],"isogeny_degrees":[1]}"#
  with_proofs (proofAttachment h.out)

certify_ec Size37 from ({ equation := source, classSize := some 1 } : EllipticWitness)
  with_proofs ({ isogenyClass := some ⟨model h.out, none⟩ } : IntegralCurveProofs source)

end

end VerifiedLcalcTests.IsogenyClass37
