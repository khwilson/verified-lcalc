/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Fixtures.IsogenyClass
public import VerifiedLcalc.Verification.LmfdbCatalogue
import Mathlib.Tactic

/-! # Conditional catalogue checks for the rational curve 43.a1

Exhaustivity at conductor 43 and exhaustivity of the subject's isogeny class are
independent test hypotheses. The conductor and reduced model are proved directly.
-/

@[expose] public section

namespace VerifiedLcalcTests.LmfdbCatalogue43

open VerifiedLcalc WeierstrassCurve TauCeti

/-- The reduced integral model in the 43.a1 data row. -/
abbrev source : WeierstrassCurve ℤ := ⟨0, 1, 1, 0, 0⟩

instance : (source.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- The given equation is already reduced and minimal. -/
theorem reduced : IsReducedMinimal (source.baseChange ℚ) := by
  refine isReducedMinimal_iff.mpr ⟨isGlobalMinimal_baseChange_of_isCoprime (O := ℤ) source ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  · simp [baseChange, source]

/-- The actual algorithmic conductor norm is 43. -/
theorem conductor : Ideal.absNorm ((source.baseChange ℚ).algorithmicConductor ℤ) = 43 := by
  have hsemi : IsSemistable ℤ (source.baseChange ℚ) :=
    isSemistable_baseChange_of_isCoprime source (by
      rw [Int.isCoprime_iff_gcd_eq_one]
      decide)
  have hprime : Prime (Ideal.span {(43 : ℤ)}) :=
    Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 43))
  have hdisc : minimalDiscriminantIdeal ℤ (source.baseChange ℚ) = Ideal.span {(43 : ℤ)} := by
    have hΔ : source.Δ = -(43 : ℤ) := by decide
    rw [minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal reduced.isGlobalMinimal
      (d := source.Δ) (by simp [baseChange]), hΔ, Ideal.span_singleton_neg]
  rw [(isSemistable_iff_algorithmicConductor_eq_radical _).mp hsemi, hdisc,
    UniqueFactorizationMonoid.radical_of_prime hprime]
  simp

/-- The singleton within-class presentation is exhaustive, as an explicit test hypothesis. -/
class CurveComplete (E : outParam (WeierstrassCurve ℚ)) : Prop where
  /-- The hypothesis concerns the equation in this fixture. -/
  equation_eq : E = source.baseChange ℚ
  /-- Any isogenous rational curve is rationally isomorphic to the subject. -/
  complete : VerifiedLcalcTests.IsogenyClass37.ExhaustiveAt E

/-- The singleton conductor roster is exhaustive, as an independent test hypothesis. -/
class RosterComplete (E : outParam (WeierstrassCurve ℚ)) : Prop where
  /-- The hypothesis concerns the equation in this fixture. -/
  equation_eq : E = source.baseChange ℚ
  /-- Any rational curve of actual conductor norm 43 is isogenous to the subject. -/
  complete (W : WeierstrassCurve ℚ) (h : W.IsElliptic) :
    letI := h
    Ideal.absNorm (W.algorithmicConductor ℤ) = 43 →
      Nonempty (Isogeny W.toAffine E.toAffine)

/-- An exhaustive singleton model with the minimum degree attained by the identity. -/
def model {E : WeierstrassCurve ℚ} (h : CurveComplete E) : IsogenyClassModel source where
  classSize := 1
  representatives := fun _ => source.baseChange ℚ
  elliptic _ := inferInstance
  curveIndex := 0
  curveChange := 1
  curveChange_eq := by simp
  distinct _ _ _ _ := Subsingleton.elim _ _
  exhaustive W hW hIso := by
    have complete := (congrArg VerifiedLcalcTests.IsogenyClass37.ExhaustiveAt
      h.equation_eq).mp h.complete
    obtain ⟨C, hC⟩ := complete W hW hIso
    exact ⟨0, C, hC⟩
  isogenyMatrix := fun _ _ => 1
  attained _ _ := ⟨Isogeny.id _, Isogeny.degree_id _⟩
  degree_min _ _ φ := φ.degree_pos

/-- The single representative is reduced minimal and its strict order is vacuous. -/
def ordering : IsogenyClassOrdering (fun _ : Fin 1 => source.baseChange ℚ) where
  elliptic _ := inferInstance
  reducedMinimal _ := reduced
  ordered i j h := (lt_irrefl _ ((Subsingleton.elim j i) ▸ h)).elim

/-- An exhaustive singleton roster, at the exact conductor. -/
def roster {E : WeierstrassCurve ℚ} (h : RosterComplete E) : ConductorClassRoster source where
  conductor := 43
  conductor_eq := conductor
  size := 1
  representatives := fun _ => source.baseChange ℚ
  elliptic _ := inferInstance
  sameConductor _ := conductor
  exhaustive W hW hN := ⟨0, h.equation_eq ▸ h.complete W hW hN⟩
  classIndex := 0
  ordered i j h := (lt_irrefl _ ((Subsingleton.elim j i) ▸ h)).elim
  subjectIsogenous := ⟨Isogeny.id _⟩

/-- Attach both kinds of order evidence to the same input equation. -/
def proofs {E R : WeierstrassCurve ℚ} (hE : CurveComplete E) (hR : RosterComplete R) :
    IntegralCurveProofs source :=
  { isogenyClass := some ⟨model hE, some ordering⟩
    conductorClassRoster := some (roster hR) }

section

variable {E R : WeierstrassCurve ℚ} [hE : CurveComplete E] [hR : RosterComplete R]

certify_ec Checked from_json_string
  r#"{"ainvs":[0,1,1,0,0],"lmfdb_number":1,"iso_nlabel":0,
      "lmfdb_iso":"43.a","lmfdb_label":"43.a1","conductor":43,
      "minimality":[43],"local_data":{"at_two":null,"at_three":null}}"#
  with_proofs (proofs hE hR)

end

end VerifiedLcalcTests.LmfdbCatalogue43
