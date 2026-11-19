module

public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

@[expose] public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An executable projective-model point count over an explicitly enumerated
finite field. Singular affine solutions and the point at infinity are included.
Unlike `pointCount`, this definition needs no classical choice. -/
def pointCountFinite (W : WeierstrassCurve F) : ℕ :=
  letI : DecidablePred (fun p : F × F => W.toAffine.Equation p.1 p.2) :=
    fun p => decidable_of_iff
      (p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
        p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)
      (W.toAffine.equation_iff p.1 p.2).symm
  Fintype.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1

/-- Executable enumeration computes exactly TauCeti's existing count. -/
theorem pointCountFinite_eq_pointCount (W : WeierstrassCurve F) :
    W.pointCountFinite = W.pointCount := by
  unfold pointCountFinite
  rw [pointCount_def]
  exact congrArg (fun n : ℕ => n + 1) (@Fintype.card_eq_nat_card _ _)

/-- Transport the projective equation count through an actual residue-field
isomorphism; singular points remain included. -/
theorem pointCount_map_equiv {F K : Type*} [Field F] [Field K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).pointCount = W.pointCount := by
  rw [WeierstrassCurve.pointCount_def, WeierstrassCurve.pointCount_def]
  congr 1
  apply Nat.card_congr
  exact ((k.toEquiv.prodCongr k.toEquiv).subtypeEquiv
    (fun xy => (W.toAffine.map_equation (f := k.toRingHom) k.injective xy.1 xy.2).symm)).symm

theorem frobeniusTrace_map_equiv {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).frobeniusTrace = W.frobeniusTrace := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.frobeniusTrace_def,
    pointCount_map_equiv, Nat.card_congr k.toEquiv]

end WeierstrassCurve
