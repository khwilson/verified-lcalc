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

end WeierstrassCurve
