/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.Reduced

/-! # Conditional modular parametrization checks for the Cremona 11a1 (LMFDB 11.a2) row

The geometric hypotheses express the pointed genus-one isomorphism, its normalized
differential identity, and surjectivity on integral periods. The degree and its
minimality follow from surjectivity of the actual function-field map.
-/

@[expose] public noncomputable section

namespace VerifiedLcalcTests.ModularParametrization11

open VerifiedLcalc VerifiedLcalc.Modularity WeierstrassCurve TauCeti.WorkedExamples

/-- The algorithmic conductor of the semistable minimal equation has norm eleven. -/
theorem conductor11 : Ideal.absNorm ((curve11a2.baseChange ℚ).algorithmicConductor ℤ) = 11 := by
  have hs : IsSemistable ℤ (curve11a2.baseChange ℚ) :=
    isSemistable_baseChange_of_isCoprime curve11a2 (by
      rw [Δ_curve11a2, c₄_curve11a2, Int.isCoprime_iff_gcd_eq_one]
      norm_num)
  have hp : Prime (Ideal.span {(11 : ℤ)}) :=
    Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 11))
  rw [(isSemistable_iff_algorithmicConductor_eq_radical _).mp hs,
    minimalDiscriminantIdeal_curve11a2, ← Ideal.span_singleton_pow,
    UniqueFactorizationMonoid.radical_pow_of_prime hp (by decide : (5 : ℕ) ≠ 0)]
  simp

/-- Mathematical inputs for the pointed genus-one description of the conductor-eleven curve. -/
class GeometricModel11 (level : ℕ) where
  /-- The cusp form matches all actual Fourier coefficients of the elliptic curve. -/
  realization : ModularRealization curve11a2
  /-- The degree-one realization is at the indicated level. -/
  realization_level : realization.level = level
  /-- The indicated level is eleven. -/
  atEleven : level = 11
  /-- The field map on the actual modular curve. -/
  pullback : letI : NeZero realization.level := ⟨Nat.ne_of_gt realization.positiveLevel⟩
    ModularPullback realization.level curve11a2
  /-- The map is a genus-one isomorphism. -/
  onto : letI : NeZero realization.level := ⟨Nat.ne_of_gt realization.positiveLevel⟩
    Function.Surjective pullback
  /-- The cusp at infinity is the elliptic point at infinity. -/
  pointed : letI : NeZero realization.level := ⟨Nat.ne_of_gt realization.positiveLevel⟩
    pullback.IsPointed
  /-- The map pulls back the Néron differential to the normalized differential. -/
  differential : letI : NeZero realization.level := ⟨Nat.ne_of_gt realization.positiveLevel⟩
    pullback.PullsBackDifferential realization.form 1
  /-- All periods on the target are attained by loops in the modular curve. -/
  periods :
    gammaZeroDifferentialPeriods realization.form 1 =
      ((curve11a2.baseChange ℚ).map (Rat.castHom ℂ)).periodLattice.toAddSubgroup

/-- Turn the geometric inputs into a minimum-degree modular parametrization. -/
def facts {level : ℕ} (h : GeometricModel11 level) : ModularParametrizationFacts curve11a2 where
  realization := h.realization
  minimal := isReducedMinimal_curve11a2.isGlobalMinimal
  level_eq := h.realization_level.trans (h.atEleven.trans conductor11.symm)
  pullback := h.pullback
  pointed := h.pointed
  degree := 1
  degree_eq := by
    let : NeZero h.realization.level := ⟨Nat.ne_of_gt h.realization.positiveLevel⟩
    exact h.pullback.degree_eq_one_of_surjective h.onto
  minimum _ hpos := hpos
  maninConstant := 1
  differential := h.differential
  periodImage_le := h.periods.le
  optimal := some ⟨true, iff_of_true h.periods rfl⟩

/-- Proof attachment used for the producer row and rollback tests. -/
def proofs {level : ℕ} (h : GeometricModel11 level) : IntegralCurveProofs curve11a2 where
  modularParametrization := some (facts h)

section

variable {level : ℕ} [h : GeometricModel11 level]

certify_ec Modular11 from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"degree":1,"manin_constant":1,"optimality":1}"#
  with_proofs (proofs h)

end

end VerifiedLcalcTests.ModularParametrization11
