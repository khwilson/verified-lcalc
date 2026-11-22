module

public import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-! # Local Euler factors of supplied minimal equations -/

@[expose] public section
namespace WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

section Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A smooth integral equation is minimal: its discriminant already has the
largest valuation possible for an integral equation. -/
theorem isMinimal_of_unit_discriminant (W : WeierstrassCurve R) (h : IsUnit W.Δ) :
    WeierstrassCurve.IsMinimal R (W.baseChange K) :=
  isMinimal_baseChange_of_isUnit_Δ_or_isUnit_c₄ R W (.inl h)

/-- Either unit discriminant or unit c4 is enough for local minimality. -/
theorem isMinimal_of_unit_invariants (W : WeierstrassCurve R)
    (h : IsUnit W.Δ ∨ IsUnit W.c₄) : WeierstrassCurve.IsMinimal R (W.baseChange K) :=
  isMinimal_baseChange_of_isUnit_Δ_or_isUnit_c₄ R W h

/-- Two minimal equations reduce to models related by an actual invertible
residue-field variable change. This includes singular reductions. -/
theorem reduction_eq_variableChange (W : WeierstrassCurve R)
    [WeierstrassCurve.IsMinimal R (W.baseChange K)] [(W.baseChange K).IsElliptic] :
    ∃ C : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R),
      ((W.baseChange K).minimal R).reduction R = C • W.map (IsLocalRing.residue R) := by
  obtain ⟨D, hD⟩ := WeierstrassCurve.exists_smul_eq_minimal R (W.baseChange K)
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_smul_reduction_eq_of_isMinimal_smul R D hD
  have hred : (W.baseChange K).reduction R = W.map (IsLocalRing.residue R) := by
    rw [WeierstrassCurve.reduction, WeierstrassCurve.integralModel_baseChange_self]
  exact ⟨C, by simpa only [hred] using hC.symm⟩

open scoped Classical in
/-- The local polynomial can be read from any supplied integral minimal
elliptic equation, rather than only mathlib's chosen representative. -/
theorem localPolynomial_of_minimal_input (W : WeierstrassCurve R)
    [WeierstrassCurve.IsMinimal R (W.baseChange K)] [(W.baseChange K).IsElliptic]
    [Finite (IsLocalRing.ResidueField R)] :
    (W.baseChange K).localPolynomial R =
      1 - Polynomial.C (W.map (IsLocalRing.residue R)).frobeniusTrace * Polynomial.X +
        Polynomial.C (if (W.map (IsLocalRing.residue R)).Δ ≠ 0 then
          (Nat.card (IsLocalRing.ResidueField R) : ℤ) else 0) * Polynomial.X ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := reduction_eq_variableChange (K := K) W
  have ht : (((W.baseChange K).minimal R).reduction R).frobeniusTrace =
      (W.map (IsLocalRing.residue R)).frobeniusTrace := by
    rw [hC, WeierstrassCurve.variableChange_frobeniusTrace]
  have hg : ((W.baseChange K).minimal R).HasGoodReduction R ↔
      (W.map (IsLocalRing.residue R)).Δ ≠ 0 := by
    rw [WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction,
      WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, hC,
      WeierstrassCurve.variableChange_Δ]
    simp
  by_cases hd : (W.map (IsLocalRing.residue R)).Δ ≠ 0
  · rw [(W.baseChange K).localPolynomial_eq_of_hasGoodReduction R (hg.mpr hd), ht,
      ite_eq_left hd]
  · rw [(W.baseChange K).localPolynomial_eq_of_not_hasGoodReduction R (mt hg.mp hd), ht,
      ite_eq_right hd]
    simp

end Local
end WeierstrassCurve
