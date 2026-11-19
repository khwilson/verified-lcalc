module

public import VerifiedLcalc.EllipticCurve.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.BadPrimeCore

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- The integer tangent polynomial is the actual reduced node polynomial. -/
theorem nodeValue_correct (e : Artifacts.CurveEquation) (p n : ℕ) :
    (weierstrass e (ZMod p)).nodePolynomial.eval (n : ZMod p) =
      (nodeValue e n : ZMod p) := by
  simp [WeierstrassCurve.nodePolynomial_def, nodeValue, modelC4, b2, b4, b6,
    weierstrass, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]

/-- The root-search Boolean is equivalent to existence of a field root. -/
theorem hasNodeRoot_correct (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime] :
    hasNodeRoot e p = true ↔
      ∃ x : ZMod p, (weierstrass e (ZMod p)).nodePolynomial.eval x = 0 := by
  simp only [hasNodeRoot, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨(n : ZMod p), ?_⟩
    rw [nodeValue_correct]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_iff_emod_eq_zero.mpr h)
  · rintro ⟨x, hx⟩
    refine ⟨x.val, ZMod.val_lt x, ?_⟩
    have hz : (nodeValue e x.val : ZMod p) = 0 := by
      rw [← nodeValue_correct, ZMod.natCast_zmod_val]
      exact hx
    exact Int.dvd_iff_emod_eq_zero.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

/-- A quadratic node polynomial splits exactly when the search finds a root. -/
theorem hasNodeRoot_iff_splits (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime]
    (hc : (weierstrass e (ZMod p)).c₄ ≠ 0) :
    hasNodeRoot e p = true ↔ (weierstrass e (ZMod p)).nodePolynomial.Splits := by
  have hd : (weierstrass e (ZMod p)).nodePolynomial.natDegree = 2 := by
    rw [WeierstrassCurve.nodePolynomial_def, sub_eq_add_neg, ← Polynomial.C_neg]
    exact Polynomial.natDegree_quadratic hc
  rw [hasNodeRoot_correct]
  constructor
  · rintro ⟨x, hx⟩
    exact Polynomial.Splits.of_natDegree_eq_two hd hx
  · intro hs
    have hn : (weierstrass e (ZMod p)).nodePolynomial.natDegree ≠ 0 := by rw [hd]; decide
    exact hs.exists_eval_eq_zero (Polynomial.degree_ne_of_natDegree_ne hn)

/-- Exact singular-model trace, including p=2 and p=3. The executable search
uses p tangent evaluations instead of p^2 equation evaluations. -/
theorem singularTrace_correct (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime]
    (hd : goodReduction e p = false) : singularTrace e p = frobeniusTrace e p := by
  have hΔ : (weierstrass e (ZMod p)).Δ = 0 := by
    by_contra h
    have := (goodReduction_correct e p).mpr h
    simp only [hd, Bool.false_eq_true] at this
  rw [frobeniusTrace_eq_tauceti]
  unfold singularTrace
  by_cases hc : modelC4 e % (p : Int) = 0
  · rw [ite_eq_left hc]
    symm
    apply WeierstrassCurve.frobeniusTrace_eq_zero_of_c₄_eq_zero _ hΔ
    rw [weierstrass_c4, ← modelC4_correct]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_iff_emod_eq_zero.mpr hc)
  · rw [ite_eq_right hc]
    have hc' : (weierstrass e (ZMod p)).c₄ ≠ 0 := by
      rw [weierstrass_c4, ← modelC4_correct]
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero] using hc
    by_cases hs : hasNodeRoot e p = true
    · rw [ite_eq_left hs]
      exact (WeierstrassCurve.frobeniusTrace_eq_one_of_splits _ hΔ hc'
        ((hasNodeRoot_iff_splits e p hc').mp hs)).symm
    · rw [ite_eq_right hs]
      exact (WeierstrassCurve.frobeniusTrace_eq_neg_one_of_not_splits _ hΔ hc'
        (mt (hasNodeRoot_iff_splits e p hc').mpr hs)).symm

end VerifiedLcalc.EllipticCurve
