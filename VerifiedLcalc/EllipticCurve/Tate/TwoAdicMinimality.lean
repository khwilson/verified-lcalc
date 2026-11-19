module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.TwoAdicMinimality
public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic

@[expose] public section
open WeierstrassCurve


namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The integer c4 criterion supplies a local minimality proof at two. -/
theorem minimal_at_two_of_c4 (e : (WeierstrassCurve ℤ))
    (h6 : (2 : ℤ) ^ 6 ∣ e.c₄) (h7 : ¬ (2 : ℤ) ^ 7 ∣ e.c₄) :
    WeierstrassCurve.IsMinimal ((rationalPlace 2).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace 2).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace 2).adicCompletion ℚ)) := by
  let v := rationalPlace 2
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (WeierstrassCurve.baseChange e R).baseChange K
  let : WeierstrassCurve.IsIntegral R W := ⟨⟨WeierstrassCurve.baseChange e R, rfl⟩⟩
  apply isMinimal_of_two_adic_c4_six W Valued.v
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  · exact completion_intCast_valuation_eq 2 1 2 (by decide) (by decide)
  · have heq : W.c₄ = (e.c₄ : K) := by
      simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, eq_intCast, map_intCast]
    rw [heq]
    exact completion_intCast_valuation_eq 2 6 (e.c₄) h6 h7

end VerifiedLcalc.EllipticCurve
