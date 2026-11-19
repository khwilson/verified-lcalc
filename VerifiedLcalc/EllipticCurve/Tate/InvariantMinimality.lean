module

public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic

@[expose] public section
open WeierstrassCurve
namespace VerifiedLcalc.EllipticCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open NumberField IsDedekindDomain

/-- Integer divisibility checks discharge the two invariant criteria at p. -/
theorem invariantMinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (h : invariantMinimalAt e p = true) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (WeierstrassCurve.baseChange e R).baseChange K
  let : WeierstrassCurve.IsIntegral R W := ⟨⟨WeierstrassCurve.baseChange e R, rfl⟩⟩
  have h' : ¬ (p : Int)^4 ∣ e.c₄ ∨ ¬ (p : Int)^6 ∣ e.c₆ := by
    simpa only [invariantMinimalAt, decide_eq_true_eq, ne_eq, Int.dvd_iff_emod_eq_zero] using h
  rcases h' with h | h
  · apply isMinimal_of_small_c4 W Valued.v (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
    have he : W.c₄ = (e.c₄ : K) := by
      simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, eq_intCast, map_intCast]
    rw [he, completion_intCast_valuation]
    exact rationalPlace_intValuation_gt p 4 (e.c₄) h
  · apply isMinimal_of_small_c6 W Valued.v (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
    have he : W.c₆ = (e.c₆ : K) := by
      simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆, eq_intCast, map_intCast]
    rw [he, completion_intCast_valuation]
    exact rationalPlace_intValuation_gt p 6 (e.c₆) h

end VerifiedLcalc.EllipticCurve
