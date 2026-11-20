module

public import VerifiedLcalc.EllipticCurve.Modularity.Realization
public import VerifiedLcalc.EllipticCurve.BadPrime

@[expose] public section
namespace VerifiedLcalc.Modularity
open EllipticCurve

/-- Same mathematical sign formula, with the proved linear-time singular trace. -/
noncomputable def semistableSignFast (equation : (WeierstrassCurve ℤ)) : Int :=
  -(∏ p ∈ (equation.Δ).natAbs.primeFactors, -(singularTrace equation p))

/-- The fast sign checker changes computation cost, not the assumed formula. -/
theorem semistableSign_eq_fast (e : (WeierstrassCurve ℤ)) :
    semistableSign e = semistableSignFast e := by
  unfold semistableSign semistableSignFast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  let : Fact p.Prime := ⟨hprime⟩
  have hd : goodReduction e p = false := by
    have hi : (p : Int) ∣ e.Δ := Int.natCast_dvd.mpr hdiv
    simp only [goodReduction, Int.dvd_iff_emod_eq_zero.mp hi, ne_self_iff_false, decide_false]
  rw [dif_pos hprime, singularTrace_correct e p hd, computeFrobeniusTrace_correct]

end VerifiedLcalc.Modularity
