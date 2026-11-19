module

public import VerifiedLcalc.Assumptions.ModularityStatement
public import VerifiedLcalc.EllipticCurve.BadPrime

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

/-- Same mathematical sign formula, with the proved linear-time singular trace. -/
noncomputable def semistableSignFast (equation : Artifacts.CurveEquation) : Int :=
  -(∏ p ∈ (discriminant equation).natAbs.primeFactors, -(singularTrace equation p))

/-- The fast sign checker changes computation cost, not the assumed formula. -/
theorem semistableSign_eq_fast (e : Artifacts.CurveEquation) :
    semistableSign e = semistableSignFast e := by
  unfold semistableSign semistableSignFast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  let : Fact p.Prime := ⟨hprime⟩
  have hd : goodReduction e p = false := by
    have hi : (p : Int) ∣ discriminant e := Int.natCast_dvd.mpr hdiv
    simp only [goodReduction, Int.dvd_iff_emod_eq_zero.mp hi, ne_self_iff_false, decide_false]
  rw [singularTrace_correct e p hd]

end VerifiedLcalc.Assumptions
