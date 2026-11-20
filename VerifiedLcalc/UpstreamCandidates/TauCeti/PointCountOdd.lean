module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Euler's criterion counts square roots in an odd finite field using one power,
rather than an enumeration of every potential root. -/
def squareRootCountOdd (a : F) : Nat :=
  if a = 0 then 1 else if npowBinRec (Fintype.card F / 2) a = 1 then 2 else 0

private theorem binPow_eq_pow (n : Nat) (a : F) : npowBinRec n a = a ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

theorem squareRootCountOdd_correct (hF : ringChar F ≠ 2) (a : F) :
    squareRootCountOdd a = Fintype.card {y : F // y ^ 2 = a} := by
  classical
  have h := quadraticChar_card_sqrts hF a
  have hc : (Fintype.card {y : F // y ^ 2 = a} : Int) = quadraticChar F a + 1 := by
    simpa [Set.toFinset_ofPred, Fintype.card_subtype] using h
  suffices hs : (squareRootCountOdd a : Int) =
      (Fintype.card {y : F // y ^ 2 = a} : Int) by exact_mod_cast hs
  rw [hc]
  by_cases ha : a = 0
  · simp [squareRootCountOdd, ha]
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    simp only [squareRootCountOdd, binPow_eq_pow, ha, ↓reduceIte]
    split <;> simp_all

private theorem quadratic_fiber_card (h2 : (2 : F) ≠ 0) (b c : F) :
    Fintype.card {y : F // y ^ 2 + b*y = c} =
      Fintype.card {z : F // z ^ 2 = b ^ 2 + 4*c} := by
  classical
  apply Fintype.card_congr
  apply ((Equiv.mulLeft₀ (2 : F) h2).trans (Equiv.addRight b)).subtypeEquiv
  intro y
  change y ^ 2 + b*y = c ↔ (2*y+b)^2 = b^2+4*c
  constructor
  · intro h
    linear_combination 4*h
  · intro h
    have he : (2 : F)*2*(y^2+b*y-c) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero h2 h2))

/-- Count the fibers of a Weierstrass equation by completing the square.
Only the x coordinate is enumerated; characteristic two uses the general API. -/
def pointCountOddFinite (W : WeierstrassCurve F) : Nat :=
  (∑ x : F, squareRootCountOdd
    ((W.a₁*x+W.a₃)^2 + 4*(x^3+W.a₂*x^2+W.a₄*x+W.a₆))) + 1

theorem pointCountOddFinite_correct (W : WeierstrassCurve F) (hF : ringChar F ≠ 2) :
    W.pointCountOddFinite = W.pointCountFinite := by
  classical
  rw [pointCountFinite_def]
  have hcard : Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} =
      ∑ x : F, Fintype.card {y : F // y^2+(W.a₁*x+W.a₃)*y =
        x^3+W.a₂*x^2+W.a₄*x+W.a₆} := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        (fun x y => W.toAffine.Equation x y)), Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro y
    rw [W.toAffine.equation_iff]
    constructor <;> intro h <;> linear_combination h
  rw [hcard]
  unfold pointCountOddFinite
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [squareRootCountOdd_correct hF, quadratic_fiber_card (Ring.two_ne_zero hF)]

end WeierstrassCurve
