/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Support.Torsion
public import VerifiedLcalc.EllipticCurve.TorsionBound

/-! # Finite torsion bounds and intrinsic torsion for the trivial group -/

@[expose] public section

namespace VerifiedLcalc.Certification

/-- Convert the raw two-prime check into explicit finite-field and point-count facts. -/
def torsionDivisorFacts_of_check (curve : WeierstrassCurve ℤ)
    (evidence : TorsionBoundWitness)
    (h : EllipticCurve.checkTorsionBound curve evidence.firstPrime
      evidence.secondPrime evidence.bound = true) : TorsionDivisorFacts curve := by
  have hcheck := h
  simp only [EllipticCurve.checkTorsionBound, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    EllipticCurve.isPrime_correct, and_assoc] at h
  rcases h with ⟨hp, hp₂, hpg, hq, hq₂, hqg, hgcd, hpos⟩
  have hfp : Fact evidence.firstPrime.Prime := ⟨hp⟩
  have hfq : Fact evidence.secondPrime.Prime := ⟨hq⟩
  have hfirst : (curve.baseChange (ZMod evidence.firstPrime)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr ((EllipticCurve.goodReduction_correct curve _).mp hpg)⟩
  have hsecond : (curve.baseChange (ZMod evidence.secondPrime)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr ((EllipticCurve.goodReduction_correct curve _).mp hqg)⟩
  have hcounts : Nat.gcd
      (curve.baseChange (ZMod evidence.firstPrime)).pointCount
      (curve.baseChange (ZMod evidence.secondPrime)).pointCount = evidence.bound := by
    simpa only [EllipticCurve.computePointCount_correct] using hgcd
  exact ⟨evidence, hp, hp₂, hfirst, hq, hq₂, hsecond, hcounts,
    EllipticCurve.checkTorsionBound_correct curve _ _ _ hcheck, none⟩

end VerifiedLcalc.Certification

namespace VerifiedLcalc.TorsionDivisorFacts

/-- Reconstruct the historical finite-check proposition from the mathematical facts. -/
theorem checked {curve : WeierstrassCurve ℤ}
    (facts : TorsionDivisorFacts curve) :
    EllipticCurve.checkTorsionBound curve facts.evidence.firstPrime
      facts.evidence.secondPrime facts.evidence.bound = true := by
  have hfp : Fact facts.evidence.firstPrime.Prime := ⟨facts.firstPrime_prime⟩
  have hfq : Fact facts.evidence.secondPrime.Prime := ⟨facts.secondPrime_prime⟩
  have hp := (EllipticCurve.isPrime_correct _).mpr facts.firstPrime_prime
  have hq := (EllipticCurve.isPrime_correct _).mpr facts.secondPrime_prime
  have hp₂ := (bne_iff_ne.mpr facts.firstPrime_odd)
  have hq₂ := (bne_iff_ne.mpr facts.secondPrime_odd)
  have hpg : EllipticCurve.goodReduction curve facts.evidence.firstPrime = true :=
    (EllipticCurve.goodReduction_correct curve _).mpr
      (isUnit_iff_ne_zero.mp facts.firstGoodReduction.isUnit)
  have hqg : EllipticCurve.goodReduction curve facts.evidence.secondPrime = true :=
    (EllipticCurve.goodReduction_correct curve _).mpr
      (isUnit_iff_ne_zero.mp facts.secondGoodReduction.isUnit)
  have hgcd : Nat.gcd
      (EllipticCurve.computePointCount curve facts.evidence.firstPrime)
      (EllipticCurve.computePointCount curve facts.evidence.secondPrime) =
      facts.evidence.bound := by
    simpa only [← EllipticCurve.computePointCount_correct] using facts.pointCountGcd
  have hbound := bne_iff_ne.mpr (Nat.ne_of_gt facts.valid.2)
  simp [EllipticCurve.checkTorsionBound, hp, hp₂, hpg, hq, hq₂, hqg, hgcd, hbound]

end VerifiedLcalc.TorsionDivisorFacts

namespace VerifiedLcalc.IntrinsicTorsionFact

variable {curve : WeierstrassCurve ℤ}

/-- Every subgroup of the trivial rational torsion group has cardinality one. -/
theorem card_subgroup (fact : IntrinsicTorsionFact curve)
    (S : AddSubgroup (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point)) :
    Nat.card S = fact.reported := by
  let _ := (Nat.card_eq_one_iff_unique.mp fact.torsion_card).1
  exact Nat.card_unique.trans fact.reported_eq_one.symm

/-- In particular, any biadditive pairing on this rational torsion group
has a left radical of order one. -/
theorem card_radical (fact : IntrinsicTorsionFact curve) {A : Type*} [AddCommGroup A]
    (pairing : AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point →+
      (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point →+ A)) :
    Nat.card pairing.ker = fact.reported :=
  fact.card_subgroup pairing.ker

end VerifiedLcalc.IntrinsicTorsionFact
