/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.IntegralPointCount
public import VerifiedLcalc.Certification.CurveData
public import Mathlib.Data.Finset.Union

/-! # Complete integral-point counts from supplied abscissa support -/

public section

namespace VerifiedLcalc

open EllipticWitness WeierstrassCurve

/-- All candidate pairs in the fibers of the supplied seeds, with duplicates removed. -/
@[expose] def integralFiberSolutions (curve : WeierstrassCurve ℤ) (seeds : List (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  seeds.toFinset.biUnion fun p => (integralYFiber curve p.1 p.2).image (p.1, ·)

/-- Checked seeds and exhaustive abscissa support characterize the set of all integral solutions. -/
theorem mem_integralFiberSolutions_iff {curve : WeierstrassCurve ℤ} {seeds : List (ℤ × ℤ)}
    (valid : affineCoordinatesValid curve seeds = true) (support : IntegralXSupport curve)
    (hs : support.xs ⊆ seeds.map Prod.fst) (p : ℤ × ℤ) :
    p ∈ integralFiberSolutions curve seeds ↔ curve.toAffine.Equation p.1 p.2 := by
  simp only [integralFiberSolutions, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact (mem_integralYFiber_iff (affineCoordinatesValid_sound curve seeds valid _ _ hq) _).mp hy
  · intro hp
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp (hs (support.covers _ _ hp))
    refine ⟨q, hq, p.2, ?_, Prod.ext hqx rfl⟩
    rw [← hqx] at hp
    exact (mem_integralYFiber_iff (affineCoordinatesValid_sound curve seeds valid _ _ hq) _).mpr hp

/-- The checked complete union of fibers counts the curve's affine integral points. -/
theorem integralPoints_finite_and_natCard_eq_fiber_count {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] {seeds : List (ℤ × ℤ)}
    (valid : affineCoordinatesValid curve seeds = true) (support : IntegralXSupport curve)
    (hs : support.xs ⊆ seeds.map Prod.fst) :
    Finite curve.integralPoints ∧
      Nat.card curve.integralPoints = (integralFiberSolutions curve seeds).card := by
  let mem := mem_integralFiberSolutions_iff valid support hs
  let point (p : integralFiberSolutions curve seeds) : curve.integralPoints :=
    ⟨curve.pointOfIntegralSolution p.val.1 p.val.2 ((mem _).mp p.property),
      curve.pointOfIntegralSolution_mem _ _ _⟩
  have injective : Function.Injective point := by
    intro p q hpq
    have h := congrArg Subtype.val hpq
    simp only [point, pointOfIntegralSolution_eq_some, Affine.Point.some.injEq] at h
    exact Subtype.ext (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2))
  have surjective : Function.Surjective point := by
    rintro ⟨P, hP⟩
    obtain ⟨x, y, h, rfl⟩ := (curve.mem_integralPoints_iff P).mp hP
    exact ⟨⟨(x, y), (mem _).mpr h⟩, rfl⟩
  let e := Equiv.ofBijective point ⟨injective, surjective⟩
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr e.symm

end VerifiedLcalc
