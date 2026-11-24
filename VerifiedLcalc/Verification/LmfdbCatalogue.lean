/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Isogeny

/-! # Conductor roster distinctness and singleton catalogue indices -/

public section

namespace VerifiedLcalc.ConductorClassRoster

/-- Strict coefficient order puts equal L-functions at the same roster index. -/
theorem eq_of_LFunction_eq {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (roster : ConductorClassRoster curve) (i j : Fin roster.size)
    (heq : (roster.representatives i).LFunction = (roster.representatives j).LFunction) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · obtain ⟨n, -, -, hn⟩ := roster.ordered i j h
    rw [heq] at hn
    exact (lt_irrefl _ hn).elim
  · exact h
  · obtain ⟨n, -, -, hn⟩ := roster.ordered j i h
    rw [heq] at hn
    exact (lt_irrefl _ hn).elim

/-- Distinct positions in a checked roster have non-isogenous representatives. -/
theorem eq_of_isogeny {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (roster : ConductorClassRoster curve) (i j : Fin roster.size)
    (φ : TauCeti.Isogeny (roster.representatives i).toAffine (roster.representatives j).toAffine) :
    i = j := by
  let := roster.elliptic i
  let := roster.elliptic j
  exact roster.eq_of_LFunction_eq i j φ.LFunction_eq

end VerifiedLcalc.ConductorClassRoster

namespace VerifiedLcalc.CremonaSingletonEvidence

/-- The class of the input curve has zero-based index zero in every singleton conductor roster. -/
theorem classIndex_zero {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (evidence : CremonaSingletonEvidence curve) (h : evidence.onlyClass.isSome) :
    (evidence.onlyClass.get h).val.classIndex.val = 0 := by
  let roster := evidence.onlyClass.get h
  have bound : roster.val.classIndex.val < 1 :=
    lt_of_lt_of_eq roster.val.classIndex.isLt roster.property
  exact Nat.lt_one_iff.mp bound

/-- The actual position in a singleton isogeny class has one-based index one in any order. -/
theorem curveIndex_one {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (evidence : CremonaSingletonEvidence curve) (h : evidence.onlyCurve.isSome) :
    (evidence.onlyCurve.get h).val.curveIndex.val + 1 = 1 := by
  let model := evidence.onlyCurve.get h
  have bound : model.val.curveIndex.val < 1 :=
    lt_of_lt_of_eq model.val.curveIndex.isLt model.property
  exact congrArg (· + 1) (Nat.lt_one_iff.mp bound)

end VerifiedLcalc.CremonaSingletonEvidence
