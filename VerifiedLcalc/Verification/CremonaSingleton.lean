/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic

/-! # Independence of historical ordering for singleton catalogue indices -/

public section

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
