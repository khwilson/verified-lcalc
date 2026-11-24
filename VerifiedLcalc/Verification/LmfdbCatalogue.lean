/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Isogeny

/-! # Distinctness in a checked conductor roster -/

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
