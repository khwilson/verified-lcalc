/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # The rational prime place used by local specifications -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The canonical height-one prime of `𝓞 ℚ` above the rational prime `p`.
This is the inverse of Mathlib's native `Rat.HeightOneSpectrum.primesEquiv`. -/
noncomputable def rationalPlace (p : ℕ) [Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩

end VerifiedLcalc.EllipticCurve
