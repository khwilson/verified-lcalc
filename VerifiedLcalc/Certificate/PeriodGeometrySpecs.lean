/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # LMFDB period area and height normalization

The area is the ordinary Euclidean covolume in the complex plane of the
periods of `dx / (2y + a₁x + a₃)`. On a global minimal equation this is the
area for a Néron differential. The height formulas follow the producer
[ecdata](https://github.com/JohnCremona/ecdata/blob/master/scripts/files.py).
-/

@[expose] public noncomputable section

namespace VerifiedLcalc

/-- Euclidean covolume of the period lattice of the given equation's invariant differential. -/
def complexPeriodArea (W : WeierstrassCurve ℚ) [W.IsElliptic] : ℝ :=
  ZLattice.covolume ((W.map (Rat.castHom ℂ)).periodLattice) MeasureTheory.volume

/-- The Faltings height in the catalogue normalization on a globally minimal equation. -/
def catalogueFaltingsHeight (W : WeierstrassCurve ℚ) [W.IsElliptic] : ℝ :=
  -Real.log (complexPeriodArea W) / 2

/-- The catalogue's stable height formula, with the discriminant and rational
j-invariant denominator from the same equation as the area. -/
def catalogueStableFaltingsHeight (W : WeierstrassCurve ℚ) [W.IsElliptic] : ℝ :=
  catalogueFaltingsHeight W + Real.log ((W.j.den : ℝ) / |(W.Δ : ℝ)|) / 12

/-- The producer sorts by increasing Faltings height, then increasing native LMFDB number.
The native indices in a complete ordered class start at zero. -/
def faltingsPrecedes {n : ℕ} (height : Fin n → ℝ) (i j : Fin n) : Prop :=
  height i < height j ∨ height i = height j ∧ i < j

end VerifiedLcalc
