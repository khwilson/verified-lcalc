/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-! # The rank-zero case of the p-adic regulator determinant -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- The p-adic regulator of a rank-zero rational elliptic curve is the determinant of its
empty height matrix. The index set uses the finrank of the actual point module, which equals
the size of a Mordell–Weil basis modulo torsion. Every height matrix on this index set is
empty, independently of the ordinary height normalization. -/
noncomputable def rankZeroPadicRegulator (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h : Module.finrank ℤ W.toAffine.Point = 0) (p : ℕ) [Fact p.Prime] : ℚ_[p] :=
  Matrix.det (fun i _ => Fin.elim0 (Fin.cast h i) :
    Matrix (Fin (Module.finrank ℤ W.toAffine.Point))
      (Fin (Module.finrank ℤ W.toAffine.Point)) ℚ_[p])

/-- The determinant of the empty p-adic height matrix equals one. -/
theorem rankZeroPadicRegulator_eq_one (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (h : Module.finrank ℤ W.toAffine.Point = 0) (p : ℕ) [Fact p.Prime] :
    rankZeroPadicRegulator W h p = 1 := by
  let : IsEmpty (Fin (Module.finrank ℤ W.toAffine.Point)) :=
    ⟨fun i => Fin.elim0 (Fin.cast h i)⟩
  exact Matrix.det_isEmpty

end VerifiedLcalc.EllipticCurve
