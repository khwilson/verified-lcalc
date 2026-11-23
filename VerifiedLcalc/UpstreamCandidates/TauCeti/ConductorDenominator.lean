/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import Mathlib.Data.Rat.Lemmas

/-! # Conductor primes detected by the denominator of j -/

public section

namespace WeierstrassCurve

/-- The denominator of the rational j-invariant divides the discriminant of an integral
equation. -/
theorem j_den_dvd_discriminant (M : WeierstrassCurve ℤ) [(M.baseChange ℚ).IsElliptic] :
    (((M.baseChange ℚ).j.den : ℕ) : ℤ) ∣ M.Δ := by
  have h := Rat.den_dvd (M.c₄ ^ 3) M.Δ
  rw [Rat.divInt_eq_div, Int.cast_pow] at h
  simpa [j_eq, baseChange, map_c₄, map_Δ, div_eq_inv_mul] using h

/-- A prime dividing the denominator of the j-invariant divides the norm of the
algorithmic conductor. Thus it stays a conductor prime in every quadratic twist. -/
theorem prime_dvd_absNorm_algorithmicConductor_of_dvd_j_den (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {p : ℕ} (hp : p.Prime) (h : p ∣ W.j.den) : p ∣ Ideal.absNorm (W.algorithmicConductor ℤ) := by
  obtain ⟨C, hC⟩ := exists_smul_eq_reducedMinimalModel W
  let R := reducedMinimalModel W
  have hm := (isReducedMinimal_reducedMinimalModel W).isGlobalMinimal
  let := hm.isIntegral
  let M := integralModel ℤ R
  have hM : M.baseChange ℚ = R := baseChange_integralModel_eq ℤ R
  have : (M.baseChange ℚ).IsElliptic := hM ▸ inferInstanceAs R.IsElliptic
  have hj : (M.baseChange ℚ).j = W.j := by
    calc
      _ = R.j := by congr
      _ = (C • W).j := by congr 1; exact hC.symm
      _ = W.j := variableChange_j W C
  have hN : R.algorithmicConductor ℤ = W.algorithmicConductor ℤ := by
    calc
      _ = (C • W).algorithmicConductor ℤ := by congr 1; exact hC.symm
      _ = _ := algorithmicConductor_smul ℤ C W
  rw [← hN, hm.dvd_absNorm_algorithmicConductor_iff hM hp]
  have hden := j_den_dvd_discriminant M
  rw [hj] at hden
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hden

end WeierstrassCurve
