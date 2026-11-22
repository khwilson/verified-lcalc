/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # The second logarithmic moment of a Mellin transform -/

public section

namespace VerifiedLcalc.Numerics

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- Twice differentiating a Mellin transform inside a vertical strip inserts `(log t)²`.
The same strict strip condition as for the first derivative suffices. -/
theorem mellin_second_derivative_of_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s : ℂ} {a b : ℝ} (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (· ^ (-a))) (hupper : s.re < a)
    (hzero : f =O[𝓝[>] 0] (· ^ (-b))) (hlower : b < s.re) :
    MellinConvergent (fun t => Real.log t ^ 2 • f t) s ∧
      iteratedDeriv 2 (mellin f) s = mellin (fun t => Real.log t ^ 2 • f t) s := by
  obtain ⟨lo, hlo, hslo⟩ := exists_between hlower
  obtain ⟨hi, hshi, hhi⟩ := exists_between hupper
  have hloclog : LocallyIntegrableOn (fun t => Real.log t • f t) (Ioi 0) :=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed hlocal
      (Real.continuousOn_log.mono fun _ ht => ne_of_gt ht)
  obtain ⟨hconv, hderiv⟩ := mellin_hasDerivAt_of_isBigO_rpow hloclog
    (isBigO_rpow_top_log_smul hhi htop) hshi (isBigO_rpow_zero_log_smul hlo hzero) hslo
  have hstrip : ∀ᶠ z : ℂ in 𝓝 s, b < z.re ∧ z.re < a :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hlower, hupper⟩
  have heq : deriv (mellin f) =ᶠ[𝓝 s] mellin (fun t => Real.log t • f t) :=
    hstrip.mono fun _ hz =>
      (mellin_hasDerivAt_of_isBigO_rpow hlocal htop hz.2 hzero hz.1).2.deriv
  have hsecond := heq.deriv_eq.trans hderiv.deriv
  exact ⟨by simpa only [pow_two, mul_smul] using hconv,
    by simpa only [iteratedDeriv_succ, iteratedDeriv_zero, pow_two, mul_smul] using hsecond⟩

end VerifiedLcalc.Numerics
