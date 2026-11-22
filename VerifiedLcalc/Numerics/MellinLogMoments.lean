/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Logarithmic moments of a Mellin transform -/

public section

namespace VerifiedLcalc.Numerics

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- Each Mellin derivative inserts one log factor. The original strict strip
condition gives room for every finite number of logarithmic weights. -/
theorem mellin_iteratedDeriv_of_isBigO_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) {f : ℝ → E} {s : ℂ} {a b : ℝ} (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (· ^ (-a))) (hupper : s.re < a)
    (hzero : f =O[𝓝[>] 0] (· ^ (-b))) (hlower : b < s.re) :
    MellinConvergent (fun t => Real.log t ^ n • f t) s ∧
      iteratedDeriv n (mellin f) s = mellin (fun t => Real.log t ^ n • f t) s := by
  induction n generalizing f a b with
  | zero =>
    simp only [pow_zero, one_smul, iteratedDeriv_zero, and_true]
    exact mellinConvergent_of_isBigO_rpow hlocal htop hupper hzero hlower
  | succ n ih =>
    obtain ⟨lo, hlo, hslo⟩ := exists_between hlower
    obtain ⟨hi, hshi, hhi⟩ := exists_between hupper
    have hloclog : LocallyIntegrableOn (fun t => Real.log t • f t) (Ioi 0) :=
      LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed hlocal
        (Real.continuousOn_log.mono fun _ ht => ne_of_gt ht)
    obtain ⟨hconv, hderiv⟩ := ih hloclog
      (isBigO_rpow_top_log_smul hhi htop) hshi (isBigO_rpow_zero_log_smul hlo hzero) hslo
    have hstrip : ∀ᶠ z : ℂ in 𝓝 s, b < z.re ∧ z.re < a :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hlower, hupper⟩
    have heq : deriv (mellin f) =ᶠ[𝓝 s] mellin (fun t => Real.log t • f t) :=
      hstrip.mono fun _ hz =>
        (mellin_hasDerivAt_of_isBigO_rpow hlocal htop hz.2 hzero hz.1).2.deriv
    have h := (heq.iteratedDeriv_eq n).trans hderiv
    exact ⟨by simpa only [pow_succ, mul_smul] using hconv,
      by simpa only [iteratedDeriv_succ', pow_succ, mul_smul] using h⟩

end VerifiedLcalc.Numerics
