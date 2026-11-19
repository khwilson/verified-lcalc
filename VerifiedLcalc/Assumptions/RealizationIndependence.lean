module

public import VerifiedLcalc.Assumptions.ModularityStatement
public import VerifiedLcalc.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section
namespace VerifiedLcalc.Assumptions

/-- Two genuine realizations of the same curve give the same entire continued
L-function. No semistability or conductor/sign equality is needed. -/
theorem ModularRealization.formL_eq {e : Artifacts.CurveEquation}
    (m n : ModularRealization e) : m.formL = n.formL := by
  have hm : AnalyticOnNhd ℂ m.formL Set.univ :=
    fun z _ => m.formL_differentiable.analyticAt z
  have hn : AnalyticOnNhd ℂ n.formL Set.univ :=
    fun z _ => n.formL_differentiable.analyticAt z
  apply hm.eq_of_eventuallyEq hn (z₀ := (3 : ℂ))
  have hopen : IsOpen {s : ℂ | (2 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (3 : ℂ) ∈ {s : ℂ | (2 : ℝ) < s.re})]
    with s hs
  exact (m.formL_eq_curveLSeries s hs).symm.trans (n.formL_eq_curveLSeries s hs)

/-- Analytic rank is independent of which general modular realization was used. -/
theorem ModularRealization.analyticOrder_eq {e : Artifacts.CurveEquation}
    (m n : ModularRealization e) (s : ℂ) :
    analyticOrderAt m.formL s = analyticOrderAt n.formL s := by
  rw [m.formL_eq n]

end VerifiedLcalc.Assumptions
