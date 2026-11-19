module

public import VerifiedLcalc.EllipticCurve.CentralFinite
public import VerifiedLcalc.EllipticCurve.CentralTail
public import VerifiedLcalc.EllipticCurve.Coefficients

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Remaining analytic obligations for an actual central value. The series
must be the convergent split-Mellin exponential series, not the raw Dirichlet
series evaluated outside its convergence domain. The coefficient majorant and
prefix identity are mathematical proofs, never unchecked runtime flags. -/
structure CentralSeriesEvidence (r : CentralResult) (value : ℝ) where
  series : Nat → ℝ
  formula : HasSum series value
  finiteSum : (∑ j ∈ Finset.range r.termLimit, series j) =
    centralFiniteValue r.coefficients r.rootNumber (2 * Real.pi / Real.sqrt r.conductor)
  majorant : ∀ j, |series j| ≤ ((1 + r.rootNumber : Int).natAbs : ℝ) *
    (((j + 1 : Nat) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (j + 1))

/-- Complete interval soundness including argument approximation, signed finite
summation and analytic tail. It is conditional on the explicit series evidence,
not on any floating-point agreement with a reference value. -/
theorem centralPayload_sound {r : CentralResult} {value : ℝ}
    (h : CentralPayloadCorrect r) (e : CentralSeriesEvidence r value) :
    r.box.Contains (Complex.ofReal value) := by
  obtain ⟨hn, _, _, hal, hah, _, remainder, hrem, htail, hbox⟩ := h
  have hα := alphaBounds_correct r.conductor r.policy.precisionBits hn
  rw [← hal, ← hah] at hα
  have hf := centralFiniteBounds_correct r.coefficients r.rootNumber r.alphaLo r.alphaHi
    r.policy.precisionBits (2 * Real.pi / Real.sqrt r.conductor) hα
  obtain ⟨hq, hr, heq⟩ := squareTailBound_correct hrem
  have hq' : (0 : ℝ) ≤ (r.geometricUpper : ℝ) := by exact_mod_cast hq
  have hr' : (r.geometricUpper : ℝ) *
      (((r.termLimit + 2 : Nat) : ℝ) / (r.termLimit + 1 : Nat)) ^ 2 < 1 := by
    have hr0 : ((squareTailRatio r.geometricUpper r.termLimit : Rat) : ℝ) < 1 := by
      exact_mod_cast hr
    simpa [squareTailRatio] using hr0
  have ht := central_tail_error e.series value ((1 + r.rootNumber : Int).natAbs : ℝ)
    r.geometricUpper r.termLimit e.formula (by positivity) hq' hr' e.majorant
  rw [e.finiteSum] at ht
  have htval : (r.tail : ℝ) = ((1 + r.rootNumber : Int).natAbs : ℝ) *
      ((((r.termLimit + 1 : Nat) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (r.termLimit + 1)) /
        (1 - (r.geometricUpper : ℝ) *
          (((r.termLimit + 2 : Nat) : ℝ) / (r.termLimit + 1 : Nat)) ^ 2)) := by
    rw [htail, heq]
    push_cast [squareTailRatio]
    rfl
  rw [← htval] at ht
  rw [hbox]
  constructor
  · change (((Numerics.rationalExpSumBounds r.policy.precisionBits
        ((centralTerms r.coefficients r.rootNumber r.alphaLo r.alphaHi).map Prod.snd)).1 - r.tail : Rat) : ℝ) ≤ value ∧
      value ≤ (((Numerics.rationalExpSumBounds r.policy.precisionBits
        ((centralTerms r.coefficients r.rootNumber r.alphaLo r.alphaHi).map Prod.snd)).2 + r.tail : Rat) : ℝ)
    push_cast
    have ha := abs_le.mp ht
    constructor <;> linarith [hf.1, hf.2, ha.1, ha.2]
  · change (0 : ℝ) ∈ Set.Icc ((0 : Rat) : ℝ) ((0 : Rat) : ℝ)
    norm_num

theorem evaluateCentral_sound {equation : Artifacts.CurveEquation} {conductor : Nat}
    {rootNumber : Int} {limit : Nat} {policy : PrecisionPolicy} {r : CentralResult}
    {value : ℝ}
    (h : evaluateCentral equation conductor rootNumber limit policy = some r)
    (e : CentralSeriesEvidence r value) : r.box.Contains (Complex.ofReal value) :=
  centralPayload_sound (evaluateCentral_correct h).2.2.2.2.2 e

/-- Once the real central value has the required mathematical series evidence,
separation of its computed interval proves analytic order zero. The function's
relationship to any elliptic curve must still be established by the caller. -/
theorem analyticOrder_zero_of_central {f : ℂ → ℂ} {center : ℂ} {r : CentralResult}
    (hf : AnalyticAt ℂ f center) (h : CentralPayloadCorrect r)
    (e : CentralSeriesEvidence r (f center).re)
    (hseparated : r.box.excludesZero = true) : analyticOrderAt f center = 0 := by
  have hn := Box.excludesZero_sound hseparated (centralPayload_sound h e)
  apply hf.analyticOrderAt_eq_zero.mpr
  intro hz
  apply hn
  simp [hz]

end VerifiedLcalc.EllipticCurve
