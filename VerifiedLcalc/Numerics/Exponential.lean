module

public import VerifiedLcalc.Numerics.Dyadic
public import VerifiedLcalc.Upstream.LedvinkaExponential
public meta import VerifiedLcalc.Upstream.LedvinkaExponential

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Export the proved exponential bounds as a real complex-certificate box.
Both endpoints are exact rationals obtained from the computed dyadic bounds. -/
def exponentialBox (x : Dyadic) (prec : Nat) : Box :=
  let bounds := expBounds x prec
  boxOfDyadics bounds.1 bounds.2 0 0

/-- The executable bound computation encloses the mathematical exponential,
for every dyadic argument and every requested precision. -/
theorem exponentialBox_correct (x : Dyadic) (prec : Nat) :
    (exponentialBox x prec).Contains (Complex.ofReal (Real.exp (Dyadic.toReal x))) := by
  have h := expBounds_bounds x prec
  constructor
  · exact h
  · change (0 : ℝ) ∈ Set.Icc (((0 : Dyadic).toRat : ℚ) : ℝ)
      (((0 : Dyadic).toRat : ℚ) : ℝ)
    norm_num

/-- A concrete positive argument evaluated by the imported exponential extension. -/
theorem exp_one_enclosure :
    Real.exp 1 ∈ Set.Icc (((2718 : ℚ) / 1000 : ℚ) : ℝ) (((2719 : ℚ) / 1000 : ℚ) : ℝ) := by
  dyadic_interval [prec := 20]

/-- Negative exponential weights are needed in central-value evaluation. -/
theorem exp_neg_one_enclosure :
    Real.exp (-1) ∈ Set.Icc (((3678794 : ℚ) / 10000000 : ℚ) : ℝ)
      (((3678795 : ℚ) / 10000000 : ℚ) : ℝ) := by
  dyadic_interval [prec := 28]

/-- Interval arguments use the endpoint-monotonicity proof, not just scalar tests. -/
theorem exp_negative_interval (x : ℝ) (hx : x ∈ Set.Icc (-2 : ℝ) (-1)) :
    Real.exp x ∈ Set.Icc (((13 : ℚ) / 100 : ℚ) : ℝ) (((37 : ℚ) / 100 : ℚ) : ℝ) := by
  dyadic_interval [prec := 20]

end VerifiedLcalc.Numerics
