module

public import VerifiedLcalc.Certificate.Support.SpecialValue
public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.NumericalRankSoundness

/-! # Verify a reported Taylor leading coefficient

The decoder supplies the report and an explicit error. This module connects
that finite check to the existing actual central-value and derivative
enclosures for the same arithmetic modular realization.
-/

@[expose] public section

namespace VerifiedLcalc
open Modularity Numerics

/-- Rescale outward raw derivative bounds by the positive factorial. -/
def SpecialLValueClaim.taylorBounds (order : Nat) (derivative : RealInterval) :
    RealInterval :=
  let scale : Rat := 1 / (order.factorial : Rat)
  intervalMul (scale, scale) derivative

/-- Check that a normalized Taylor interval is within the reported error. -/
def SpecialLValueClaim.Valid (claim : SpecialLValueClaim) (order : Nat)
    (derivative : RealInterval) : Bool :=
  let b := taylorBounds order derivative
  (⟨b.1 - claim.reported, b.2 - claim.reported, 0, 0⟩ : Box).withinCutoff claim.error

/-- Convert a finite checked interval into the reported absolute-error bound. -/
theorem specialValueError_of_check (claim : SpecialLValueClaim) (order : Nat)
    {d : ℝ} {derivative : RealInterval} (hD : derivative.Contains d)
    (h : claim.Valid order derivative = true) :
    |d / (order.factorial : ℝ) - (claim.reported : ℝ)| ≤ (claim.error : ℝ) := by
  let b := SpecialLValueClaim.taylorBounds order derivative
  let q := d / (order.factorial : ℝ)
  have hq : b.Contains q := by
    let scale : Rat := 1 / (order.factorial : Rat)
    have hb := intervalMul_sound (scale, scale) derivative (scale : ℝ) d
      ⟨le_rfl, le_rfl⟩ hD
    simpa [b, q, scale, SpecialLValueClaim.taylorBounds, div_eq_inv_mul] using hb
  have hbox : (⟨b.1 - claim.reported, b.2 - claim.reported, 0, 0⟩ : Box).Contains
      (Complex.ofReal (q - (claim.reported : ℝ))) := by
    constructor
    · exact ⟨by simpa only [Complex.ofReal_re, Rat.cast_sub] using
        sub_le_sub_right hq.1 _,
        by simpa only [Complex.ofReal_re, Rat.cast_sub] using sub_le_sub_right hq.2 _⟩
    · simp
  exact (Box.withinCutoff_sound h hbox).1

/-- Package a real raw derivative interval and the independently established order. -/
def SpecialLValueFacts.ofInterval (curve : WeierstrassCurve ℤ)
    (claim : SpecialLValueClaim) (order : Nat) (derivative : RealInterval)
    (valid : claim.Valid order derivative = true)
    (verified : ∀ m : ArithmeticModularRealization curve,
      analyticOrderAt m.formL 1 = order ∧
        derivative.Contains (iteratedDeriv order m.formL 1).re) :
    SpecialLValueFacts curve where
  order := order
  claim := claim
  correct m := by
    have h := verified m
    refine ⟨h.1, ?_⟩
    simpa only [div_eq_mul_inv] using
      specialValueError_of_check claim order h.2 valid

/-- Use the proved order zero and actual central-value enclosure. -/
def SpecialLValueFacts.ofCentralEnclosure (curve : WeierstrassCurve ℤ)
    (claim : SpecialLValueClaim) (r : EllipticCurve.CentralResult)
    (rank : ConditionalAnalyticRank curve) (hrank : rank.val = 0)
    (enclosure : CentralCurveEnclosure curve r)
    (valid : claim.Valid 0 (r.box.reLo, r.box.reHi) = true) :
    SpecialLValueFacts curve :=
  ofInterval curve claim 0 (r.box.reLo, r.box.reHi) valid fun m => by
    have h := rank.correct m
    rw [hrank] at h
    refine ⟨h, ?_⟩
    simpa only [iteratedDeriv_zero, Complex.ofReal_re, RealInterval.Contains,
      Set.mem_Icc] using (enclosure.contains m).1

/-- Use the proved order one and actual raw first-derivative enclosure. -/
def SpecialLValueFacts.ofDerivativeEnclosure (curve : WeierstrassCurve ℤ)
    (claim : SpecialLValueClaim) (r : EllipticCurve.DerivativeResult)
    (rank : ConditionalAnalyticRank curve) (hrank : rank.val = 1)
    (enclosure : DerivativeCurveEnclosure curve r)
    (valid : claim.Valid 1 r.realDerivativeBounds = true) :
    SpecialLValueFacts curve :=
  ofInterval curve claim 1 r.realDerivativeBounds valid fun m => by
    have h := rank.correct m
    rw [hrank] at h
    exact ⟨h, by simpa only [iteratedDeriv_one] using enclosure.contains m⟩

end VerifiedLcalc
