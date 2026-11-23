/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Invariants
public import VerifiedLcalc.Verification.AbcQuality

/-! # Checked enclosures for the modified Szpiro ratio -/

@[expose] public section

namespace VerifiedLcalc.Certification

open EllipticCurve

/-- Check the absolute error of a modified Szpiro ratio report by directed rational
bounds on the two logarithms. -/
def modifiedSzpiroRatioValid (curve : WeierstrassCurve ℤ) (conductor : ℕ)
    (reported error : ℚ) : Bool :=
  decide (1 < conductor ∧ 0 ≤ error) &&
    ratioErrorValid (logNatBounds (max (curve.c₄.natAbs ^ 3) (curve.c₆.natAbs ^ 2)))
      (logNatBounds conductor) reported error

/-- An accepted enclosure for the arithmetic data encloses the actual ratio of the
minimal equation, using TauCeti's algorithmic conductor norm. -/
def modifiedSzpiroRatioFactsOfCheck (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (evidence : ModifiedSzpiroRatioEvidence curve)
    (reported error : ℚ) (h : modifiedSzpiroRatioValid curve evidence.conductor
      reported error = true) : ModifiedSzpiroRatioFacts curve := by
  rw [modifiedSzpiroRatioValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact {
    toModifiedSzpiroRatioEvidence := evidence
    one_lt_conductor := h.1.1
    reported := reported
    error := error
    error_nonneg := h.1.2
    within_error := ratioErrorValid_sound (logNatBounds_sound _)
      (logNatBounds_sound _) h.2 }

end VerifiedLcalc.Certification
