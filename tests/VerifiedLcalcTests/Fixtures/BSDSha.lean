/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Fixtures.BSDTamagawa
public import VerifiedLcalc.Certificate.Analytic.BSDQuotient

/-! # Conditional certification of the analytic quotient of 37.a1

The test receives the analytic enclosure, order, and positive denominator as hypotheses
specific to this equation. The command checks the reported decimal, integer, and prime list.
-/

@[expose] public section

namespace Curve37a1Sha
open VerifiedLcalc Modularity Curve37a1Tamagawa

/-- The analytic hypotheses for the fixed equation, expressed without an axiom or BSD identity. -/
def QuotientEvidence (order : ℕ) : Prop :=
  let E := model.baseChange ℚ
  0 < E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ) ∧
    ∀ m : ArithmeticModularRealization model, analyticOrderAt m.formL 1 = order ∧
      |(iteratedDeriv order m.formL 1).re / (order.factorial : ℝ) *
        (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
        (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ)) - 1|
        ≤ (1 : ℝ) / 100

/-- Keep the fixed rational numbers computationally visible when the proof is a premise. -/
def proofAttachment (h : QuotientEvidence 1) : IntegralCurveProofs model where
  tamagawaProduct := some product
  analyticSha := some
    { order := 1
      reported := 1
      error := ⟨1 / 100, by decide +kernel⟩
      order_correct m := (h.2 m).1
      denominator_pos := h.1
      correct m := by simpa using (h.2 m).2 }

/-- Curve-specific analytic evidence supplied as a local hypothesis to the command. -/
class GivenQuotientEvidence (order : outParam ℕ) : Prop where
  /-- Identify the order used by the fixed report. -/
  order_eq : order = 1
  /-- The quotient and denominator premises for the supplied analytic order. -/
  evidence : QuotientEvidence order

/-- Specialize the supplied evidence to the order specified by the report. -/
theorem GivenQuotientEvidence.atOne {order : ℕ} (h : GivenQuotientEvidence order) :
    QuotientEvidence 1 :=
  h.order_eq ▸ h.evidence

section

variable {order : ℕ} [h : GivenQuotientEvidence order]

certify_ec ShaCertificate from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"tamagawa_product":1,"sha_an":"1.000",
      "sha_an_evidence":{"error":"1/100"},"sha":1,"sha_primes":[]}"#
  with_proofs (proofAttachment h.atOne)

end

end Curve37a1Sha
