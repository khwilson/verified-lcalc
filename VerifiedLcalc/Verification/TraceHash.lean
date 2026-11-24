/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes

/-! # Checking the published weighted trace fingerprint -/

@[expose] public section

namespace VerifiedLcalc.Certification

open EllipticCurve

/-- The proved coefficient vector consumes every published weight without truncation. -/
theorem _root_.VerifiedLcalc.TraceHashCoefficients.length_eq {curve : WeierstrassCurve ℤ}
    (evidence : TraceHashCoefficients curve) :
    evidence.coefficients.length = lmfdbTraceHashWeights.length := by
  rw [evidence.correct, List.length_map, lmfdbTraceHashWeights_length]

/-- The checked sum of a fully justified vector is the arithmetic trace hash of the curve. -/
def traceHashFact (curve : WeierstrassCurve ℤ) (evidence : TraceHashCoefficients curve)
    (value : ℤ) (valid : computeLmfdbTraceHash evidence.coefficients = value) :
    TraceHashFact curve where
  evidence := evidence
  value := value
  correct := by
    unfold lmfdbTraceHash
    rw [← evidence.correct]
    exact valid

end VerifiedLcalc.Certification
