module

public import VerifiedLcalc.EllipticCurve.BadPrime

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.BadPrimeExamples
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def curve389 : (WeierstrassCurve ℤ) := ⟨0, 1, 1, -2, 0⟩
def curve5077 : (WeierstrassCurve ℤ) := ⟨0, 0, 1, -7, 6⟩

/-- Kernel computation of the old resource-limit case, without p^2 point counting. -/
theorem curve389_trace : frobeniusTrace curve389 389 = 1 := by
  let : Fact (Nat.Prime 389) := ⟨by decide +kernel⟩
  rw [← singularTrace_correct curve389 389 (by decide +kernel)]
  decide +kernel

/-- The other old resource-limit case, using only 5077 tangent evaluations. -/
theorem curve5077_trace : frobeniusTrace curve5077 5077 = -1 := by
  let : Fact (Nat.Prime 5077) := ⟨by decide +kernel⟩
  rw [← singularTrace_correct curve5077 5077 (by decide +kernel)]
  decide +kernel

end VerifiedLcalc.EllipticCurve.BadPrimeExamples
