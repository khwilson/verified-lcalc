module

public import VerifiedLcalc.EllipticCurve.CoefficientCore

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- A sufficient, decidable prefix criterion. Prime powers beyond the prefix
need no local-factor identification. Repeated primes within it require a trace
whose magnitude rules out all bad local factors in the actual curve. -/
def prefixSupported (e : (WeierstrassCurve ℤ)) (limit : Nat) : Bool :=
  ((List.range (limit + 1)).filter isPrime).all fun p =>
    goodReduction e p && decide (limit < p ^ 2 ∨ 1 < (frobeniusTrace e p).natAbs)

end VerifiedLcalc.EllipticCurve
