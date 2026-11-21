module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

open VerifiedLcalc VerifiedLcalc.EllipticCurve

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Exact LMFDB 37.a1 data, with supplied arithmetic evidence but no rank search.
certify_ec Invariants37 from
  { equation := ⟨0, 0, 1, -1, 0⟩
    bInvariants := some (0, -2, 1, -1)
    cInvariants := some (48, -216)
    discriminant := some 37
    jInvariant := some (110592 / 37)
    discriminantSign := some 1
    minimalDiscriminantAbs := some 37
    badPrimes := some [37]
    numBadPrimes := some 1
    conductor := some 37
    rootNumber := some (-1)
    dirichletCoefficients := some [1, -2, -3, 2, -2, 6, -1, 0]
    minimality := some ⟨[37]⟩
    localData := some ⟨none, none⟩ }

example : (Invariants37.curve.baseChange ℚ).j = 110592 / 37 := Invariants37.j_invariant
example : Invariants37.curve.Δ = 37 := Invariants37.discriminant
