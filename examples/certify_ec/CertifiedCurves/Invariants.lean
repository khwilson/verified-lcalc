module
public import VerifiedLcalc.Tactic.CertifyEC

/-! # Invariant certificates for rational curves -/

@[expose] public section

open VerifiedLcalc VerifiedLcalc.EllipticCurve

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
    semistable := some true
    squarefreeDiscriminant := some true
    localInvariants := some [
      { prime := 37, discriminantValuation := some 1, jDenominatorValuation := some 1,
        reductionType := some (-1) }]
    conductor := some 37
    rootNumber := some (-1)
    dirichletCoefficients := some [1, -2, -3, 2, -2, 6, -1, 0]
    minimality := some ⟨[37]⟩
    localData := some ⟨none, none⟩ }

example : (Invariants37.curve.baseChange ℚ).j = 110592 / 37 := Invariants37.j_invariant
example : Invariants37.curve.Δ = 37 := Invariants37.discriminant

certify_ec ProofCarrying37 from
  { equation := Invariants37.curve }
  with_proofs Invariants37.discriminant_witness.toProofs

certify_ec FileProofCarrying37 from_json "../../../data/curve-data/37a1.json"
  with_proofs Invariants37.discriminant_witness.toProofs

-- LMFDB 50.b3, with a supplied translation to a type-II equation at 5.
certify_ec ExactAdditiveKodaira from_json_string
  r#"{"ainvs":[1,1,1,-3,1],"prime":5,"kodaira_symbol":2,"kodaira_terminal":[0,0,2]}"#
