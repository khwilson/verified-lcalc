/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC

/-! # Native semistable Serre-invariant records -/

@[expose] public section

namespace VerifiedLcalcTests.SerreInvariants

open VerifiedLcalc

-- https://www.lmfdb.org/EllipticCurve/Q/data/37.a1
certify_ec Serre37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"minimality":[37],"serre_invariants":[[37,38,1]]}"#

-- https://www.lmfdb.org/EllipticCurve/Q/data/69.a1
certify_ec Serre69 from
  { equation := ⟨1, 0, 1, -16, -25⟩, minimality := some ⟨[3, 23, 23]⟩,
    serreInvariants := some [(2, 2, 3), (3, 4, 23), (23, 24, 3)] }

-- https://www.lmfdb.org/EllipticCurve/Q/data/11.a2
certify_ec Serre11 from
  { equation := ⟨0, -1, 1, -10, -20⟩, minimality := some ⟨[11, 11, 11, 11, 11]⟩,
    serreInvariants := some [(5, 2, 1), (11, 12, 1)] }

end VerifiedLcalcTests.SerreInvariants
