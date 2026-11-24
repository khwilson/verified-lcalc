/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Fixtures.LmfdbCatalogue

/-! # The native Cremona 43a1 labels with separately parameterized singleton evidence -/

@[expose] public section

namespace VerifiedLcalcTests.Cremona43

open VerifiedLcalc VerifiedLcalcTests.LmfdbCatalogue43

/-- The actual conductor is in the published Cremona range. -/
def rangeEvidence : CremonaSingletonEvidence source where
  conductor := ⟨43, by decide +kernel⟩
  conductor_eq := conductor

/-- The combined subject evidence, conditional on the two independent enumeration proofs. -/
def evidence {E R : WeierstrassCurve ℚ} (hE : CurveComplete E) (hR : RosterComplete R) :
    CremonaSingletonEvidence source :=
  { rangeEvidence with
    onlyClass := some ⟨roster hR, rfl⟩
    onlyCurve := some ⟨model hE, rfl⟩ }

section

variable {E R : WeierstrassCurve ℚ} [hE : CurveComplete E] [hR : RosterComplete R]

certify_ec Checked from_json_string
  r#"{"ainvs":[0,1,1,0,0],"Ciso":"43a","Clabel":"43a1","Cnumber":1,"conductor":43,
    "minimality":[43],"local_data":{"at_two":null,"at_three":null}}"#
  with_proofs ({ cremonaSingleton := some (evidence hE hR) } : IntegralCurveProofs source)

end

end VerifiedLcalcTests.Cremona43
