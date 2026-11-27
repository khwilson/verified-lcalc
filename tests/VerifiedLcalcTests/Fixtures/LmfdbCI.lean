module

public import VerifiedLcalc.Tactic.CertifyEC

/-!
# LMFDB arithmetic certificate fixtures

The checked-in inputs are exact values from the LMFDB source snapshot. Each command elaborates
and checks the supplied witnesses before exporting the resulting Lean theorems for consumers.
The 112.a2 fixture covers both LMFDB rational generator coordinate lists.
-/

@[expose] public section

certify_ec LMFDB.C112a2 from_json "../../fixtures/lmfdb/112.a2.json"
certify_ec LMFDB.C179a1 from_json "../../fixtures/lmfdb/179.a1.json"
certify_ec LMFDB.C197a1 from_json "../../fixtures/lmfdb/197.a1.json"
certify_ec LMFDB.C214a1 from_json "../../fixtures/lmfdb/214.a1.json"
certify_ec LMFDB.C243a1 from_json "../../fixtures/lmfdb/243.a1.json"
certify_ec LMFDB.C254a1 from_json "../../fixtures/lmfdb/254.a1.json"
certify_ec LMFDB.C275a1 from_json "../../fixtures/lmfdb/275.a1.json"
certify_ec LMFDB.C286f1 from_json "../../fixtures/lmfdb/286.f1.json"
certify_ec LMFDB.C288a1 from_json "../../fixtures/lmfdb/288.a1.json"
certify_ec LMFDB.C291d1 from_json "../../fixtures/lmfdb/291.d1.json"
certify_ec LMFDB.C17a2 from_json "../../fixtures/lmfdb/17.a2-tamagawa.json"
certify_ec LMFDB.C11a2 from_json "../../fixtures/lmfdb/11.a2-tamagawa.json"
certify_ec LMFDB.C26b1 from_json "../../fixtures/lmfdb/26.b1-tamagawa.json"
certify_ec LMFDB.C49a4 from_json "../../fixtures/lmfdb/49.a4-tamagawa.json"
certify_ec LMFDB.C50a3 from_json "../../fixtures/lmfdb/50.a3-tamagawa.json"
certify_ec LMFDB.C50a1 from_json "../../fixtures/lmfdb/50.a1-tamagawa.json"
certify_ec LMFDB.C107200dh1 from_json "../../fixtures/lmfdb/107200.dh1-tamagawa.json"
