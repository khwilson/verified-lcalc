import Lake
open Lake DSL

package «verified-lcalc»

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "31ce06eaadf4a200c0e1407c5f10953cf606b8f8"
require TauCeti from git "https://github.com/TauCetiProject/TauCeti" @
  "e0e414ce57522ba17560057ad0d7f2edab91bf0c"

lean_lib VerifiedLcalc

-- Keep the matrix inputs in sync with lakefile.toml.
input_file witness_tests_fixtures_lmfdb_112_a2 where
  path := "tests/fixtures/lmfdb/112.a2.json"
  text := true

input_file witness_tests_fixtures_lmfdb_179_a1 where
  path := "tests/fixtures/lmfdb/179.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_197_a1 where
  path := "tests/fixtures/lmfdb/197.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_214_a1 where
  path := "tests/fixtures/lmfdb/214.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_243_a1 where
  path := "tests/fixtures/lmfdb/243.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_254_a1 where
  path := "tests/fixtures/lmfdb/254.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_275_a1 where
  path := "tests/fixtures/lmfdb/275.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_286_f1 where
  path := "tests/fixtures/lmfdb/286.f1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_288_a1 where
  path := "tests/fixtures/lmfdb/288.a1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_291_d1 where
  path := "tests/fixtures/lmfdb/291.d1.json"
  text := true

input_file witness_tests_fixtures_lmfdb_37_a1_trace_hash where
  path := "tests/fixtures/lmfdb/37.a1-trace-hash-source.json"
  text := true

input_file torsionFixture120b4 where
  path := "tests/fixtures/torsion/120.b4.json"
  text := true

lean_lib VerifiedLcalcTests where
  srcDir := "tests"
  needs := #[
    `@/witness_tests_fixtures_lmfdb_112_a2,
    `@/witness_tests_fixtures_lmfdb_179_a1,
    `@/witness_tests_fixtures_lmfdb_197_a1,
    `@/witness_tests_fixtures_lmfdb_214_a1,
    `@/witness_tests_fixtures_lmfdb_243_a1,
    `@/witness_tests_fixtures_lmfdb_254_a1,
    `@/witness_tests_fixtures_lmfdb_275_a1,
    `@/witness_tests_fixtures_lmfdb_286_f1,
    `@/witness_tests_fixtures_lmfdb_288_a1,
    `@/witness_tests_fixtures_lmfdb_291_d1,
    `@/witness_tests_fixtures_lmfdb_37_a1_trace_hash,
    `@/torsionFixture120b4]

input_file witness_data_witnesses_11a1 where
  path := "data/witnesses/11a1.json"
  text := true

input_file witness_data_witnesses_37a1 where
  path := "data/witnesses/37a1.json"
  text := true

input_file witness_data_witnesses_112a2 where
  path := "data/witnesses/112a2.json"
  text := true

input_file witness_data_curve_data_11a1 where
  path := "data/curve-data/11a1.json"
  text := true

input_file witness_data_curve_data_37a1 where
  path := "data/curve-data/37a1.json"
  text := true

@[default_target]
lean_lib CertifiedCurves where
  srcDir := "examples/certify_ec"
  needs := #[
    `@/witness_data_witnesses_11a1,
    `@/witness_data_witnesses_37a1,
    `@/witness_data_witnesses_112a2,
    `@/witness_data_curve_data_11a1,
    `@/witness_data_curve_data_37a1]
