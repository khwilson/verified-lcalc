import Lake
open Lake DSL

package «verified-lcalc»

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "31ce06eaadf4a200c0e1407c5f10953cf606b8f8"
require TauCeti from git "https://github.com/TauCetiProject/TauCeti" @
  "e0e414ce57522ba17560057ad0d7f2edab91bf0c"

lean_lib VerifiedLcalc

input_dir lmfdbCIWitnesses where
  path := "tests/fixtures/lmfdb"
  text := true

lean_lib VerifiedLcalcTests where
  srcDir := "tests"
  needs := #[`@/lmfdbCIWitnesses]

-- JSON is an explicit Lake input. Editing a witness invalidates its consumers.
input_dir certificateWitnesses where
  path := "data/witnesses"
  text := true

input_dir curveDataWitnesses where
  path := "data/curve-data"
  text := true

@[default_target]
lean_lib CertifiedCurves where
  srcDir := "examples/certify_ec"
  needs := #[`@/certificateWitnesses, `@/curveDataWitnesses]
