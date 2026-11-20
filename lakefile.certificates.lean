import Lake
open Lake DSL

package «verified-lcalc»

require mathlib from "../mathlib4"

lean_lib VerifiedLcalc

lean_lib VerifiedLcalcTests where
  srcDir := "tests"

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
  extraDepTargets := #[`certificateWitnesses, `curveDataWitnesses]
