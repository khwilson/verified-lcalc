import VerifiedLcalc.LmfdbSupplement
import VerifiedLcalc.EllipticCurve.Arithmetic
import VerifiedLcalc.Regression.ConditionalCore

open VerifiedLcalc.Regression VerifiedLcalc.Lmfdb

/-- Default mode is a strict coverage gate: inconclusive cases fail. `--inventory`
checks the fixture and reports coverage without claiming analytic computations.
`--conditional` uses the separately proved modularity-dependent certificate cache. -/
def main (args : List String) : IO UInt32 := do
  if args != [] && args != ["--inventory"] && args != ["--conditional"] then
    IO.eprintln "Usage: lake exe lmfdb-check [--inventory|--conditional]"
    return 2
  let labels := allCases.map (fun c => c.input.label)
  if labels.eraseDups.length != labels.length then
    IO.eprintln "Invalid fixture: duplicate curve labels."
    return 2
  if allCases.any (fun c => c.input.conductor == 0 ||
      VerifiedLcalc.EllipticCurve.discriminant c.input.equation == 0) then
    IO.eprintln "Invalid fixture: zero conductor or singular equation."
    return 2
  let conditional := args == ["--conditional"]
  let backend := if conditional then conditionalCertifiedBackend else pendingBackend
  let mut agrees := 0
  let mut mismatches := 0
  let mut inconclusive := 0
  for c in allCases do
    match checkCase backend c with
    | .agree => agrees := agrees + 1
    | .mismatch expected actual =>
      mismatches := mismatches + 1
      IO.eprintln s!"{c.input.label}: expected {expected}, got {actual}"
    | .inconclusive => inconclusive := inconclusive + 1
  IO.println s!"LMFDB: {allCases.length} curves; {agrees} matches, {mismatches} mismatches, {inconclusive} inconclusive."
  if conditional then
    IO.println "Conditional certificate cache: exact ranks depend on ellipticModularity; unresolved curves fail coverage."
  else
    IO.println "Default axiom-free elliptic backend is pending; these are reference-data checks."
  return if mismatches = 0 && (args == ["--inventory"] || inconclusive = 0) then 0 else 1
