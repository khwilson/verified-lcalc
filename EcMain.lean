import VerifiedLcalc.EllipticCurve.Arithmetic
import VerifiedLcalc.Lmfdb

open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Execute proved good-prime arithmetic on the LMFDB fixture. This command
computes point counts and Euler coefficients; it does not compute ranks. -/
def main (args : List String) : IO UInt32 := do
  let summary := args == ["--summary"]
  let validArgs := match args with
    | [] | ["--summary"] | ["--curve", _] => true
    | _ => false
  if !validArgs then
    IO.eprintln "Usage: lake exe ec-coefficients [--summary | --curve LMFDB_LABEL]"
    return 2
  let selected := match args with
    | ["--curve", label] => Lmfdb.cases.filter (fun (c : Regression.Case) => c.input.label == label)
    | _ => Lmfdb.cases
  if selected.isEmpty then
    IO.eprintln "No matching curve in the fixture."
    return 2
  if !summary then IO.println "label,prime,status,points,trace,a_prime_squared"
  let mut supported := 0
  let mut skipped := 0
  for c in selected do
    let equation := c.input.equation
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23] do
      match analysePrime equation p with
      | none =>
        skipped := skipped + 1
        if !summary then IO.println s!"{c.input.label},{p},bad-reduction-pending,,,"
      | some d =>
        supported := supported + 1
        if !summary then
          IO.println s!"{c.input.label},{p},good,{d.points},{d.trace},{localCoefficient d.trace p 2}"
  IO.eprintln s!"Arithmetic: {selected.length} curves; {supported} good-prime computations, {skipped} bad-prime cases pending. No analytic ranks computed."
  return 0
