import Lean
import VerifiedLcalc.Lmfdb

open Lean VerifiedLcalc

def parseCurveRow (line : String) : Except String Regression.Case := do
  let fields := ((line.splitOn " ").filter (· != "")).toArray
  if fields.size != 57 then throw s!"Expected 57 columns, got {fields.size}"
  let label := fields[3]!
  let some conductor := fields[9]!.toNat? | throw s!"Invalid conductor for {label}"
  let some rank := fields[30]!.toNat? | throw s!"Invalid analytic_rank for {label}"
  let inv ← Json.parse fields[10]!
  let a ← inv.getArr?
  if a.size != 5 then throw s!"Invalid ainvs for {label}"
  let a1 ← a[0]!.getInt?
  let a2 ← a[1]!.getInt?
  let a3 ← a[2]!.getInt?
  let a4 ← a[3]!.getInt?
  let a6 ← a[4]!.getInt?
  return ⟨⟨label, conductor, ⟨a1, a2, a3, a4, a6⟩⟩, rank⟩

/-- Data ingestion only. Expected ranks are kept in Regression.Case and never
passed to the arithmetic or analytic backend. All input rows are retained. -/
def main : IO UInt32 := do
  let raw ← IO.FS.readFile "data/lmfdb/raw/curvedata-first-1200.txt"
  let mut cases : List Regression.Case := []
  let mut seen := Lmfdb.cases.map (·.input.label)
  for line in raw.splitOn "\n" do
    if line != "" && cases.length < 1000 then
      let c ← IO.ofExcept (parseCurveRow line)
      if !seen.contains c.input.label then
        seen := c.input.label :: seen
        cases := cases ++ [c]
  if cases.length != 1000 then throw (IO.userError "Source does not contain 1000 additional curves")
  let source := "module\n\npublic import VerifiedLcalc.Lmfdb\n\n@[expose] public section\nnamespace VerifiedLcalc.Lmfdb\n\nset_option maxRecDepth 100000\n\n" ++
    "-- Reference data from ecdata commit 25cec5ecfec8b9f016eb1631ac633194c2bed39f.\n" ++
    "-- Uses analytic_rank (column 30), not Mordell-Weil rank (column 28).\n" ++
    "def supplementalCases : List Regression.Case := [\n" ++
    String.intercalate ",\n" (cases.map (fun c => "  " ++ (reprStr c).replace "\n" " ")) ++
    "\n]\n\n-- Same 1100 inputs, sorted by label for a linear uniqueness certificate.\n" ++
    "def allCases : List Regression.Case := [\n" ++
    String.intercalate ",\n" (((Lmfdb.cases ++ cases).mergeSort
      (fun a b => a.input.label ≤ b.input.label)).map
      (fun c => "  " ++ (reprStr c).replace "\n" " ")) ++ "\n]\n\n" ++
    "theorem has_1000_additional_cases : supplementalCases.length = 1000 := by decide +kernel\n" ++
    "theorem has_1100_cases : allCases.length = 1100 := by decide +kernel\n\n" ++
    "end VerifiedLcalc.Lmfdb\n"
  IO.FS.writeFile "VerifiedLcalc/LmfdbSupplement.lean" source
  let records := cases.map fun c => Json.mkObj [
    ("label", toJson c.input.label), ("conductor", toJson c.input.conductor),
    ("ainvs", toJson [c.input.equation.a₁,c.input.equation.a₂,c.input.equation.a₃,c.input.equation.a₄,c.input.equation.a₆]),
    ("analytic_rank", toJson c.expectedRank),
    ("source_url", toJson ("https://www.lmfdb.org/EllipticCurve/Q/data/" ++ c.input.label))]
  let fixture := Json.mkObj [
    ("retrieved_date", toJson "2026-11-17"),
    ("source", toJson "https://github.com/JohnCremona/ecdata"),
    ("source_commit", toJson "25cec5ecfec8b9f016eb1631ac633194c2bed39f"),
    ("selection", toJson "First 1000 source rows excluding all 100 baseline labels; source order retained"),
    ("field", toJson "analytic_rank (column 30), separate from rank (column 28)"),
    ("cases", toJson records)]
  IO.FS.writeFile "data/lmfdb-1000-additional.json" (fixture.pretty ++ "\n")
  IO.println "Imported 1000 additional reference curves; 1100 total, without duplicate baseline labels."
  return 0
