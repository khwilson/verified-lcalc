import Mathlib.Tactic.Linter.TextBased

/-!
# Run Mathlib's text linters on explicit source paths
-/

open Lean Mathlib.Linter.TextBased

/-- Lint the files named on the command line without editing them. -/
def main (files : List String) : IO UInt32 := do
  let modules := files.toArray.map fun file =>
    ((System.FilePath.mk file).withExtension "").components.foldl Name.str Name.anonymous
  let opts : Lean.Linter.LinterOptions := ⟨{}, {}⟩
  let errors ← lintModules opts #[] modules .github false
  let names ← modulesOSForbidden opts modules
  return if errors == 0 && names == 0 then 0 else 1
