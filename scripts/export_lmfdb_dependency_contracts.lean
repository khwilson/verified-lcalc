/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.Certificate.FieldCatalogue

/-! Export the exact EC/Q catalogue routes and Lean declaration locations. -/

open Lean Elab Command VerifiedLcalc.FieldCatalogue

private def declarationJson (decl : Name) : CommandElabM Json := do
  let moduleName ← findModuleOf? decl
  let ranges ← findDeclarationRanges? decl
  pure <| Json.mkObj [
    ("name", toJson decl.toString),
    ("module", toJson (moduleName.map Name.toString)),
    ("line", toJson (ranges.map (·.selectionRange.pos.line)))
  ]

private def references (decls : List Name) : CommandElabM Json := do
  return toJson (← decls.mapM declarationJson)

private def pathJson (path : Path) : CommandElabM Json := do
  pure <| Json.mkObj [
    ("json", toJson path.json),
    ("claim", ← references path.claim),
    ("check", toJson (path.check.map Name.toString)),
    ("verify", ← references path.verify.toList),
    ("output", ← references path.output),
    ("prerequisites", ← references path.prerequisites),
    ("scope", toJson path.scope),
    ("fact", toJson (path.fact.map Name.toString))
  ]

run_cmd do
  let docs ← columns.mapM fun column => do
    pure <| Json.mkObj [
      ("table", toJson column.table),
      ("field", toJson column.field),
      ("paths", toJson (← column.paths.mapM pathJson))
    ]
  IO.println (toJson docs).compress
