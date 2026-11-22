import VerifiedLcalc.Certificate.Witnesses
import Lean

/-! Check the public witness import and the source of each witness structure. -/

open Lean Elab Command

private def isStructureCommand (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Parser.Command.declaration &&
    cmd[1].isOfKind ``Parser.Command.«structure» &&
    cmd[1][0].isOfKind ``Parser.Command.structureTk

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let root := `VerifiedLcalc.Certificate.Witnesses
  for optIn in [`VerifiedLcalc.Assumptions.ellipticModularity,
      `VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank] do
    if env.contains optIn then throwError "ordinary witnesses imported the axiom {optIn}"
  -- Re-exporting the legacy declarations would leave their source in the old modules.
  for decl in [``VerifiedLcalc.EllipticWitness, ``VerifiedLcalc.DiscriminantWitness,
      ``VerifiedLcalc.EllipticCertificate, ``VerifiedLcalc.ArithmeticFacts,
      ``VerifiedLcalc.AnalyticFacts, ``VerifiedLcalc.EllipticCurve.AlgebraicRankBounds] do
    let some idx := env.getModuleIdxFor? decl | throwError "missing witness {decl}"
    let mod := modules[idx.toNat]!
    unless root.isPrefixOf mod do
      throwError "{decl} is defined in {mod}; its structure belongs in {root}"
  let dir : System.FilePath := "VerifiedLcalc/Certificate/Witnesses"
  for path in ← dir.walkDir do
    if path.extension != some "lean" then continue
    let mod := (path.withExtension "").components.foldl Name.str Name.anonymous
    let optIn := [root ++ `AssumedEvidence, root ++ `CurvePrecision].contains mod
    if !optIn && !modules.contains mod then
      throwError "the witness umbrella must import {mod}"
    let source ← IO.FS.readFile path
    let tree ← Parser.testParseModule env path.toString source
    let mut structures := 0
    for cmd in tree[1].getArgs do
      if isStructureCommand cmd then
        let derivingClause := cmd[1].getArgs.back!
        unless derivingClause[0].getArgs.isEmpty do
          throwError "{path}: derive instances in a companion module"
        structures := structures + 1
      else if !([``Parser.Command.moduleDoc, ``Parser.Command.«namespace»,
          ``Parser.Command.«section», ``Parser.Command.«end», ``Parser.Command.«open»,
          ``Parser.Command.«variable», ``Parser.Command.«universe», ``Parser.Command.eoi]
          : List Name).contains cmd.getKind then
        let line := source.toFileMap.toPosition (cmd.getPos?.getD 0)
        throwError "{path}:{line.line}: only structure declarations belong in witness modules"
    if structures == 0 then throwError "{path} declares no witness structures"
