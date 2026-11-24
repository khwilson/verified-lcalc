import VerifiedLcalc.Certificate.Witnesses
import Lean

/-! Check the public witness import and the source of each witness structure. -/

open Lean Elab Command

private def isStructureCommand (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Parser.Command.declaration &&
    cmd[1].isOfKind ``Parser.Command.«structure» &&
    cmd[1][0].isOfKind ``Parser.Command.structureTk

private def hasDoc (modifiers : Syntax) : Bool :=
  modifiers[0][0].isOfKind ``Parser.Command.docComment

private partial def forbiddenFieldTerm (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Term.«match» || stx.isOfKind ``Parser.Term.byTactic ||
      stx.isOfKind ``Parser.Term.binderTactic || stx[0].getAtomVal == "if" then
    some stx
  else
    stx.getArgs.findSome? forbiddenFieldTerm

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let root := `VerifiedLcalc.Certificate.Witnesses
  for mod in modules do
    if (`VerifiedLcalc.Verification).isPrefixOf mod || (`VerifiedLcalc.Tactic).isPrefixOf mod then
      throwError "ordinary witness structures imported a checker or command module: {mod}"
  -- The fields use the realization, reduction invariants and series formula themselves.
  -- Their proof companions used to enter through public imports of the checked records.
  for companion in [`VerifiedLcalc.EllipticCurve.Modularity.Realization,
      `VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealization,
      `VerifiedLcalc.EllipticCurve.Tate.Kodaira, `VerifiedLcalc.EllipticCurve.Tate.Tamagawa,
      `VerifiedLcalc.EllipticCurve.CentralFinite, `VerifiedLcalc.EllipticCurve.CentralTail,
      `VerifiedLcalc.NumericalRankSeparation] do
    if modules.contains companion then
      throwError "ordinary witness structures imported proof companion {companion}"
  for optIn in [`VerifiedLcalc.Assumptions.ellipticModularity,
      `VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank] do
    if env.contains optIn then throwError "ordinary witnesses imported the axiom {optIn}"
  for name in [``VerifiedLcalc.EllipticWitness.mk, ``VerifiedLcalc.EllipticCertificate.mk,
      ``VerifiedLcalc.IntegralCurveProofs.mk] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in ordinary aggregate {name}: {axiomName}"
  -- Re-exporting the legacy declarations would leave their source in the old modules.
  for decl in [``VerifiedLcalc.EllipticWitness, ``VerifiedLcalc.DiscriminantWitness,
      ``VerifiedLcalc.EllipticCertificate, ``VerifiedLcalc.ArithmeticFacts,
      ``VerifiedLcalc.AnalyticFacts, ``VerifiedLcalc.EllipticCurve.AlgebraicRankBounds] do
    let some idx := env.getModuleIdxFor? decl | throwError "missing witness {decl}"
    let mod := modules[idx.toNat]!
    unless root.isPrefixOf mod do
      throwError "{decl} is defined in {mod}; its structure belongs in {root}"
  -- Downstream readers can find each family in its mathematical subject module.
  for (decl, subject) in [(``VerifiedLcalc.LocalTamagawaFact, `FinitePrimes),
      (``VerifiedLcalc.NonmaxPrimeSupportFact, `FinitePrimes),
      (``VerifiedLcalc.FiniteGaloisImageFact, `FinitePrimes),
      (``VerifiedLcalc.ModPrimeImageFact, `FinitePrimes),
      (``VerifiedLcalc.ModPrimeImageCoverage, `FinitePrimes),
      (``VerifiedLcalc.ModPrimeImageListFact, `FinitePrimes),
      (``VerifiedLcalc.AdelicImageFact, `FinitePrimes),
      (``VerifiedLcalc.PadicImageLabelFact, `FinitePrimes),
      (``VerifiedLcalc.PadicImageListFact, `FinitePrimes),
      (``VerifiedLcalc.ModulusImageLabelFact, `FinitePrimes),
      (``VerifiedLcalc.ModulusImageListFact, `FinitePrimes),
      (``VerifiedLcalc.AdelicGenusFact, `FinitePrimes),
      (``VerifiedLcalc.AdelicImageCertificate, `FinitePrimes),
      (``VerifiedLcalc.ConditionalAnalyticRank, `Analytic),
      (``VerifiedLcalc.TorsionWitness, `Algebraic),
      (``VerifiedLcalc.PeriodGeometryFacts, `Algebraic),
      (``VerifiedLcalc.FaltingsRatioFact, `Algebraic),
      (``VerifiedLcalc.FaltingsIndexFact, `Algebraic),
      (``VerifiedLcalc.IntrinsicTorsionFact, `Algebraic),
      (``VerifiedLcalc.DiscriminantWitness, `Invariants)] do
    let some idx := env.getModuleIdxFor? decl | throwError "missing witness {decl}"
    unless modules[idx.toNat]! == (root ++ subject) do
      throwError "{decl} belongs in {root ++ subject}"
  let dir : System.FilePath := "VerifiedLcalc/Certificate/Witnesses"
  for path in ← dir.walkDir do
    if path.extension != some "lean" then continue
    let mod := (path.withExtension "").components.foldl Name.str Name.anonymous
    let optIn := mod == (root ++ `Assumptions)
    if !optIn && !modules.contains mod then
      throwError "the witness umbrella must import {mod}"
    let source ← IO.FS.readFile path
    let tree ← Parser.testParseModule env path.toString source
    let mut structures := 0
    for cmd in tree[1].getArgs do
      if isStructureCommand cmd then
        let declaration := cmd[1]
        let name := declaration[1][0].getId
        unless hasDoc cmd[0] do
          throwError "{path}: missing documentation for {name}"
        -- The optional structure body contains its opener, constructor and field group.
        let fields := declaration[4][2][0].getArgs
        for field in fields do
          unless hasDoc field[0] do
            let line := source.toFileMap.toPosition (field.getPos?.getD 0)
            throwError "{path}:{line.line}: missing documentation for a field of {name}"
          if let some term := forbiddenFieldTerm field then
            let line := source.toFileMap.toPosition (term.getPos?.getD 0)
            throwError "{path}:{line.line}: move the computation or proof body to a companion"
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
