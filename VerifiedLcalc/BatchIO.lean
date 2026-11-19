import Lean.Data.Json
import VerifiedLcalc.LmfdbSupplement

open Lean

structure BatchRow where
  label : String
  status : String
  moduleName : String
  conductor : String
  equation : String
  bits : String
  terms : String
  sourceHash : String := ""
  log : String := ""

/-- Process/file orchestration only: mathematical computation and all
certificate assertions are produced and checked by the Lean proof modules. -/
def runLogged (args : Array String) (path : System.FilePath) : IO UInt32 := do
  let out ← IO.Process.output { cmd := args[0]!, args := args.extract 1 args.size }
  IO.FS.writeFile path (out.stdout ++ out.stderr)
  return out.exitCode

def rowJson (r : BatchRow) : Json := Json.mkObj [
  ("label", toJson r.label), ("status", toJson r.status), ("module", toJson r.moduleName),
  ("conductor", toJson r.conductor), ("equation", toJson r.equation),
  ("bits", toJson r.bits), ("terms", toJson r.terms),
  ("source_sha256", toJson r.sourceHash), ("log", toJson r.log)]

