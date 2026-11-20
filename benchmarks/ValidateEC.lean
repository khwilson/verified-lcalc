module
public import VerifiedLcalc.Tactic.CertifyEC
public meta import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/-! Benchmark harness only. Each invocation runs the real `certify_ec` command.
Failures are recorded separately and never represented by admitted theorems. -/
public meta section
namespace ECBenchmark
open Lean Elab Command

syntax (name := benchmarkEC) "benchmark_ec " ident str str : command

@[command_elab benchmarkEC] def elabBenchmark : CommandElab := fun stx => do
  let `(benchmark_ec $name:ident $label:str $file:str) := stx | throwUnsupportedSyntax
  let saved ← get
  let start ← IO.monoNanosNow
  let result ← try
    elabCommand (← `(certify_ec $name from_json $file))
    if (← get).messages.hasErrors then
      let mut details : List String := []
      for message in (← get).messages.reportedPlusUnreported.toList do
        if message.severity == .error then
          details := details ++ [← message.toString]
      throwError "Certificate command logged an error: {String.intercalate "\n" details}"
    pure ("checked", "")
  catch error =>
    let message ← error.toMessageData.toString
    set saved
    pure ("rejected", message.take 2000 |>.toString)
  let elapsed := (← IO.monoNanosNow) - start
  let event := Json.mkObj [
    ("label", .str label.getString), ("status", .str result.1),
    ("validation_ns", toJson elapsed), ("error", .str result.2)]
  let stdout ← IO.getStdout
  stdout.putStrLn ("EC_BENCH " ++ event.compress)
  stdout.flush

end ECBenchmark
end

@[expose] public section
