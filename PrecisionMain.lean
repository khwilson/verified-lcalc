import VerifiedLcalc.NumericalRank

open VerifiedLcalc

/-- Report the global policy without importing the analytic proof library. -/
def main : IO Unit := do
  IO.println s!"precision_bits = {globalPrecision.precisionBits}"
  IO.println "cutoff_rule = pari-half-bits-v1: 2^(1-floor(bits/2))"
  IO.println s!"cutoff = {globalPrecision.cutoff}"
  IO.println "comparison = each real and imaginary derivative coordinate"
  IO.println "claim = numerical lower bound; exact analytic vanishing requires additional proof"
