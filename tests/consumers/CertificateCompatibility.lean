/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalc.Analytic
import VerifiedLcalc.Certificate
import VerifiedLcalc.NumericalRank

/-! Compatibility projections remain available from the established imports. -/

open VerifiedLcalc

variable {bs : List Box}

example (c : Certificate bs) : scan bs = some c.rank := c.computed

variable {f : ℂ → ℂ} {center : ℂ}

example (c : AnalyticCertificate f center bs) : scan bs = some c.rank :=
  c.computed

variable {request : Artifacts.Request} (c : Artifacts.Checked request)

example : Artifacts.check request c.artifact = true := c.accepted

variable {numericalRequest : NumericalRanks.Request}
  (n : NumericalRanks.Checked numericalRequest)

example : NumericalRanks.check numericalRequest n.artifact = true := n.accepted
