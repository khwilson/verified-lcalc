/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData

/-! # Compatibility path for finite reduction transcripts -/

public section

export VerifiedLcalc.EllipticCurve (
  instReprMinimalityWitness instDecidableEqMinimalityWitness
  instReprTateWitness instDecidableEqTateWitness
  instReprWildData instDecidableEqWildData
)
