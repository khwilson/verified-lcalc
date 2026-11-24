/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.Certificate.Numerical.Intervals
public import VerifiedLcalc.Certificate.Numerical.Precision
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Compatibility imports for numerical output records. -/

public section

export VerifiedLcalc.EllipticCurve (
  instReprCentralResult instDecidableEqCentralResult
  instReprDerivativeResult instDecidableEqDerivativeResult
)
