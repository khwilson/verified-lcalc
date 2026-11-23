/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.NumericalData
public import VerifiedLcalc.Certificate.Numerical.Intervals
public import VerifiedLcalc.Certificate.Numerical.Precision
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Compatibility imports and instances for numerical output records. -/

@[expose] public section

deriving instance Repr for VerifiedLcalc.EllipticCurve.CentralResult
deriving instance DecidableEq for VerifiedLcalc.EllipticCurve.CentralResult
deriving instance Repr for VerifiedLcalc.EllipticCurve.DerivativeResult
deriving instance DecidableEq for VerifiedLcalc.EllipticCurve.DerivativeResult
