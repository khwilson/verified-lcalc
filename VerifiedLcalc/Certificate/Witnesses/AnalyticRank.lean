/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Scan
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic

/-! Typed analytic rank certificate records. -/

@[expose] public section

namespace VerifiedLcalc

/-- An analytic order is certified by a finite witness on these exact boxes. -/
structure AnalyticCertificate (f : ℂ → ℂ) (center : ℂ) (bs : List Box) where
  /-- Claimed order of vanishing. -/
  rank : ℕ
  /-- The same boxes witness the first nonzero derivative at this rank. -/
  sound : Witness bs rank
  /-- The function has this analytic order at the specified center. -/
  correct : analyticOrderAt f center = rank

end VerifiedLcalc
