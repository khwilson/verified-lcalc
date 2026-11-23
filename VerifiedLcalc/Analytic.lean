/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Certificate.Witnesses.AnalyticRank
public import VerifiedLcalc.Certificate.Analytic.Enclosures
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Rat.Cast.Order

/-! # Analytic orders from exact derivative enclosures -/

@[expose] public section

namespace VerifiedLcalc

/-- Main semantic theorem: the executable search computes the actual analytic
order, assuming analyticity and proved enclosures of the true derivatives. -/
theorem scan_analyticOrderAt {f : ℂ → ℂ} {center : ℂ} {bs : List Box} {n : ℕ}
    (hf : AnalyticAt ℂ f center)
    (hencl : Encloses bs (fun k => iteratedDeriv k f center))
    (hscan : scan bs = some n) : analyticOrderAt f center = n := by
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mpr
  exact (scan_correct bs n hscan).sound _ hencl

/-- Historical executable projection, reconstructed from the finite witness. -/
theorem AnalyticCertificate.computed {f : ℂ → ℂ} {center : ℂ} {bs : List Box}
    (c : AnalyticCertificate f center bs) : scan bs = some c.rank :=
  Certificate.computed ⟨c.rank, c.sound⟩

/-- This function cannot be called for an L-function without a proof that the
boxes enclose its actual derivatives. Proof arguments erase at runtime. -/
def computeRank (f : ℂ → ℂ) (center : ℂ) (bs : List Box)
    (hf : AnalyticAt ℂ f center)
    (hencl : Encloses bs (fun k => iteratedDeriv k f center)) :
    Option (AnalyticCertificate f center bs) :=
  match h : scan bs with
  | none => none
  | some n => some ⟨n, scan_correct bs n h,
      scan_analyticOrderAt hf hencl h⟩

/-- A successful scan of derivative enclosures returns the analytic order at the center. -/
theorem computeRank_correct {f : ℂ → ℂ} {center : ℂ} {bs : List Box}
    {hf : AnalyticAt ℂ f center}
    {hencl : Encloses bs (fun k => iteratedDeriv k f center)}
    {c : AnalyticCertificate f center bs}
    (_h : computeRank f center bs hf hencl = some c) :
    scan bs = some c.rank ∧ analyticOrderAt f center = c.rank :=
  ⟨c.computed, c.correct⟩

end VerifiedLcalc
