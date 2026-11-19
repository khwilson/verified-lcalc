module

public import VerifiedLcalc.Regression
public import VerifiedLcalc.Regression.Generated
public import VerifiedLcalc.Regression.GeneratedRankOne

@[expose] public section
namespace VerifiedLcalc.Regression

/-- The exact equation certified by the current conditional certificate cache.
The cache key uses arithmetic input, not an LMFDB label or expected rank. -/
def certifiedEquation11 : Artifacts.CurveEquation := ⟨0, -1, 1, -10, -20⟩

/-- A runtime certificate cache with a generated registry. Its analytic interpretation is proved
separately in Assumptions/Regression.lean and depends on ellipticModularity. -/
def conditionalCertifiedBackend (c : CurveInput) : Option Nat :=
  if (c.equation = certifiedEquation11 ∧ c.conductor = 11) ∨
      (c.equation, c.conductor) ∈ generatedCertificateKeys then some 0
  else if (c.equation,c.conductor) ∈ generatedRankOneKeys then some 1 else none

theorem conditionalCertifiedBackend_correct (c : CurveInput) (n : Nat) :
    conditionalCertifiedBackend c = some n ↔
      (((c.equation = certifiedEquation11 ∧ c.conductor = 11) ∨
        (c.equation,c.conductor) ∈ generatedCertificateKeys) ∧ n = 0) ∨
      (¬ ((c.equation = certifiedEquation11 ∧ c.conductor = 11) ∨
        (c.equation,c.conductor) ∈ generatedCertificateKeys) ∧
        (c.equation,c.conductor) ∈ generatedRankOneKeys ∧ n = 1) := by
  unfold conditionalCertifiedBackend
  split
  · simp_all [eq_comm]
  · split <;> simp_all [eq_comm]

end VerifiedLcalc.Regression
