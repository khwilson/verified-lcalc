module

public import VerifiedLcalc.Regression.ConditionalCore
public import VerifiedLcalc.Assumptions.Generated
public import VerifiedLcalc.Assumptions.GeneratedRankOne
public import VerifiedLcalc.Certificates.AssumedCurve11Central

@[expose] public section
namespace VerifiedLcalc.Assumptions
open Regression EllipticCurve

/-- Every returned cached rank is tied to the actual curve continuation by a
checked certificate. The reference rank is absent from both input and proof.
This opt-in theorem has the named modularity axiom as its only custom axiom. -/
theorem conditionalCertifiedBackend_sound (c : CurveInput) (n : Nat)
    (h : conditionalCertifiedBackend c = some n) :
    ∃ hn : discriminant c.equation ≠ 0,
      analyticOrderAt (modularWitness c.equation hn).formL (1 : ℂ) = n := by
  rcases (conditionalCertifiedBackend_correct c n).mp h with ⟨hkey,rfl⟩ | ⟨_,hkey,rfl⟩
  ·
    rcases hkey with ⟨he, _⟩ | hkey
    ·
      have he' : c.equation = Examples.curve11 := he
      have hn : discriminant c.equation ≠ 0 := by rw [he']; decide +kernel
      refine ⟨hn, ?_⟩
      have ht : ∀ e : Artifacts.CurveEquation, e = Examples.curve11 →
          ∀ hne : discriminant e ≠ 0,
            analyticOrderAt (modularWitness e hne).formL (1 : ℂ) = 0 := by
        intro e he hne
        subst e
        exact Certificates.AssumedCurve11Central.analytic_rank_zero
      exact ht c.equation he' hn
    · exact generatedCertificateKeys_sound c.equation c.conductor hkey
  · exact generatedRankOneKeys_sound c.equation c.conductor hkey

end VerifiedLcalc.Assumptions
