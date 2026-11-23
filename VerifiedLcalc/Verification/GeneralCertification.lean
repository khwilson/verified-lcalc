/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.RealizationIndependence
public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.Verification.CentralEvaluator
public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.Certificate.Witnesses.ArithmeticCompatibility

/-! Soundness results for explicit modular arithmetic compatibility. -/

@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- The existing proved/assumed semistable arithmetic route is one constructor
of the general interface, not a restriction on general modularity. -/
noncomputable def arithmeticCompatibility_of_semistable (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (hs : SemistableModel e) :
    ArithmeticCompatibility e (semistableLevel e) (semistableSign e) :=
  ⟨modularWitness e hn, (modularWitness e hn).semistableLevel_eq hs,
    (modularWitness e hn).semistableSign_eq hs⟩

/-- The central computation can be checked against any genuine realization.
This implication adds no custom axiom and imposes no semistability condition. -/
theorem certifyCentralWithRealization (r : CentralResult)
    (m : ModularRealization r.equation)
    (hN : m.level = r.conductor) (hw : m.rootNumber = r.rootNumber)
    (hp : CentralPayloadCorrect r)
    (hc : r.coefficients = (List.range r.termLimit).map
      (fun j => (WeierstrassCurve.baseChange r.equation ℚ).LFunction (j + 1)))
    (hz : r.box.excludesZero = true) : analyticOrderAt m.formL (1 : ℂ) = 0 :=
  m.analyticOrder_zero_of_centralCoefficients r hp rfl hN.symm hw.symm hc hz

/-- A certificate obtained from general arithmetic compatibility proves rank
for the canonical continued curve L-function as well. Its witness need not be
the particular one selected by Classical.choice in modularWitness. -/
theorem certifyGeneralMinimalCentral (r : CentralResult)
    (hn : r.equation.Δ ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((WeierstrassCurve.baseChange r.equation
          ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ)))
    (ha : ArithmeticCompatibility r.equation r.conductor r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  rw [(modularWitness r.equation hn).analyticOrder_eq ha.realization]
  apply certifyCentralWithRealization r ha.realization ha.conductor_eq ha.rootNumber_eq hp
  · rw [hp.2.2.1]
    exact minimal_prefix r.equation hn hmin r.termLimit
  · exact hz

/-- General modularity supplies a realization for every nonsingular equation;
this theorem intentionally has no SemistableModel argument. -/
theorem general_modularity (e : (WeierstrassCurve ℤ)) (hn : e.Δ ≠ 0) :
    Nonempty (ModularRealization e) := ⟨modularWitness e hn⟩

end VerifiedLcalc.Certification

namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- A verified negative sign in any genuine general realization forces the
canonical continued curve L-function to vanish exactly at the center. -/
theorem central_zero_with_general_compatibility (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (N : Nat) (ha : ArithmeticCompatibility e N (-1)) :
    (modularWitness e hn).formL 1 = 0 := by
  rw [(modularWitness e hn).formL_eq ha.realization]
  exact ha.realization.central_zero_of_negative_sign ha.rootNumber_eq

/-- Exact rank lower bound from general conductor/sign evidence, without a
semistable restriction and without claiming that the first derivative is nonzero. -/
theorem certifyGeneralNegativeLowerBound (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (N : Nat) (ha : ArithmeticCompatibility e N (-1)) :
    1 ≤ analyticOrderAt (modularWitness e hn).formL (1 : ℂ) := by
  have hz := central_zero_with_general_compatibility e hn N ha
  have hne : analyticOrderAt (modularWitness e hn).formL (1 : ℂ) ≠ 0 :=
    ((modularWitness e hn).formL_differentiable.analyticAt 1).analyticOrderAt_ne_zero.mpr hz
  exact Order.one_le_iff_ne_zero.mpr hne

end VerifiedLcalc.Certification
