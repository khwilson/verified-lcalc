/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealization

/-!
# Opt-in forward analytic-to-algebraic rank assumption

This file isolates the user-authorized rank-zero and rank-one implications.
TauCeti already defines the full conjectural `WeierstrassCurve.BirchSwinnertonDyer`
structure and derives `analyticOrderAt_eq_finrank` from it. This assumption
records only its forward rank comparison for orders zero and one, without
assuming the leading-coefficient clause or either converse. It is not imported
by the default library or certificate command.
-/

@[expose] public section

namespace VerifiedLcalc.Assumptions

/-- TEMPORARY USER-AUTHORIZED ASSUMPTION (2026-11-22): for a nonsingular
integral Weierstrass equation, analytic order zero or one for the L-function of
an explicit arithmetic modular realization implies the same rational
Mordell--Weil rank. This assumes only the forward implication in ranks zero and
one; it does not assume either converse or general BSD. -/
axiom analyticOrder_le_one_implies_finrank
    (curve : WeierstrassCurve ℤ)
    (m : Modularity.ArithmeticModularRealization curve)
    (r : ℕ) (hr : r ≤ 1)
    (horder : analyticOrderAt m.formL (1 : ℂ) = (r : ℕ∞))
    [(curve.baseChange ℚ).IsElliptic] :
    curve.Δ ≠ 0 → Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = r

end VerifiedLcalc.Assumptions
