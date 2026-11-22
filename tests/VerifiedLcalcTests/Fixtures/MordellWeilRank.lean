/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.WorkedExamples.X3SubXAddOne.Rank
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-! # Checked Mordell–Weil rank of `y² = x³ - x + 1` -/

@[expose] public section

open VerifiedLcalc EllipticCurve TauCeti.WorkedExamples

namespace MordellWeilRankExample

/-- The rank proof is TauCeti's worked two-descent for this exact equation. -/
def exactBounds : AlgebraicRankBounds (curveX3SubXAddOne.baseChange ℚ) :=
  .ofRankEq 1 <| by
    rw [← Module.finrank_eq_rank, finrank_point_curveX3SubXAddOne]

/-- The singleton interval is supplied as a proof attachment for the integral equation. -/
def exactProofs : IntegralCurveProofs curveX3SubXAddOne where
  algebraicRank := some exactBounds

certify_ec Exact from_json_string
  r#"{"ainvs":[0,0,0,-1,1],"rank":1,"rank_bounds":[1,1],"gens":[[1,1,1]],"ngens":1}"#
  with_proofs exactProofs

certify_ec Partial from
  { equation := curveX3SubXAddOne, algebraicRank := some 1, algebraicRankBounds := some (0, 2) }
  with_proofs
    { algebraicRank := some (exactBounds.weaken 0 2 (by decide) (by decide)) }

certify_ec FromPointAndUpper from
  { equation := curveX3SubXAddOne, integralCoordinates := some [(3, -5)],
    infiniteOrderPoints := some [0], algebraicRank := some 1 }
  with_proofs
    { algebraicRank := some (exactBounds.weaken 0 1 (by decide) (by decide)) }

end MordellWeilRankExample
