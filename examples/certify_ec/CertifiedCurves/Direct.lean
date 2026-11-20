module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Partial input: verify only the supplied coefficients and integer points.
-- Omitted Option fields default to none; no analytic-rank theorem is requested.
certify_ec DirectPoints from
  { equation := ⟨0, 0, 1, -1, 0⟩
    primeCoefficients := some [(2, -2), (37, -1)]
    integralCoordinates := some [(0, 0), (6, 14)] }

example : (DirectPoints.curve.baseChange ℚ).LFunction 2 = -2 :=
  DirectPoints.ap_correct 2 (-2) (by decide +kernel)

example : DirectPoints.point ⟨0, by decide⟩ ∈ DirectPoints.curve.integralPoints :=
  DirectPoints.point_integral _

-- The second supplied point (6,14) passes an exact Nagell–Lutz obstruction.
-- This proves infinite order and algebraic rank ≥ 1, without modularity.
certify_ec_infinite_order DirectOrder for DirectPoints at 1

example : ¬ IsOfFinAddOrder (DirectPoints.point ⟨1, by decide⟩) :=
  DirectOrder.infinite_order

-- Select a family from the supplied points and provide its independence proof.
-- The same command accepts any number of indices, with the corresponding proof.
certify_ec_rank DirectRank for DirectPoints from [1] using (by
  apply LinearIndependent.of_subsingleton' (0 : Fin 1)
  intro a ha
  have hp : a • DirectOrder.point = 0 := by
    simpa [DirectRank.points, DirectRank.indices, DirectOrder.point, DirectOrder.index] using ha
  by_contra hn
  exact DirectOrder.infinite_order
    (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, hp⟩))

example : (1 : Cardinal) ≤ Module.rank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectRank.algebraic_rank_lower_bound

-- Supplied data only. No JSON file, witness search, or numerical producer.
certify_ec DirectCurve from EllipticWitness.central
  { equation := ⟨0,-1,1,-10,-20⟩
    conductor := 11
    rootNumber := 1
    policy := ⟨53⟩
    termLimit := 1
    coefficients := [1]
    alphaLo := ((5397215081808807583435051761664 : Rat) / 2848959001535859775543212890625)
    alphaHi := ((337325942613050473965764476928 : Rat) / 178059937595991230010986328125)
    geometricUpper := ((169336229459221 : Rat) / 1125899906842624)
    tail := ((28674758607465946046101926841 : Rat) / 104834424879811077321286221824)
    box := ⟨((366028917649787835048376743221 : Rat) / 13418806384615817897124636393472),((963345890145134125303004031503 : Rat) / 1677350798076977237140579549184),((0 : Rat) / 1),((0 : Rat) / 1)⟩ }
  ⟨[11,11,11,11,11]⟩
  ⟨none, none⟩

-- A numerical component can be supplied without the local arithmetic witnesses:
-- it is checked, but it cannot establish an analytic rank alone.
certify_ec DirectNumerics from
  { equation := DirectCurve.curve
    centralResult := some DirectCurve.result }

example : DirectNumerics.result.equation = DirectNumerics.curve :=
  DirectNumerics.result_curve_eq
