module
public import VerifiedLcalc.Tactic.CertifyEC

/-! # Direct examples of the shared elliptic certifier -/

@[expose] public section

open VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Partial input: verify only the supplied coefficients and integer points.
-- Omitted Option fields default to none; no analytic-rank theorem is requested.
certify_ec DirectPoints from
  { equation := ⟨0, 0, 1, -1, 0⟩
    primeCoefficients := some [(2, -2), (37, -1)]
    integralCoordinates := some [(0, 0), (6, 14)]
    infiniteOrderPoints := some [1]
    independentPoints := some [1] }
  with_independence (by
    apply LinearIndependent.of_subsingleton' (0 : Fin 1)
    intro a ha
    have hp : a • DirectPoints.infiniteOrder.point0.point = 0 := by
      simpa [DirectPoints.algebraic.points, DirectPoints.algebraic.indices,
        DirectPoints.infiniteOrder.point0.point, DirectPoints.infiniteOrder.point0.index,
        DirectPoints.infinite_order_indices] using ha
    by_contra hn
    exact DirectPoints.infiniteOrder.point0.infinite_order
      (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, hp⟩))

example : (DirectPoints.curve.baseChange ℚ).LFunction 2 = -2 :=
  DirectPoints.ap_correct 2 (-2) (by decide +kernel)

example : DirectPoints.point ⟨0, by decide⟩ ∈ DirectPoints.curve.integralPoints :=
  DirectPoints.point_integral _

-- The same command proves infinite order of (6,14) and algebraic rank ≥ 1.
example : ¬ IsOfFinAddOrder (DirectPoints.point ⟨1, by decide⟩) :=
  DirectPoints.infiniteOrder.point0.infinite_order

example : 1 ≤ Module.finrank ℤ (DirectPoints.curve.baseChange ℚ).toAffine.Point :=
  DirectPoints.algebraic_rank_lower_bound

-- Supplied data only. No JSON file, witness search, or numerical producer.
certify_ec DirectCurve from EllipticWitness.central
  { equation := ⟨0, -1, 1, -10, -20⟩
    conductor := 11
    rootNumber := 1
    policy := ⟨53⟩
    termLimit := 1
    coefficients := [1]
    alphaLo := ((5397215081808807583435051761664 : Rat) / 2848959001535859775543212890625)
    alphaHi := ((337325942613050473965764476928 : Rat) / 178059937595991230010986328125)
    geometricUpper := ((169336229459221 : Rat) / 1125899906842624)
    tail := ((28674758607465946046101926841 : Rat) / 104834424879811077321286221824)
    box := ⟨
      (366028917649787835048376743221 : Rat) / 13418806384615817897124636393472,
      (963345890145134125303004031503 : Rat) / 1677350798076977237140579549184,
      (0 : Rat) / 1, (0 : Rat) / 1⟩ }
  ⟨[11,11,11,11,11]⟩
  ⟨none, none⟩

-- A numerical component can be supplied without the local arithmetic witnesses:
-- it is checked, but it cannot establish an analytic rank alone.
certify_ec DirectNumerics from
  { equation := DirectCurve.curve
    centralResult := some DirectCurve.result }

example : DirectNumerics.result.equation = DirectNumerics.curve :=
  DirectNumerics.result_curve_eq
