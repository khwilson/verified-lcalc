import VerifiedLcalc.Numerics.RealInterval

open VerifiedLcalc.Numerics

-- Exhaustively compare with the four-corner formula on ordered integer intervals
-- across every sign pattern, including zero and singleton endpoints.
private def endpoints : List Rat := [-2, -1, 0, 1, 2]

example : (endpoints.all fun a => endpoints.all fun b =>
    endpoints.all fun c => endpoints.all fun d =>
      if a ≤ b ∧ c ≤ d then
        decide (intervalMul (a, b) (c, d) =
          (min (min (a*c) (a*d)) (min (b*c) (b*d)),
           max (max (a*c) (a*d)) (max (b*c) (b*d))))
      else true) = true := by decide +kernel

-- The reusable real enclosure theorem covers every rational input, including
-- intervals whose endpoints are not integral.
example (i j : RealInterval) (x y : ℝ)
    (hx : i.Contains x) (hy : j.Contains y) :
    (intervalMul i j).Contains (x*y) := intervalMul_sound i j x y hx hy
