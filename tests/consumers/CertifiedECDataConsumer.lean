import CertifiedCurves.Data

-- Import and use the compiled arithmetic theorems without reading witness JSON.
theorem imported_ap_bad_prime : (Data37.curve.baseChange ℚ).LFunction 37 = -1 :=
  Data37.ap_correct 37 (-1) (by decide +kernel)

theorem imported_integral_point :
    Data37.point ⟨8, by decide⟩ ∈ Data37.curve.integralPoints :=
  Data37.point_integral _

#print axioms imported_ap_bad_prime
#print axioms imported_integral_point
