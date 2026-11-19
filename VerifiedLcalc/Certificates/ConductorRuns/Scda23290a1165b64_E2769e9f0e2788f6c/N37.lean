module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1, a6 := 0 }
def label : String := "37.a1"
def inputConductor : Nat := 37
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.nonsingular
def minimality : MinimalityWitness := { primes := [37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 37 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1, a6 := 0 },   conductor := 37,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   finite := ((67275646462285 : Rat)/2251799813685248, (916571988775781 : Rat)/2251799813685248),   tail := (3032403881083705372597559290790557861328125 : Rat)/758024334991772882370407397346757837370425344,   box := { reLo := (10283712920796241229017211494935974495928793484615 : Rat)/397423062544166620952216153540136973039265562755072,            reHi := (163356829145525307802728876771554607105780530671759 : Rat)/397423062544166620952216153540136973039265562755072,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 12 = (List.range 12).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 12

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1873, a6 := -31833 }
def label : String := "37.b1"
def inputConductor : Nat := 37
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.nonsingular
def minimality : MinimalityWitness := { primes := [37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 37 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1873, a6 := -31833 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 4 = (List.range 4).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 4

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -23, a6 := -50 }
def label : String := "37.b2"
def inputConductor : Nat := 37
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.nonsingular
def minimality : MinimalityWitness := { primes := [37, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 37 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -23, a6 := -50 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 4 = (List.range 4).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 4

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -3, a6 := 1 }
def label : String := "37.b3"
def inputConductor : Nat := 37
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.nonsingular
def minimality : MinimalityWitness := { primes := [37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 37 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -3, a6 := 1 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 4 = (List.range 4).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 4

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N37.C37_b3
