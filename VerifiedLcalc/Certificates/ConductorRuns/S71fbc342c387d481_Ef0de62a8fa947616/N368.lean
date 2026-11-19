module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -55, a6 := 157 }
def label : String := "368.a1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -55, a6 := 157 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -3, 0, 0, 0, 2, 0, 6, 0, 0, 0, -5, 0, 0, 0, -6, 0, -6, 0, -6, 0, -1, 0, -5, 0, -9, 0, 9, 0, -3,                    0, 0, 0, 0, 0, -8, 0, 15, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((451522322902309 : Rat)/562949953421312, (14374540975271955 : Rat)/4503599627370496),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (24941872575120019789596990877169051737109259184189 : Rat)/95341726464137424901463032199463159929280137265152,            reHi := (2846712533428629485025275115204675052179322979082555 : Rat)/762733811713099399211704257595705279434241098121216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -18, a6 := 43 }
def label : String := "368.b1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -18, a6 := 43 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0, 0, -6, 0, -2, 0, 2, 0, 1, 0, -5, 0, 5, 0, -3, 0, -5,                    0, 0, 0, 0, 0, 8, 0, 1, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((11662081268986105 : Rat)/9007199254740992, (31724745086864497 : Rat)/9007199254740992),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (1150647032906380353666826423519053112456180163374705 : Rat)/1525467623426198798423408515191410558868482196242432,            reHi := (6197386136697102856000472487072679477255884556522537 : Rat)/1525467623426198798423408515191410558868482196242432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := -1 }
def label : String := "368.b2"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := -1 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0, 0, 0, -6, 0, -2, 0, 2, 0, 1, 0, -5, 0, 5, 0, -3, 0, -5,                    0, 0, 0, 0, 0, 8, 0, 1, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((11662081268986105 : Rat)/9007199254740992, (31724745086864497 : Rat)/9007199254740992),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (1150647032906380353666826423519053112456180163374705 : Rat)/1525467623426198798423408515191410558868482196242432,            reHi := (6197386136697102856000472487072679477255884556522537 : Rat)/1525467623426198798423408515191410558868482196242432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -35, a6 := -62 }
def label : String := "368.c1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -35, a6 := -62 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 0, 0, -4, 0, -3, 0, -6, 0, -2, 0, 0, 0, 6, 0, 6, 0, 0, 0, -1, 0, -5, 0, 0, 0, -6, 0, 0,                    0, 0, 0, 0, 0, -8, 0, 0, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((12680174654199283 : Rat)/9007199254740992, (33980849563007585 : Rat)/9007199254740992),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (1323072273299459643446599539752466775796307231010843 : Rat)/1525467623426198798423408515191410558868482196242432,            reHi := (6579482084181743194764221014009334329208902868229785 : Rat)/1525467623426198798423408515191410558868482196242432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := -6 }
def label : String := "368.c2"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := -6 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 0, 0, -4, 0, -3, 0, -6, 0, -2, 0, 0, 0, 6, 0, 6, 0, 0, 0, -1, 0, -5, 0, 0, 0, -6, 0, 0,                    0, 0, 0, 0, 0, -8, 0, 0, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((12680174654199283 : Rat)/9007199254740992, (33980849563007585 : Rat)/9007199254740992),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (1323072273299459643446599539752466775796307231010843 : Rat)/1525467623426198798423408515191410558868482196242432,            reHi := (6579482084181743194764221014009334329208902868229785 : Rat)/1525467623426198798423408515191410558868482196242432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2723, a6 := 54690 }
def label : String := "368.d1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0, 0, 1, 1, 0, 0],              kodaira := -13 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -163, a6 := 930 }
def label : String := "368.d2"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -18 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := -1 }
def label : String := "368.e1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := -1 },   conductor := 368,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -4, 0, -2, 0, -2, 0, 4, 0, -5, 0, -4, 0, -2, 0, -6, 0, -2, 0, -1, 0, 11, 0, -5, 0, 1, 0,                    9, 0, 4, 0, 8, 0, -4, 0, -5, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   finite := ((13141854227504595 : Rat)/9007199254740992, (35662599403455787 : Rat)/9007199254740992),   tail := (49141280166925983137535329297733306884765625 : Rat)/90924955810677933598959953498328361443786752,   box := { reLo := (1401262754219905073227976642630735128408487419039995 : Rat)/1525467623426198798423408515191410558868482196242432,            reHi := (6864304797630162304059974770840067992058955559156627 : Rat)/1525467623426198798423408515191410558868482196242432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := -5 }
def label : String := "368.f1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := -5 },   conductor := 368,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, -2, 0, 4, 0, -2, 0, 2, 0, 7, 0, -2, 0, -4, 0, 6, 0, 4, 0, 1, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   geometricUpper := (3245739841673983 : Rat)/4503599627370496,   tail := (2369205314607257370911716719134002570894866665654533081782832789078969167735239204339164657601142499869406487972027613794645632009212237966121981465443984358215813056324436680684000896223295506549418675935527703595094041943111856293456533964662832159926422058531171225680227062464908327857230706269012838992215061636912855285888551018688067294225249491162429804706510740588773180290569899609375 : Rat)/1503962825535774953109494959359738581406540560919035062403922812039506038117157261983811250811401052114869877234465425510061894482698155710189094453020763743842158155845703848245979744664585803794544907509383301878936251109738070340775664219972677994596551165418569589609436465782466693637709983755560359471911933413677057101061027981776549894066586411943684306802574679464826025439175823589376,   box := { reLo := (4028768325295711058925974649162802424496728030376674489273738879462442009783099125665974958767168697341774784632844037821746201421566677372296119233691471514971162986708676953642303799773567671804132789214089679218374518766162514025575021924675195820594652715743730329423041403699414490863584621509971562344549430325659361515693238212021551070216706935640532612816433688685579027422564080070971997 : Rat)/53512501295388408606588940148978858465026119698060186555393977575177664342246572538645988115120460835299185101879514305073512267588883078324238169732931794769647829343145988624440205294910627484813702354091367264154430750735590280795138908610847855725739887016758124567893358889005947426323358932006593150370098502792043368712852436619591421780783211123368231320342409670037974811151314979133587456,            reHi := (37527425418125527439027408071658145204593957479798088042400052989618648503437359243836257098454120427345191681116154085978080386607132733417959656469170036581148869859338189446476221669453880756500572750380440534493035476818835858813909372399067296910449035368908773722036423056614574664710640942020584680892205992683492090907969975293093139081640148878458198557031320798649977309321425093469959081 : Rat)/11633152455519219262301943510647577927179591238708736207694342951125579204836211421444780025026187138108518500408590066320328753823670234418312645594115607558619093335466519266182653324980571192350804859585079840033571902333823974085899762741488664288204323264512635775628991062827379875287686724349259380515238804954792036676707051439041613430605045896384398113117915145660429306772024995463823360,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2369205314607257370911716719134002570894866665654533081782832789078969167735239204339164657601142499869406487972027613794645632009212237966121981465443984358215813056324436680684000896223295506549418675935527703595094041943111856293456533964662832159926422058531171225680227062464908327857230706269012838992215061636912855285888551018688067294225249491162429804706510740588773180290569899609375 : Rat)/3007925651071549906218989918719477162813081121838070124807845624079012076234314523967622501622802104229739754468930851020123788965396311420378188906041527487684316311691407696491959489329171607589089815018766603757872502219476140681551328439945355989193102330837139179218872931564933387275419967511120718943823866827354114202122055963553099788133172823887368613605149358929652050878351647178752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := -1 }
def label : String := "368.g1"
def inputConductor : Nat := 368
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 368 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := -1 },   conductor := 368,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 3, 0, -2, 0, 4, 0, 6, 0, -2, 0, -5, 0, -6, 0, 4, 0, 2, 0, 12, 0, -1, 0],   alphaLo := (337325942613050473964690735104 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/16478351639803193569183349609375,   geometricUpper := (3245739841673983 : Rat)/4503599627370496,   tail := (2369205314607257370911716719134002570894866665654533081782832789078969167735239204339164657601142499869406487972027613794645632009212237966121981465443984358215813056324436680684000896223295506549418675935527703595094041943111856293456533964662832159926422058531171225680227062464908327857230706269012838992215061636912855285888551018688067294225249491162429804706510740588773180290569899609375 : Rat)/1503962825535774953109494959359738581406540560919035062403922812039506038117157261983811250811401052114869877234465425510061894482698155710189094453020763743842158155845703848245979744664585803794544907509383301878936251109738070340775664219972677994596551165418569589609436465782466693637709983755560359471911933413677057101061027981776549894066586411943684306802574679464826025439175823589376,   box := { reLo := (7227021664099599078527849733008595101292093947573285759858870124325939923446898356786022276060232876945732004601801552664427096779447910890742232764390748404233674243101920997059994549219228415078461317870555717024019645081750281063996080303897778359130310918164144451719685565372881552477110179146274558334449167131934179588041423717715005253826626832494156237743945091942025577571450958173408343 : Rat)/11633152455519219262301943510647577927179591238708736207694342951125579204836211421444780025026187138108518500408590066320328753823670234418312645594115607558619093335466519266182653324980571192350804859585079840033571902333823974085899762741488664288204323264512635775628991062827379875287686724349259380515238804954792036676707051439041613430605045896384398113117915145660429306772024995463823360,            reHi := (10623246750154730920516444736859811642737515135252529169680952947597334634603496430158189967653378005593874833740776724247584522934387807618092643560704051176566823660208403999926423482347175795885104701949719192278057886545455634578050300165222225950826379583851532305550870419866214798319209823359234884989644768892959254501254869363545135130299844726600415262133760816677370554736366215683305009 : Rat)/2816447436599389926662575797314676761317164194634746660810209346061982333802451186244525690269497938699957110625237595003869066715204372543380956301733252356297254175955052032865273962890033025516510650215335119166022671091346856883954679400570939775038941421934638135152282046789786706648597838526662797387899921199581229932255391401031127462146484795966749016860126824738840779534279735743873024,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2369205314607257370911716719134002570894866665654533081782832789078969167735239204339164657601142499869406487972027613794645632009212237966121981465443984358215813056324436680684000896223295506549418675935527703595094041943111856293456533964662832159926422058531171225680227062464908327857230706269012838992215061636912855285888551018688067294225249491162429804706510740588773180290569899609375 : Rat)/3007925651071549906218989918719477162813081121838070124807845624079012076234314523967622501622802104229739754468930851020123788965396311420378188906041527487684316311691407696491959489329171607589089815018766603757872502219476140681551328439945355989193102330837139179218872931564933387275419967511120718943823866827354114202122055963553099788133172823887368613605149358929652050878351647178752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N368.C368_g1
