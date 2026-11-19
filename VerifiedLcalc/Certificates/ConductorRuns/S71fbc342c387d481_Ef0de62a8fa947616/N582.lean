module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -15, a6 := -27 }
def label : String := "582.a1"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -15, a6 := -27 },   conductor := 582,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -1, -1, 1, 0, 1, -2, -1, 1, 0, 4, -1, -4, 2, 0, 1, -2, -1, 0, 0, 2, -4, -2, 1, -5, 4, -1, -2, 4,                    0, -4, -1, -4, 2, 0, 1, -8, 0, 4, 0, -2, -2, -4, 4, 0, 2, 0, -1, -3, 5, 2, -4, -6, 1, 0, 2, 0, -4, 0,                    0, -14, 4, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   finite := ((8400671598581349 : Rat)/4503599627370496, (34820286144334039 : Rat)/9007199254740992),   tail := (11205908843422256883653410754680633544921875 : Rat)/189532806340223278813513062192232992400736256,   box := { reLo := (358963370400049842156615231073655368956692367318839 : Rat)/198739551941005964805158272701282902239594420371456,            reHi := (1560086478546353005349786019503058611207791899038429 : Rat)/397479103882011929610316545402565804479188840742912,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 25, a6 := -99 }
def label : String := "582.a2"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 97, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 25, a6 := -99 },   conductor := 582,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -1, -1, 1, 0, 1, -2, -1, 1, 0, 4, -1, -4, 2, 0, 1, -2, -1, 0, 0, 2, -4, -2, 1, -5, 4, -1, -2, 4,                    0, -4, -1, -4, 2, 0, 1, -8, 0, 4, 0, -2, -2, -4, 4, 0, 2, 0, -1, -3, 5, 2, -4, -6, 1, 0, 2, 0, -4, 0,                    0, -14, 4, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   finite := ((8400671598581349 : Rat)/4503599627370496, (34820286144334039 : Rat)/9007199254740992),   tail := (11205908843422256883653410754680633544921875 : Rat)/189532806340223278813513062192232992400736256,   box := { reLo := (358963370400049842156615231073655368956692367318839 : Rat)/198739551941005964805158272701282902239594420371456,            reHi := (1560086478546353005349786019503058611207791899038429 : Rat)/397479103882011929610316545402565804479188840742912,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -514, a6 := 4271 }
def label : String := "582.b1"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 97, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -514, a6 := 4271 },   conductor := 582,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -2, 1, 1, -2, 0, -1, -4, -2, 2, 1, -4, 1, -4, -2, 2, 0, 0, -1, -1, -4, -1, -2,                    2, 2, -8, 1, 0, -4, 4, 1, 4, -4, 4, -2, 0, 2, -4, 0, -2, 0, 0, -1, -3, -1, 4, -4, 10, -1, 0, -2, 4,                    2, 10, 2, 10, -8, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   finite := ((27496440840006391 : Rat)/9007199254740992, (53041636911478575 : Rat)/9007199254740992),   tail := (2892504864644694084777405894931316375732421875 : Rat)/1330845362240185913610631331650149315264905216,   box := { reLo := (1227034152121255730369371355254517516535305337075293 : Rat)/1395492506556365184550181359216386968403213251772416,            reHi := (11250793951380939993801769030818457847739667917654725 : Rat)/1395492506556365184550181359216386968403213251772416,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -34, a6 := 47 }
def label : String := "582.b2"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -34, a6 := 47 },   conductor := 582,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -2, 1, 1, -2, 0, -1, -4, -2, 2, 1, -4, 1, -4, -2, 2, 0, 0, -1, -1, -4, -1, -2,                    2, 2, -8, 1, 0, -4, 4, 1, 4, -4, 4, -2, 0, 2, -4, 0, -2, 0, 0, -1, -3, -1, 4, -4, 10, -1, 0, -2, 4,                    2, 10, 2, 10, -8, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   finite := ((27496440840006391 : Rat)/9007199254740992, (53041636911478575 : Rat)/9007199254740992),   tail := (2892504864644694084777405894931316375732421875 : Rat)/1330845362240185913610631331650149315264905216,   box := { reLo := (1227034152121255730369371355254517516535305337075293 : Rat)/1395492506556365184550181359216386968403213251772416,            reHi := (11250793951380939993801769030818457847739667917654725 : Rat)/1395492506556365184550181359216386968403213251772416,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -746498, a6 := -248562097 }
def label : String := "582.c1"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 97, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -746498, a6 := -248562097 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, 0, -1, -2, 1, 1, 0, 4, -1, 2, -2, 0, 1, 4, 1, 6, 0, 2, 4, 4, -1, -5, 2, -1, -2, -8, 0,                    8, 1, -4, 4, 0, 1, -2, 6, -2, 0, -8, 2, 8, 4, 0, 4, 0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (1749048163878170449244841929671741410686273139620081266695286699470035750034229511844223010683163608366574960131110438574170584842366541766338303905701714293557854440657757488026887816735530118227134413157090465469182074826486857372705312489381049398616671134508344296094400594918231563714263575537900144682487829999279066079047116009604041133356657817624669767190424229782841159818123738689554201440870571305996794776107382791871586557453903043388152716193356673355076507433111594823742997237055197099227002963082023305262380740233885183933196336792354491597040556231046467270178068315568992658689881942133800134433452055024289246877244116642009285247474989851342303836263177113562227949859873511201974529724389327112899955620976564557969138563993644070860304942718343 : Rat)/25083562826741990410013254942465359064721796563467085776621240796019160363235190884679072166845163875720600143646873692671522881693369029303145276821809447534724613788426250678560566577242974118593548958193352190861972217669733034124975321402457998469842788317358392706350197187447404592177248627530244227856594059874839078432034559371920792093904904868308634469794292349706297472702017187968969355128720912031838223629926114368364375086802461604339139933380726008733286411760887750576575257442931058786478084430182717587284562683869424971327127020322942389676771841111067840815434296014814820096620476094051657561628489504977681628148686770634266049591755478935568383038797138382049765174581243806417113664293327823789112152533303945976109883314838009116651584149782528,   box := { reLo := (341485925952130933032828406160579929741688834382341415313317060659847716156823839737697909606259618144988341503712081176963155421015383072033546392946166713801319412327907459851475336579910171634773939257807215477120581710362334858229707789785213571211235580270254527737999622102079243872635767675957586137637297791808531163506726099157809648027076689735129281679345642159934481739797150922685998166437388738584972718165164328735978546668185440589958749471833394048891040873724582275012627002175230639425054824379548043617106858655805622556481144324317375258289547837518162589174793889642084317266109943635342700352253828719084869866968844966386488375973391232802802259373527628509924614319313224316295763696048366874833434773965631517104927590255905800200194988867927126162902493177 : Rat)/181706680958037599363729890804624369096385775685222271562048906092086744133874854586191318182625586346393589408120397663218102116168547404264231979503679760513114862202006589534575820542835737992203543945176389408821391725453568944046944507767514620892693983035605592260924940073752871548368614585338883230948112580224583119100906020336879901338315447690487792814923194812316139250344789063174043900142239763254752284408649163025625875146087594325731215436869674561087982064210769532639501302328112466741478607962819234676730575990465540422567747478596100080415827974060178217407240366143628002682499680141421684529913833886865604676518802005865839874913191692931120158182375613768339877615596215253821558743888218916312866450585991899029818977940563515679842593888758267057421680640,            reHi := (1540670561955294607534480966276829127548949883875894389403977549400309675233235256673667689481563001612383863186906062327412380836810221308749093919797916507697683831114539059904576596158455537771672291829732002263999206287439760202094405213788357212569920272905512760252176864950384894918048303433575977713599689167146604061085416084285579568916825975977466705916510579368687457267803389543573524445895037622709953441442336187240593083725439000859944303455033685838677849050219343504155884607187047049949507748713111554549414119477848599461963922551252586528355599239145481282919236125407627045958387739143504495715963365357297851352634741707792073338171399017017651703141053405145188238871307223545831921734857987307306338646572231776235416420388318447513955670385616278294473666999 : Rat)/763168060023757917327665541379422350204820257877933540560605405586764325362274389262003536367027462654853075514105670185516028887907899097909774313915454994155082421248427676045218446279910099567254884569740835517049845246904989564997166932623561407749314728749543487495884748309762060503148181258423309569982072836943249100223805285414895585620924880300048729822677418211727784851448114065330984380597407005669959594516326484707628675613567896168071104834852633156569524669685232037085905469778072360314210153443840785642268419159955269774784539410103620337746477491052748513110409537803237611266498656593971075025638102324835539641378968424636527474635405110310704664365977577827027485985504104066050546724330519448514039092461165975925239707350366765855338894332784721641171058688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1749048163878170449244841929671741410686273139620081266695286699470035750034229511844223010683163608366574960131110438574170584842366541766338303905701714293557854440657757488026887816735530118227134413157090465469182074826486857372705312489381049398616671134508344296094400594918231563714263575537900144682487829999279066079047116009604041133356657817624669767190424229782841159818123738689554201440870571305996794776107382791871586557453903043388152716193356673355076507433111594823742997237055197099227002963082023305262380740233885183933196336792354491597040556231046467270178068315568992658689881942133800134433452055024289246877244116642009285247474989851342303836263177113562227949859873511201974529724389327112899955620976564557969138563993644070860304942718343 : Rat)/50167125653483980820026509884930718129443593126934171553242481592038320726470381769358144333690327751441200287293747385343045763386738058606290553643618895069449227576852501357121133154485948237187097916386704381723944435339466068249950642804915996939685576634716785412700394374894809184354497255060488455713188119749678156864069118743841584187809809736617268939588584699412594945404034375937938710257441824063676447259852228736728750173604923208678279866761452017466572823521775501153150514885862117572956168860365435174569125367738849942654254040645884779353543682222135681630868592029629640193240952188103315123256979009955363256297373541268532099183510957871136766077594276764099530349162487612834227328586655647578224305066607891952219766629676018233303168299565056, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -46658, a6 := -3898033 }
def label : String := "582.c2"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -46658, a6 := -3898033 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, 0, -1, -2, 1, 1, 0, 4, -1, 2, -2, 0, 1, 4, 1, 6, 0, 2, 4, 4, -1, -5, 2, -1, -2, -8, 0,                    8, 1, -4, 4, 0, 1, -2, 6, -2, 0, -8, 2, 8, 4, 0, 4, 0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (1749048163878170449244841929671741410686273139620081266695286699470035750034229511844223010683163608366574960131110438574170584842366541766338303905701714293557854440657757488026887816735530118227134413157090465469182074826486857372705312489381049398616671134508344296094400594918231563714263575537900144682487829999279066079047116009604041133356657817624669767190424229782841159818123738689554201440870571305996794776107382791871586557453903043388152716193356673355076507433111594823742997237055197099227002963082023305262380740233885183933196336792354491597040556231046467270178068315568992658689881942133800134433452055024289246877244116642009285247474989851342303836263177113562227949859873511201974529724389327112899955620976564557969138563993644070860304942718343 : Rat)/25083562826741990410013254942465359064721796563467085776621240796019160363235190884679072166845163875720600143646873692671522881693369029303145276821809447534724613788426250678560566577242974118593548958193352190861972217669733034124975321402457998469842788317358392706350197187447404592177248627530244227856594059874839078432034559371920792093904904868308634469794292349706297472702017187968969355128720912031838223629926114368364375086802461604339139933380726008733286411760887750576575257442931058786478084430182717587284562683869424971327127020322942389676771841111067840815434296014814820096620476094051657561628489504977681628148686770634266049591755478935568383038797138382049765174581243806417113664293327823789112152533303945976109883314838009116651584149782528,   box := { reLo := (341485925952130933032828406160579929741688834382341415313317060659847716156823839737697909606259618144988341503712081176963155421015383072033546392946166713801319412327907459851475336579910171634773939257807215477120581710362334858229707789785213571211235580270254527737999622102079243872635767675957586137637297791808531163506726099157809648027076689735129281679345642159934481739797150922685998166437388738584972718165164328735978546668185440589958749471833394048891040873724582275012627002175230639425054824379548043617106858655805622556481144324317375258289547837518162589174793889642084317266109943635342700352253828719084869866968844966386488375973391232802802259373527628509924614319313224316295763696048366874833434773965631517104927590255905800200194988867927126162902493177 : Rat)/181706680958037599363729890804624369096385775685222271562048906092086744133874854586191318182625586346393589408120397663218102116168547404264231979503679760513114862202006589534575820542835737992203543945176389408821391725453568944046944507767514620892693983035605592260924940073752871548368614585338883230948112580224583119100906020336879901338315447690487792814923194812316139250344789063174043900142239763254752284408649163025625875146087594325731215436869674561087982064210769532639501302328112466741478607962819234676730575990465540422567747478596100080415827974060178217407240366143628002682499680141421684529913833886865604676518802005865839874913191692931120158182375613768339877615596215253821558743888218916312866450585991899029818977940563515679842593888758267057421680640,            reHi := (1540670561955294607534480966276829127548949883875894389403977549400309675233235256673667689481563001612383863186906062327412380836810221308749093919797916507697683831114539059904576596158455537771672291829732002263999206287439760202094405213788357212569920272905512760252176864950384894918048303433575977713599689167146604061085416084285579568916825975977466705916510579368687457267803389543573524445895037622709953441442336187240593083725439000859944303455033685838677849050219343504155884607187047049949507748713111554549414119477848599461963922551252586528355599239145481282919236125407627045958387739143504495715963365357297851352634741707792073338171399017017651703141053405145188238871307223545831921734857987307306338646572231776235416420388318447513955670385616278294473666999 : Rat)/763168060023757917327665541379422350204820257877933540560605405586764325362274389262003536367027462654853075514105670185516028887907899097909774313915454994155082421248427676045218446279910099567254884569740835517049845246904989564997166932623561407749314728749543487495884748309762060503148181258423309569982072836943249100223805285414895585620924880300048729822677418211727784851448114065330984380597407005669959594516326484707628675613567896168071104834852633156569524669685232037085905469778072360314210153443840785642268419159955269774784539410103620337746477491052748513110409537803237611266498656593971075025638102324835539641378968424636527474635405110310704664365977577827027485985504104066050546724330519448514039092461165975925239707350366765855338894332784721641171058688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1749048163878170449244841929671741410686273139620081266695286699470035750034229511844223010683163608366574960131110438574170584842366541766338303905701714293557854440657757488026887816735530118227134413157090465469182074826486857372705312489381049398616671134508344296094400594918231563714263575537900144682487829999279066079047116009604041133356657817624669767190424229782841159818123738689554201440870571305996794776107382791871586557453903043388152716193356673355076507433111594823742997237055197099227002963082023305262380740233885183933196336792354491597040556231046467270178068315568992658689881942133800134433452055024289246877244116642009285247474989851342303836263177113562227949859873511201974529724389327112899955620976564557969138563993644070860304942718343 : Rat)/50167125653483980820026509884930718129443593126934171553242481592038320726470381769358144333690327751441200287293747385343045763386738058606290553643618895069449227576852501357121133154485948237187097916386704381723944435339466068249950642804915996939685576634716785412700394374894809184354497255060488455713188119749678156864069118743841584187809809736617268939588584699412594945404034375937938710257441824063676447259852228736728750173604923208678279866761452017466572823521775501153150514885862117572956168860365435174569125367738849942654254040645884779353543682222135681630868592029629640193240952188103315123256979009955363256297373541268532099183510957871136766077594276764099530349162487612834227328586655647578224305066607891952219766629676018233303168299565056, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3104, a6 := -66822 }
def label : String := "582.d1"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3104, a6 := -66822 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -2, 1, 0, 1, 1, -2, 4, 1, 2, 0, -2, 1, 6, 1, 0, -2, 0, 4, 4, 1, -1, 2, 1, 0, -2, -2, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/365800350588273278583183715406738268072602375137092499667983848887773122666133762513129777078341299357372906545958481230939909495221048205581111162193302035754246289429671960480988054455134136087255473723162209677486053134474768220245126072355020356576098542583514168426433208062670648955736809474890212680710846978994097686693642372415492924912475133060879389251501116846751340774619900882498475593142373774779615693907421871071472253959232711032445372458157899994682727007494032835530522139035446240639159027355353088,   box := { reLo := (184561543378787702511627704940262068480914801649216163143032181610355819316105807366927508272638897600843090231191808271047474355892805062701571326973324498303401644413224149711842871164858488260166117427203728136431595658420777961737890334502741115605598689510820387679242400193836498620225586837665890925239076804797406961576737445851452203153906476488957605986366581830866300323145868459445986738518349881126285053539344847035595717922181429306613159341710032226858333260425010495292817573832980997357648557309241045775571871 : Rat)/539625595319867034363540553645217991290794512127228325505900071115316031068522064282419874027597199786549425869860301811678183818612593075542123165606017684575012896641663631115286525607855093050822739709042774074610892763979520128583354416750966438974556416388978835155805275834273813339285489254738215796542806474526294882137450833850347562302990928688413237114960003675418144030673251609196816145346757568055836553390007574175372091886920488779472965098011574091848503679480159101747986914856068920556310012239811406567833600,            reHi := (3950736829336666917278688107019493417450549091610003859347829469357165668962897791498022107944820986794316037232497720352451206017464767758076024877727494657089818861437244084829181422933159898983382115237827898044434568542490836808775867535054736613635367708796699819164525064239017260519227110523862457206184561960881689870822222118706934701460128780407509155235874296107697656564745168523262165303450406457334988465254787486569878660563905398856150072338214613125259626926948633264733389761451591941304015010965291278068402393 : Rat)/827425912823796119357428848922667586645884918595083432442380109043484580971733831899710473508982373006042453000452462777906548521872642715831255520595893783015019774850550901043439339265377809344594867553865586914403368904768597530494476772351481873094319838463100880572234756279219847120237750190598597554698969927606985485944091278570532928864586090655566963576272005635641154180365652467435118089531694937685616048531344947068903874226611416128525213150284413607501038975202910622680246602779305678186342018767710823404011520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/731600701176546557166367430813476536145204750274184999335967697775546245332267525026259554156682598714745813091916962461879818990442096411162222324386604071508492578859343920961976108910268272174510947446324419354972106268949536440490252144710040713152197085167028336852866416125341297911473618949780425361421693957988195373387284744830985849824950266121758778503002233693502681549239801764996951186284747549559231387814843742142944507918465422064890744916315799989365454014988065671061044278070892481278318054710706176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -194, a6 := -1056 }
def label : String := "582.d2"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 97, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -194, a6 := -1056 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -2, 1, 0, 1, 1, -2, 4, 1, 2, 0, -2, 1, 6, 1, 0, -2, 0, 4, 4, 1, -1, 2, 1, 0, -2, -2, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/365800350588273278583183715406738268072602375137092499667983848887773122666133762513129777078341299357372906545958481230939909495221048205581111162193302035754246289429671960480988054455134136087255473723162209677486053134474768220245126072355020356576098542583514168426433208062670648955736809474890212680710846978994097686693642372415492924912475133060879389251501116846751340774619900882498475593142373774779615693907421871071472253959232711032445372458157899994682727007494032835530522139035446240639159027355353088,   box := { reLo := (184561543378787702511627704940262068480914801649216163143032181610355819316105807366927508272638897600843090231191808271047474355892805062701571326973324498303401644413224149711842871164858488260166117427203728136431595658420777961737890334502741115605598689510820387679242400193836498620225586837665890925239076804797406961576737445851452203153906476488957605986366581830866300323145868459445986738518349881126285053539344847035595717922181429306613159341710032226858333260425010495292817573832980997357648557309241045775571871 : Rat)/539625595319867034363540553645217991290794512127228325505900071115316031068522064282419874027597199786549425869860301811678183818612593075542123165606017684575012896641663631115286525607855093050822739709042774074610892763979520128583354416750966438974556416388978835155805275834273813339285489254738215796542806474526294882137450833850347562302990928688413237114960003675418144030673251609196816145346757568055836553390007574175372091886920488779472965098011574091848503679480159101747986914856068920556310012239811406567833600,            reHi := (3950736829336666917278688107019493417450549091610003859347829469357165668962897791498022107944820986794316037232497720352451206017464767758076024877727494657089818861437244084829181422933159898983382115237827898044434568542490836808775867535054736613635367708796699819164525064239017260519227110523862457206184561960881689870822222118706934701460128780407509155235874296107697656564745168523262165303450406457334988465254787486569878660563905398856150072338214613125259626926948633264733389761451591941304015010965291278068402393 : Rat)/827425912823796119357428848922667586645884918595083432442380109043484580971733831899710473508982373006042453000452462777906548521872642715831255520595893783015019774850550901043439339265377809344594867553865586914403368904768597530494476772351481873094319838463100880572234756279219847120237750190598597554698969927606985485944091278570532928864586090655566963576272005635641154180365652467435118089531694937685616048531344947068903874226611416128525213150284413607501038975202910622680246602779305678186342018767710823404011520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/731600701176546557166367430813476536145204750274184999335967697775546245332267525026259554156682598714745813091916962461879818990442096411162222324386604071508492578859343920961976108910268272174510947446324419354972106268949536440490252144710040713152197085167028336852866416125341297911473618949780425361421693957988195373387284744830985849824950266121758778503002233693502681549239801764996951186284747549559231387814843742142944507918465422064890744916315799989365454014988065671061044278070892481278318054710706176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -164, a6 := -1386 }
def label : String := "582.d3"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 97, 97, 97, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -164, a6 := -1386 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -2, 1, 0, 1, 1, -2, 4, 1, 2, 0, -2, 1, 6, 1, 0, -2, 0, 4, 4, 1, -1, 2, 1, 0, -2, -2, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/365800350588273278583183715406738268072602375137092499667983848887773122666133762513129777078341299357372906545958481230939909495221048205581111162193302035754246289429671960480988054455134136087255473723162209677486053134474768220245126072355020356576098542583514168426433208062670648955736809474890212680710846978994097686693642372415492924912475133060879389251501116846751340774619900882498475593142373774779615693907421871071472253959232711032445372458157899994682727007494032835530522139035446240639159027355353088,   box := { reLo := (184561543378787702511627704940262068480914801649216163143032181610355819316105807366927508272638897600843090231191808271047474355892805062701571326973324498303401644413224149711842871164858488260166117427203728136431595658420777961737890334502741115605598689510820387679242400193836498620225586837665890925239076804797406961576737445851452203153906476488957605986366581830866300323145868459445986738518349881126285053539344847035595717922181429306613159341710032226858333260425010495292817573832980997357648557309241045775571871 : Rat)/539625595319867034363540553645217991290794512127228325505900071115316031068522064282419874027597199786549425869860301811678183818612593075542123165606017684575012896641663631115286525607855093050822739709042774074610892763979520128583354416750966438974556416388978835155805275834273813339285489254738215796542806474526294882137450833850347562302990928688413237114960003675418144030673251609196816145346757568055836553390007574175372091886920488779472965098011574091848503679480159101747986914856068920556310012239811406567833600,            reHi := (3950736829336666917278688107019493417450549091610003859347829469357165668962897791498022107944820986794316037232497720352451206017464767758076024877727494657089818861437244084829181422933159898983382115237827898044434568542490836808775867535054736613635367708796699819164525064239017260519227110523862457206184561960881689870822222118706934701460128780407509155235874296107697656564745168523262165303450406457334988465254787486569878660563905398856150072338214613125259626926948633264733389761451591941304015010965291278068402393 : Rat)/827425912823796119357428848922667586645884918595083432442380109043484580971733831899710473508982373006042453000452462777906548521872642715831255520595893783015019774850550901043439339265377809344594867553865586914403368904768597530494476772351481873094319838463100880572234756279219847120237750190598597554698969927606985485944091278570532928864586090655566963576272005635641154180365652467435118089531694937685616048531344947068903874226611416128525213150284413607501038975202910622680246602779305678186342018767710823404011520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/731600701176546557166367430813476536145204750274184999335967697775546245332267525026259554156682598714745813091916962461879818990442096411162222324386604071508492578859343920961976108910268272174510947446324419354972106268949536440490252144710040713152197085167028336852866416125341297911473618949780425361421693957988195373387284744830985849824950266121758778503002233693502681549239801764996951186284747549559231387814843742142944507918465422064890744916315799989365454014988065671061044278070892481278318054710706176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14, a6 := -12 }
def label : String := "582.d4"
def inputConductor : Nat := 582
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 97] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 582 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14, a6 := -12 },   conductor := 582,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -2, 1, 0, 1, 1, -2, 4, 1, 2, 0, -2, 1, 6, 1, 0, -2, 0, 4, 4, 1, -1, 2, 1, 0, -2, -2, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20722939029876007556915283203125,   alphaHi := (1349303770452201895863057907712 : Rat)/5180734757469001865386962890625,   geometricUpper := (3470957817183943 : Rat)/4503599627370496,   tail := (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/365800350588273278583183715406738268072602375137092499667983848887773122666133762513129777078341299357372906545958481230939909495221048205581111162193302035754246289429671960480988054455134136087255473723162209677486053134474768220245126072355020356576098542583514168426433208062670648955736809474890212680710846978994097686693642372415492924912475133060879389251501116846751340774619900882498475593142373774779615693907421871071472253959232711032445372458157899994682727007494032835530522139035446240639159027355353088,   box := { reLo := (184561543378787702511627704940262068480914801649216163143032181610355819316105807366927508272638897600843090231191808271047474355892805062701571326973324498303401644413224149711842871164858488260166117427203728136431595658420777961737890334502741115605598689510820387679242400193836498620225586837665890925239076804797406961576737445851452203153906476488957605986366581830866300323145868459445986738518349881126285053539344847035595717922181429306613159341710032226858333260425010495292817573832980997357648557309241045775571871 : Rat)/539625595319867034363540553645217991290794512127228325505900071115316031068522064282419874027597199786549425869860301811678183818612593075542123165606017684575012896641663631115286525607855093050822739709042774074610892763979520128583354416750966438974556416388978835155805275834273813339285489254738215796542806474526294882137450833850347562302990928688413237114960003675418144030673251609196816145346757568055836553390007574175372091886920488779472965098011574091848503679480159101747986914856068920556310012239811406567833600,            reHi := (3950736829336666917278688107019493417450549091610003859347829469357165668962897791498022107944820986794316037232497720352451206017464767758076024877727494657089818861437244084829181422933159898983382115237827898044434568542490836808775867535054736613635367708796699819164525064239017260519227110523862457206184561960881689870822222118706934701460128780407509155235874296107697656564745168523262165303450406457334988465254787486569878660563905398856150072338214613125259626926948633264733389761451591941304015010965291278068402393 : Rat)/827425912823796119357428848922667586645884918595083432442380109043484580971733831899710473508982373006042453000452462777906548521872642715831255520595893783015019774850550901043439339265377809344594867553865586914403368904768597530494476772351481873094319838463100880572234756279219847120237750190598597554698969927606985485944091278570532928864586090655566963576272005635641154180365652467435118089531694937685616048531344947068903874226611416128525213150284413607501038975202910622680246602779305678186342018767710823404011520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (810744175384369928717250282331242486244242525250467254319821203326043106131140540638689457553603321811243214880876150745482737639979058645173590103809471711601272992632268376930803282251584843175650934668868799055852281583734166961398934810640490993193534882143239384279327896080691681673568138907542737097402866229091275919524390244963657523366611587768915385115297732596914173766239222985158019682933378234158350008967959061817991099147160849681707609405769185690339576571862871790703044366403239172665541571795058503 : Rat)/731600701176546557166367430813476536145204750274184999335967697775546245332267525026259554156682598714745813091916962461879818990442096411162222324386604071508492578859343920961976108910268272174510947446324419354972106268949536440490252144710040713152197085167028336852866416125341297911473618949780425361421693957988195373387284744830985849824950266121758778503002233693502681549239801764996951186284747549559231387814843742142944507918465422064890744916315799989365454014988065671061044278070892481278318054710706176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N582.C582_d4
