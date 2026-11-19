module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -116, a6 := 444 }
def label : String := "551.a1"
def inputConductor : Nat := 551
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 29, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 551 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -116, a6 := 444 },   conductor := 551,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -2, -2, 2, -1, 4, -1, 0, 1, 2, 1, -4, 2, 2, 2, -4, 3, -2, 1, -2, 2, -2, 8, 0, -4, -4, 4, -2, 1,                    -4, -10, 8, -2, -6, 1, 2, -8, -2, -4, 0, -6, -4, 5, 2, -1, -16, 7, 8, -6, 8, -6, 4, -12, -8, -1, 0,                    -2, -2, -10, 4, 1, 20, -1, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20163487778272848224639892578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5040871944568212032318115234375,   finite := ((3426399933045405 : Rat)/9007199254740992, (11880241355796383 : Rat)/4503599627370496),   tail := (34609447650866228699084530877590179443359375 : Rat)/758432494218573431391196157318873362131320832,   box := { reLo := (532474102527392061578219451787835018444179063889635 : Rat)/1590548222115469708788909803713589909140423745470464,            reHi := (2134178806780659842648115721270037196880785053096161 : Rat)/795274111057734854394454901856794954570211872735232,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -11, a6 := 14 }
def label : String := "551.b1"
def inputConductor : Nat := 551
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 551 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -11, a6 := 14 },   conductor := 551,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, -1, -1, 2, 3, -2, 1, -3, -1, -5, -2, -1, -1, 2, 2, 1, 1, 2, 3, 0, 3, -4, 5, -5, -2, 1,                    1, -7, -5, -3, -2, -2, 2, 2, -1, -5, -3, 0, -2, -11, 3, 2, 0, -9, -1, -3, 4, 2, 5, 1, 5, 3, 6, 1, -1,                    8, 1, 0, 7, -4, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20163487778272848224639892578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5040871944568212032318115234375,   finite := ((8740949390080919 : Rat)/4503599627370496, (17382973428905313 : Rat)/4503599627370496),   tail := (2507119572750187735810580050970172882080078125 : Rat)/1351409127280395771953594187287125110772727808,   box := { reLo := (60714782825710698098944750332258016974437567267131 : Rat)/708527588523584138486005989264392250076811917000704,            reHi := (4049224281300122440424820962335421199441765566467037 : Rat)/708527588523584138486005989264392250076811917000704,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := -5 }
def label : String := "551.c1"
def inputConductor : Nat := 551
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 551 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := -5 },   conductor := 551,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 1, -1, -1, 1, -4, -3, -2, -1, 1, -1, -1, -4, -1, -1, 0, -2, 1, 1, -4, 1, -4, -3, -4, -1, -5, 4,                    1, -1, 5, 5, 1, 0, 4, 2, 10, 1, -1, 3, -6, -4, -7, -1, 2, -4, 7, -1, 9, -4, 0, 1, -3, -5, -1, 12, 1,                    1, -10, 1, -8, 5, 8, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20163487778272848224639892578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5040871944568212032318115234375,   finite := ((7115733565121591 : Rat)/2251799813685248, (58119464380805835 : Rat)/9007199254740992),   tail := (2507119572750187735810580050970172882080078125 : Rat)/1351409127280395771953594187287125110772727808,   box := { reLo := (462254497734279981344978811148392012190710657664859 : Rat)/354263794261792069243002994632196125038405958500352,            reHi := (11772534365776333301705987069178479464366430018112415 : Rat)/1417055177047168276972011978528784500153623834001408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2376, a6 := -61851 }
def label : String := "551.d1"
def inputConductor : Nat := 551
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19, 19, 19, 19, 19, 29, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 551 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2376, a6 := -61851 },   conductor := 551,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 2, -2, 2, -1, -4, -1, 0, 1, -2, -3, -4, -2, -2, 2, -4, -1, 2, 1, -2, 2, -6, 0, 0, -4, -4, 4, -2,                    1, 4, 2, -8, 6, -2, 1, 2, -4, 2, 4, 0, -6, 4, 1, -6, -1, 0, 3, 8, -6, -8, 2, -4, 4, 8, 3, 0, -2, 2,                    14, 4, -3, 4, -1, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20163487778272848224639892578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5040871944568212032318115234375,   finite := ((3724611417000617 : Rat)/1125899906842624, (61897458017012743 : Rat)/9007199254740992),   tail := (2507119572750187735810580050970172882080078125 : Rat)/1351409127280395771953594187287125110772727808,   box := { reLo := (257360303204581888372530020360521826741593871510533 : Rat)/177131897130896034621501497316098062519202979250176,            reHi := (12366906188762301222532422886500326312643149141168107 : Rat)/1417055177047168276972011978528784500153623834001408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N551.C551_d1
