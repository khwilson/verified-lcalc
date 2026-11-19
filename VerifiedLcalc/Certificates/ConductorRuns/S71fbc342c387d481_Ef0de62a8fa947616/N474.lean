module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 81, a6 := -27 }
def label : String := "474.a1"
def inputConductor : Nat := 474
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 79] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 474 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 81, a6 := -27 },   conductor := 474,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 2, 1, -3, -1, 1, -2, -5, -1, -1, 3, -2, 1, 5, -1, -6, 2, 3, 5, 3, 1, -1, 1, -1, -3, -5,                    2, -4, -1, 5, -5, -6, 1, -8, 6, 1, -2, -2, -3, -5, -5, 2, -3, 0, -1, 2, 1, -5, -1, 2, 1, -10, 3, 6,                    5, -2, -2, -12, 4, -3, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18701611364733604145050048828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4675402841183401012420654296875,   finite := ((1726098087356957 : Rat)/1125899906842624, (7423089596834325 : Rat)/2251799813685248),   tail := (207972831515162043365379693702220916748046875 : Rat)/174892578381592022572021269849119630785773568,   box := { reLo := (7884245529849430883175676547545956979855226653903 : Rat)/22923520033632029582559971881663808246352913104896,            reHi := (205654239096371791546017823040579458393634275229175 : Rat)/45847040067264059165119943763327616492705826209792,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -7, a6 := 14 }
def label : String := "474.b1"
def inputConductor : Nat := 474
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 79] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 474 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -7, a6 := 14 },   conductor := 474,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -2, -1, -1, -1, 1, 2, -5, 1, -1, 1, -2, 1, -1, -1, -2, -2, -1, 5, -5, -1, -1, 1, 1, -1,                    1, 2, 0, -1, -5, 1, 2, 1, 4, 2, -1, 2, -6, 1, 1, -5, -2, 5, 4, 1, -6, 1, -1, -1, -2, -1, 10, 1, -2,                    -1, -6, -2, 0, 0, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18701611364733604145050048828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4675402841183401012420654296875,   finite := ((8268141185201719 : Rat)/4503599627370496, (8245026665301497 : Rat)/2251799813685248),   tail := (207972831515162043365379693702220916748046875 : Rat)/174892578381592022572021269849119630785773568,   box := { reLo := (59303148159302081701323827897118664007697127813901 : Rat)/91694080134528118330239887526655232985411652419584,            reHi := (222389022304792157575356977494345817455015842818563 : Rat)/45847040067264059165119943763327616492705826209792,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N474.C474_b1
