module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := 2 }
def label : String := "335.a1"
def inputConductor : Nat := 335
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 335 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := 2 },   conductor := 335,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 1, 0, -2, 0, -3, 0, -2, 0, -2, 0, 0, 4, -3, 0, -1, -2, 0, 0, -1, 0, 1, 0, 0, 4, -9, 0,                    0, 0, 0, 0, -2, 6, -3, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15722161765727637767791748046875,   alphaHi := (2698607540904403791726115815424 : Rat)/7861080882863818836212158203125,   finite := ((3034832508446731 : Rat)/2251799813685248, (14652395841471009 : Rat)/4503599627370496),   tail := (583040929497691511624408219180583953857421875 : Rat)/1469143384179788895242770840068918251456823296,   box := { reLo := (366209149996807401575407118449478396932421440317303 : Rat)/385127123302426580154520919099026506109897486106624,            reHi := (2811692343757969197174560518980667120711059655305317 : Rat)/770254246604853160309041838198053012219794972213248,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N335.C335_a1
