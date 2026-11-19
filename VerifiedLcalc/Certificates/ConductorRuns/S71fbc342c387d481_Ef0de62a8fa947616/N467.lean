module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -4, a6 := 3 }
def label : String := "467.a1"
def inputConductor : Nat := 467
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.nonsingular
def minimality : MinimalityWitness := { primes := [467] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 467 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -4, a6 := 3 },   conductor := 467,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, 0, -3, -2, 2, 0, 1, 0, 6, 0, 4, 6, -6, 0, -6, 4, -7, 0, 2, -4, -3, 0, -7, 0, -1, 0, -9, -2, -8, 0,                    6, 0, -12, 0, 2, -12, -2, 0, 18, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18563005664409371852874755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9281502832204685878753662109375,   finite := ((2612679312207581 : Rat)/2251799813685248, (14195728073091533 : Rat)/4503599627370496),   tail := (199435387076660078312637016704082489013671875 : Rat)/175401107082672000989041424606745293056114688,   box := { reLo := (1068491995303806236778810890816228378375630722709 : Rat)/45980347815079969027271275212110638102902128771072,            reHi := (394429494020035258504882739287083328417016712210437 : Rat)/91960695630159938054542550424221276205804257542144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N467.C467_a1
