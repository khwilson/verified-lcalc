module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -309, a6 := 1991 }
def label : String := "524.a1"
def inputConductor : Nat := 524
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 131] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 524 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -309, a6 := 1991 },   conductor := 524,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -2, 0, -3, 0, -2, 0, 0, 0, 1, 0, -2, 0, -4, 0, -6, 0, -3, 0, 2, 0, -1, 0, -5, 0, 0, 0, 2,                    0, 0, 0, 6, 0, 0, 0, 1, 0, 5, 0, -3, 0, 4, 0, 6, 0, 2, 0, -4, 0, 3, 0, 0, 0, -6, 0, -9, 0, 5, 0, 6,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19663259032646449947357177734375,   alphaHi := (2698607540904403791726115815424 : Rat)/9831629516323224925994873046875,   finite := ((11522028008157065 : Rat)/4503599627370496, (44005060794965065 : Rat)/9007199254740992),   tail := (2192539480465747398779529202383899688720703125 : Rat)/1368727710934124375112245621778261549953056768,   box := { reLo := (686407908064202316121933390797529206890474750713135 : Rat)/717607514110230200378849032550881191501788226781184,            reHi := (9310849256097664430489875485536217039321452484545135 : Rat)/1435215028220460400757698065101762383003576453562368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N524.C524_a1
