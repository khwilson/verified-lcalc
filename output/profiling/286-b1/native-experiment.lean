import VerifiedLcalc.Assumptions.DerivativeCertification
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true
set_option Elab.async false
set_option trace.profiler true
set_option trace.profiler.threshold 10
namespace VerifiedLcalc.ProfileNativeCurve
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -33, a6 := 61 }
def label : String := "286.b1"
def inputConductor : Nat := 286
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.ProfileNativeCurve.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 11, 11, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.ProfileNativeCurve.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.ProfileNativeCurve.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.ProfileNativeCurve.local_data_valid
theorem conductor_formula : wildLevel equation localData = 286 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.ProfileNativeCurve.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.ProfileNativeCurve.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.ProfileNativeCurve.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -33, a6 := 61 },   conductor := 286,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 1, -1, -2, 1, -1, -1, -1, -1, 1, 1, -1, 2, -4, -1, -1, 1, -8, 1, -4, 1, 5, 1,                    -8, -1, 0, -1, 1, 1, -1, -2, 7, 4, 1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/7263448771128582668304443359375,   alphaHi := (5397215081808807583452231630848 : Rat)/14526897542257165241241455078125,   finite := ((1004990881850203 : Rat)/1125899906842624, (1243869816965115 : Rat)/562949953421312),   tail := (24488496693844250985806728371143341064453125 : Rat)/106238359499268304943252251032734806956834816,   box := { reLo := (18439485331339155463487404512331582969915722911813 : Rat)/27849748512576190531043918094725233234892506005504,            reHi := (33977554845201439907166270663480196454015443040165 : Rat)/13924874256288095265521959047362616617446253002752,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by native_decide

#print axioms VerifiedLcalc.ProfileNativeCurve.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.ProfileNativeCurve.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.ProfileNativeCurve.coefficients_correct
end VerifiedLcalc.ProfileNativeCurve
