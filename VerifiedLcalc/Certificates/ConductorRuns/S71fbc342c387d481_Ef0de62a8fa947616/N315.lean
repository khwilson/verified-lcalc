module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1013, a6 := 12656 }
def label : String := "315.a1"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1013, a6 := 12656 },   conductor := 315,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 1, 3, 0, 1, 0, 0, -6, -1, 0, -1, -2, 0, -8, 1, 0, 0, -8, 0, 1, 6, 0, -1, 2, 0,                    4, -5, 0, 2, -1, 0, -2, 8, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   finite := ((8250249447431871 : Rat)/9007199254740992, (11058124103879319 : Rat)/4503599627370496),   tail := (23808944898985995113841541755847930908203125 : Rat)/73851854361361161382709448160724041791963136,   box := { reLo := (91931854813900528432671254432835103915494122654461 : Rat)/154878564077637282316071884629158745692099074588672,            reHi := (215109653352925290451758819737530717691361571101829 : Rat)/77439282038818641158035942314579372846049537294336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -68, a6 := 182 }
def label : String := "315.a2"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -68, a6 := 182 },   conductor := 315,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 1, 3, 0, 1, 0, 0, -6, -1, 0, -1, -2, 0, -8, 1, 0, 0, -8, 0, 1, 6, 0, -1, 2, 0,                    4, -5, 0, 2, -1, 0, -2, 8, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   finite := ((8250249447431871 : Rat)/9007199254740992, (11058124103879319 : Rat)/4503599627370496),   tail := (23808944898985995113841541755847930908203125 : Rat)/73851854361361161382709448160724041791963136,   box := { reLo := (91931854813900528432671254432835103915494122654461 : Rat)/154878564077637282316071884629158745692099074588672,            reHi := (215109653352925290451758819737530717691361571101829 : Rat)/77439282038818641158035942314579372846049537294336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -23, a6 := -34 }
def label : String := "315.a3"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -23, a6 := -34 },   conductor := 315,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 1, 3, 0, 1, 0, 0, -6, -1, 0, -1, -2, 0, -8, 1, 0, 0, -8, 0, 1, 6, 0, -1, 2, 0,                    4, -5, 0, 2, -1, 0, -2, 8, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   finite := ((8250249447431871 : Rat)/9007199254740992, (11058124103879319 : Rat)/4503599627370496),   tail := (23808944898985995113841541755847930908203125 : Rat)/73851854361361161382709448160724041791963136,   box := { reLo := (91931854813900528432671254432835103915494122654461 : Rat)/154878564077637282316071884629158745692099074588672,            reHi := (215109653352925290451758819737530717691361571101829 : Rat)/77439282038818641158035942314579372846049537294336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 157, a6 := 992 }
def label : String := "315.a4"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 157, a6 := 992 },   conductor := 315,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 1, 3, 0, 1, 0, 0, -6, -1, 0, -1, -2, 0, -8, 1, 0, 0, -8, 0, 1, 6, 0, -1, 2, 0,                    4, -5, 0, 2, -1, 0, -2, 8, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   finite := ((8250249447431871 : Rat)/9007199254740992, (11058124103879319 : Rat)/4503599627370496),   tail := (23808944898985995113841541755847930908203125 : Rat)/73851854361361161382709448160724041791963136,   box := { reLo := (91931854813900528432671254432835103915494122654461 : Rat)/154878564077637282316071884629158745692099074588672,            reHi := (215109653352925290451758819737530717691361571101829 : Rat)/77439282038818641158035942314579372846049537294336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1182, a6 := 16362 }
def label : String := "315.b1"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1182, a6 := 16362 },   conductor := 315,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, -2, 1, 0, 1, 0, 0, 0, 3, 0, 5, 0, 0, 4, -3, 0, 2, -2, 0, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   geometricUpper := (6321817768441055 : Rat)/9007199254740992,   tail := (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/11025502485669231638325589001054269053142213813584422305968893759560020138689703757122196419042403692222275415023866001234618032663807843291018342931871555109259645684280648459191299746229295217891245241116748147890695510154884713502086331058005657285451448342375897389145473974849799892110570178891818045851954135760562106574797807720057767781599135480309387815246985649733507335318616191258614300672,   box := { reLo := (216993913920384897236111799957748685795071455929988629001343701849907301179160676534052822082261522345227208469998239129630595980137308577623008541058205689925735313032441113829202668559823750746014133753549653004971554784285215958208860595928189929139548629610982070085369529298954055812439987500986559650292716234528147077150842841818229737105720959045846723655019562541979983327505424807638664226975355021 : Rat)/409951832120013792814809607447604984802946499637698959921769773257555804999680675104362289971315415232744016711352564118475746710120439481383921224552573283447982988481547291703677489902760858039438874785762891563353284609427895875718031763916769760007962142726230261228328439426591612809439576424231517894484007209198905528169585432329307330031747387303508302607746631241310481100380408422725529426659901440,            reHi := (10737881740469982272647925073429935383553423395155279298480015663269984507971256692159559574287621582514634468953080085150726050995542774107343761338550423254054235127736941338885785237584344332375332164803389144228369907522026409022658690083972186416971795133702600468455210299373891919843987081445695919431468470762111990656381831256467182210554645464531707632511401707752931560624983393323684499412356799 : Rat)/5324049767792386919672852044774090711726577917372713765217789263085140324671177598757951817809291106918753463783799534006178528702862850407583392526656795888934844006253860931216590777957933221291413958256660929394198501421141504879454957972945061818285222632808185210757512200345345620901812680834175557071220872846739032833371239380900095195217498536409198735165540665471564689615329979515915966579998720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/22051004971338463276651178002108538106284427627168844611937787519120040277379407514244392838084807384444550830047732002469236065327615686582036685863743110218519291368561296918382599492458590435782490482233496295781391020309769427004172662116011314570902896684751794778290947949699599784221140357783636091703908271521124213149595615440115535563198270960618775630493971299467014670637232382517228601344, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := -18 }
def label : String := "315.b2"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := -18 },   conductor := 315,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, -2, 1, 0, 1, 0, 0, 0, 3, 0, 5, 0, 0, 4, -3, 0, 2, -2, 0, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   geometricUpper := (6321817768441055 : Rat)/9007199254740992,   tail := (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/11025502485669231638325589001054269053142213813584422305968893759560020138689703757122196419042403692222275415023866001234618032663807843291018342931871555109259645684280648459191299746229295217891245241116748147890695510154884713502086331058005657285451448342375897389145473974849799892110570178891818045851954135760562106574797807720057767781599135480309387815246985649733507335318616191258614300672,   box := { reLo := (216993913920384897236111799957748685795071455929988629001343701849907301179160676534052822082261522345227208469998239129630595980137308577623008541058205689925735313032441113829202668559823750746014133753549653004971554784285215958208860595928189929139548629610982070085369529298954055812439987500986559650292716234528147077150842841818229737105720959045846723655019562541979983327505424807638664226975355021 : Rat)/409951832120013792814809607447604984802946499637698959921769773257555804999680675104362289971315415232744016711352564118475746710120439481383921224552573283447982988481547291703677489902760858039438874785762891563353284609427895875718031763916769760007962142726230261228328439426591612809439576424231517894484007209198905528169585432329307330031747387303508302607746631241310481100380408422725529426659901440,            reHi := (10737881740469982272647925073429935383553423395155279298480015663269984507971256692159559574287621582514634468953080085150726050995542774107343761338550423254054235127736941338885785237584344332375332164803389144228369907522026409022658690083972186416971795133702600468455210299373891919843987081445695919431468470762111990656381831256467182210554645464531707632511401707752931560624983393323684499412356799 : Rat)/5324049767792386919672852044774090711726577917372713765217789263085140324671177598757951817809291106918753463783799534006178528702862850407583392526656795888934844006253860931216590777957933221291413958256660929394198501421141504879454957972945061818285222632808185210757512200345345620901812680834175557071220872846739032833371239380900095195217498536409198735165540665471564689615329979515915966579998720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/22051004971338463276651178002108538106284427627168844611937787519120040277379407514244392838084807384444550830047732002469236065327615686582036685863743110218519291368561296918382599492458590435782490482233496295781391020309769427004172662116011314570902896684751794778290947949699599784221140357783636091703908271521124213149595615440115535563198270960618775630493971299467014670637232382517228601344, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 78, a6 := 45 }
def label : String := "315.b3"
def inputConductor : Nat := 315
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 315 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 78, a6 := 45 },   conductor := 315,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, -2, 1, 0, 1, 0, 0, 0, 3, 0, 5, 0, 0, 4, -3, 0, 2, -2, 0, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7622810756681887340545654296875,   alphaHi := (5397215081808807583452231630848 : Rat)/15245621513363774585723876953125,   geometricUpper := (6321817768441055 : Rat)/9007199254740992,   tail := (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/11025502485669231638325589001054269053142213813584422305968893759560020138689703757122196419042403692222275415023866001234618032663807843291018342931871555109259645684280648459191299746229295217891245241116748147890695510154884713502086331058005657285451448342375897389145473974849799892110570178891818045851954135760562106574797807720057767781599135480309387815246985649733507335318616191258614300672,   box := { reLo := (216993913920384897236111799957748685795071455929988629001343701849907301179160676534052822082261522345227208469998239129630595980137308577623008541058205689925735313032441113829202668559823750746014133753549653004971554784285215958208860595928189929139548629610982070085369529298954055812439987500986559650292716234528147077150842841818229737105720959045846723655019562541979983327505424807638664226975355021 : Rat)/409951832120013792814809607447604984802946499637698959921769773257555804999680675104362289971315415232744016711352564118475746710120439481383921224552573283447982988481547291703677489902760858039438874785762891563353284609427895875718031763916769760007962142726230261228328439426591612809439576424231517894484007209198905528169585432329307330031747387303508302607746631241310481100380408422725529426659901440,            reHi := (10737881740469982272647925073429935383553423395155279298480015663269984507971256692159559574287621582514634468953080085150726050995542774107343761338550423254054235127736941338885785237584344332375332164803389144228369907522026409022658690083972186416971795133702600468455210299373891919843987081445695919431468470762111990656381831256467182210554645464531707632511401707752931560624983393323684499412356799 : Rat)/5324049767792386919672852044774090711726577917372713765217789263085140324671177598757951817809291106918753463783799534006178528702862850407583392526656795888934844006253860931216590777957933221291413958256660929394198501421141504879454957972945061818285222632808185210757512200345345620901812680834175557071220872846739032833371239380900095195217498536409198735165540665471564689615329979515915966579998720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (8200481442044337919335831952352334971516470547067600110523861800938331500906643659004145976038896249534084030754599262899154464052539128354011228109573146027665128718275839370448794852902764151393808960763629678575540899258830843429730994147137796903704055882675244450749706153425666093298292579231116012164172353980589892085344833126464996837056438277253281384398975582403020258061587810516357421875 : Rat)/22051004971338463276651178002108538106284427627168844611937787519120040277379407514244392838084807384444550830047732002469236065327615686582036685863743110218519291368561296918382599492458590435782490482233496295781391020309769427004172662116011314570902896684751794778290947949699599784221140357783636091703908271521124213149595615440115535563198270960618775630493971299467014670637232382517228601344, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N315.C315_b3
