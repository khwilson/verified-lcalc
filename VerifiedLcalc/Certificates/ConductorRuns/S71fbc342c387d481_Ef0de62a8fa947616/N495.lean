module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -533, a6 := -4598 }
def label : String := "495.a1"
def inputConductor : Nat := 495
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 495 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -533, a6 := -4598 },   conductor := 495,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 0, 3, 0, 1, 1, 0, 2, 0, 0, -1, -6, 0, -4, 1, 0, -1, -4, 0, 1, -2, 0, 0, -6, 0,                    -8, -5, 0, 6, 0, 0, -2, 4, 0, -3, -2, 0, 4, -1, 0, 4, 12, 0, -7, -1, 0, -2, 2, 0, -1, 0, 0, 6, -4, 0,                    -10, 8, 0, 7],   alphaLo := (84331485653262618491172683776 : Rat)/298615593400505161285400390625,   alphaHi := (5397215081808807583452231630848 : Rat)/19111397977632330226898193359375,   finite := ((6597603660831493 : Rat)/4503599627370496, (28683427048234561 : Rat)/9007199254740992),   tail := (14665580001875042982970654570484161376953125 : Rat)/10833181548219599461772501318920589249871872,   box := { reLo := (40420425008007652392296053497015679635737499262357 : Rat)/363501253603389271207281994975631225384756737736704,            reHi := (3299329980476728830910057948710690018389673651711889 : Rat)/727002507206778542414563989951262450769513475473408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -263, a6 := 1666 }
def label : String := "495.a2"
def inputConductor : Nat := 495
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 495 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -263, a6 := 1666 },   conductor := 495,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 0, 3, 0, 1, 1, 0, 2, 0, 0, -1, -6, 0, -4, 1, 0, -1, -4, 0, 1, -2, 0, 0, -6, 0,                    -8, -5, 0, 6, 0, 0, -2, 4, 0, -3, -2, 0, 4, -1, 0, 4, 12, 0, -7, -1, 0, -2, 2, 0, -1, 0, 0, 6, -4, 0,                    -10, 8, 0, 7],   alphaLo := (84331485653262618491172683776 : Rat)/298615593400505161285400390625,   alphaHi := (5397215081808807583452231630848 : Rat)/19111397977632330226898193359375,   finite := ((6597603660831493 : Rat)/4503599627370496, (28683427048234561 : Rat)/9007199254740992),   tail := (14665580001875042982970654570484161376953125 : Rat)/10833181548219599461772501318920589249871872,   box := { reLo := (40420425008007652392296053497015679635737499262357 : Rat)/363501253603389271207281994975631225384756737736704,            reHi := (3299329980476728830910057948710690018389673651711889 : Rat)/727002507206778542414563989951262450769513475473408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -38, a6 := -44 }
def label : String := "495.a3"
def inputConductor : Nat := 495
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 495 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -38, a6 := -44 },   conductor := 495,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 0, 3, 0, 1, 1, 0, 2, 0, 0, -1, -6, 0, -4, 1, 0, -1, -4, 0, 1, -2, 0, 0, -6, 0,                    -8, -5, 0, 6, 0, 0, -2, 4, 0, -3, -2, 0, 4, -1, 0, 4, 12, 0, -7, -1, 0, -2, 2, 0, -1, 0, 0, 6, -4, 0,                    -10, 8, 0, 7],   alphaLo := (84331485653262618491172683776 : Rat)/298615593400505161285400390625,   alphaHi := (5397215081808807583452231630848 : Rat)/19111397977632330226898193359375,   finite := ((6597603660831493 : Rat)/4503599627370496, (28683427048234561 : Rat)/9007199254740992),   tail := (14665580001875042982970654570484161376953125 : Rat)/10833181548219599461772501318920589249871872,   box := { reLo := (40420425008007652392296053497015679635737499262357 : Rat)/363501253603389271207281994975631225384756737736704,            reHi := (3299329980476728830910057948710690018389673651711889 : Rat)/727002507206778542414563989951262450769513475473408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7, a6 := -8 }
def label : String := "495.a4"
def inputConductor : Nat := 495
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 495 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7, a6 := -8 },   conductor := 495,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 0, 3, 0, 1, 1, 0, 2, 0, 0, -1, -6, 0, -4, 1, 0, -1, -4, 0, 1, -2, 0, 0, -6, 0,                    -8, -5, 0, 6, 0, 0, -2, 4, 0, -3, -2, 0, 4, -1, 0, 4, 12, 0, -7, -1, 0, -2, 2, 0, -1, 0, 0, 6, -4, 0,                    -10, 8, 0, 7],   alphaLo := (84331485653262618491172683776 : Rat)/298615593400505161285400390625,   alphaHi := (5397215081808807583452231630848 : Rat)/19111397977632330226898193359375,   finite := ((6597603660831493 : Rat)/4503599627370496, (28683427048234561 : Rat)/9007199254740992),   tail := (14665580001875042982970654570484161376953125 : Rat)/10833181548219599461772501318920589249871872,   box := { reLo := (40420425008007652392296053497015679635737499262357 : Rat)/363501253603389271207281994975631225384756737736704,            reHi := (3299329980476728830910057948710690018389673651711889 : Rat)/727002507206778542414563989951262450769513475473408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N495.C495_a4
