module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -111, a6 := 450 }
def label : String := "504.a1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -111, a6 := 450 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, -2, 0, 2, 0, 0, 0, -6, 0, -4, 0, 0, 0, -6, 0, -1, 0, 0, 0, 0, 0, -4,                    0, 0, 0, 2, 0, 10, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 12, 0, 4, 0, 0, 0, -12, 0, 6, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20779876568484321 : Rat)/9007199254740992, (38463555647999951 : Rat)/9007199254740992),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318208252672523750894108220409789789636482258046431 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (2063212900254431881610825664532836543587071541685361 : Rat)/362064350956016040371758895190488085258906697203712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -6, a6 := 9 }
def label : String := "504.a2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -6, a6 := 9 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, -2, 0, 2, 0, 0, 0, -6, 0, -4, 0, 0, 0, -6, 0, -1, 0, 0, 0, 0, 0, -4,                    0, 0, 0, 2, 0, 10, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 12, 0, 4, 0, 0, 0, -12, 0, 6, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20779876568484321 : Rat)/9007199254740992, (38463555647999951 : Rat)/9007199254740992),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318208252672523750894108220409789789636482258046431 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (2063212900254431881610825664532836543587071541685361 : Rat)/362064350956016040371758895190488085258906697203712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1371, a6 := -19514 }
def label : String := "504.b1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1371, a6 := -19514 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -6, 0, -4, 0, 0, 0, 4, 0, -1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, -10, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8, 0, 1, 0, 0, 0, -6, 0, 0, 0, 0, 0, -4, 0, -10, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20781504035928165 : Rat)/9007199254740992, (19236159945648335 : Rat)/4503599627370496),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318273672335961003072347641912275843969261083508315 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (1031782599225903689725015247663537498801476227683185 : Rat)/181032175478008020185879447595244042629453348601856,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -111, a6 := -110 }
def label : String := "504.b2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -111, a6 := -110 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -6, 0, -4, 0, 0, 0, 4, 0, -1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, -10, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8, 0, 1, 0, 0, 0, -6, 0, 0, 0, 0, 0, -4, 0, -10, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20781504035928165 : Rat)/9007199254740992, (19236159945648335 : Rat)/4503599627370496),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318273672335961003072347641912275843969261083508315 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (1031782599225903689725015247663537498801476227683185 : Rat)/181032175478008020185879447595244042629453348601856,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -66, a6 := 205 }
def label : String := "504.b3"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -66, a6 := 205 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -6, 0, -4, 0, 0, 0, 4, 0, -1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, -10, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8, 0, 1, 0, 0, 0, -6, 0, 0, 0, 0, 0, -4, 0, -10, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20781504035928165 : Rat)/9007199254740992, (19236159945648335 : Rat)/4503599627370496),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318273672335961003072347641912275843969261083508315 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (1031782599225903689725015247663537498801476227683185 : Rat)/181032175478008020185879447595244042629453348601856,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 429, a6 := -866 }
def label : String := "504.b4"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 429, a6 := -866 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -6, 0, -4, 0, 0, 0, 4, 0, -1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, -10, 0, 0, 0, 10, 0, 12, 0, 0, 0, 8, 0, 1, 0, 0, 0, -6, 0, 0, 0, 0, 0, -4, 0, -10, 0,                    0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((20781504035928165 : Rat)/9007199254740992, (19236159945648335 : Rat)/4503599627370496),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (318273672335961003072347641912275843969261083508315 : Rat)/362064350956016040371758895190488085258906697203712,            reHi := (1031782599225903689725015247663537498801476227683185 : Rat)/181032175478008020185879447595244042629453348601856,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2691, a6 := -53730 }
def label : String := "504.c1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2691, a6 := -53730 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 8, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (2078913115487474618053437787810767570454444819079243113557275250515344520853698460834875229175004045428799740813452221406694583382159489082702570018495938006656397406997508354598608141655682545568772514960601234856728680998577004438316147088739699978078116953216773119572424051808199032749177685402474296350141700932747843529163635762513201401379947073018091108369622662708903366824775730309321266759595275773814947723476920754415076794320766483681271730836311149145817250994642881946144504400222988238362386018907509600472263673792402827 : Rat)/8269893846696429149816492110732759103198643139665847605803014370100384677950282131921669218082320787342942404729519788530063017919823015945909381941922889615806417110303604161537163503037763662890106944365148145817510407675276690337246820766827083726468412611734808426335224166921448600030833018713643001533662278748530099087825069777462212825489098781768388887678372408251208085911742561537601233231424060464542765385898677372933503765632905990850029412306306133337223528649081024788011816846127786840594693500058390971592151350535782400,            reHi := (2835451949469044440653748794335743016716301371226453433620601825196576407079384281515211719902795016381220814471860991336879470389904884555154710145751710415728109395495227606559948435544631952288430147909404164884015370544638575594469073025731146841186719843912230579167825677155945571643412098070746597856009006588386930954714608226572441039100117606555701288839850640056934395757209859783177291346360390362277239596718348134473854313898640946075452383944185708575150302005316694525091961970797777449569311962264226409837827982296541859 : Rat)/1181413406670918449973784587247537014742663305666549657971859195728626382564326018845952745440331541048991772104217112647151859702831859420844197420274698516543773872900514880219594786148251951841443849195021163688215772525039527191035260109546726246638344658819258346619317738131635514290119002673377571647666039821218585583975009968208887546498442683109769841096910344035886869415963223076800176175917722923506109340842668196133357680804700855835718487472329447619603361235583003541144545263732540977227813357151198710227450192933683200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -531, a6 := 3726 }
def label : String := "504.c2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -531, a6 := 3726 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 8, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (2078913115487474618053437787810767570454444819079243113557275250515344520853698460834875229175004045428799740813452221406694583382159489082702570018495938006656397406997508354598608141655682545568772514960601234856728680998577004438316147088739699978078116953216773119572424051808199032749177685402474296350141700932747843529163635762513201401379947073018091108369622662708903366824775730309321266759595275773814947723476920754415076794320766483681271730836311149145817250994642881946144504400222988238362386018907509600472263673792402827 : Rat)/8269893846696429149816492110732759103198643139665847605803014370100384677950282131921669218082320787342942404729519788530063017919823015945909381941922889615806417110303604161537163503037763662890106944365148145817510407675276690337246820766827083726468412611734808426335224166921448600030833018713643001533662278748530099087825069777462212825489098781768388887678372408251208085911742561537601233231424060464542765385898677372933503765632905990850029412306306133337223528649081024788011816846127786840594693500058390971592151350535782400,            reHi := (2835451949469044440653748794335743016716301371226453433620601825196576407079384281515211719902795016381220814471860991336879470389904884555154710145751710415728109395495227606559948435544631952288430147909404164884015370544638575594469073025731146841186719843912230579167825677155945571643412098070746597856009006588386930954714608226572441039100117606555701288839850640056934395757209859783177291346360390362277239596718348134473854313898640946075452383944185708575150302005316694525091961970797777449569311962264226409837827982296541859 : Rat)/1181413406670918449973784587247537014742663305666549657971859195728626382564326018845952745440331541048991772104217112647151859702831859420844197420274698516543773872900514880219594786148251951841443849195021163688215772525039527191035260109546726246638344658819258346619317738131635514290119002673377571647666039821218585583975009968208887546498442683109769841096910344035886869415963223076800176175917722923506109340842668196133357680804700855835718487472329447619603361235583003541144545263732540977227813357151198710227450192933683200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -171, a6 := -810 }
def label : String := "504.c3"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -171, a6 := -810 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 8, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (2078913115487474618053437787810767570454444819079243113557275250515344520853698460834875229175004045428799740813452221406694583382159489082702570018495938006656397406997508354598608141655682545568772514960601234856728680998577004438316147088739699978078116953216773119572424051808199032749177685402474296350141700932747843529163635762513201401379947073018091108369622662708903366824775730309321266759595275773814947723476920754415076794320766483681271730836311149145817250994642881946144504400222988238362386018907509600472263673792402827 : Rat)/8269893846696429149816492110732759103198643139665847605803014370100384677950282131921669218082320787342942404729519788530063017919823015945909381941922889615806417110303604161537163503037763662890106944365148145817510407675276690337246820766827083726468412611734808426335224166921448600030833018713643001533662278748530099087825069777462212825489098781768388887678372408251208085911742561537601233231424060464542765385898677372933503765632905990850029412306306133337223528649081024788011816846127786840594693500058390971592151350535782400,            reHi := (2835451949469044440653748794335743016716301371226453433620601825196576407079384281515211719902795016381220814471860991336879470389904884555154710145751710415728109395495227606559948435544631952288430147909404164884015370544638575594469073025731146841186719843912230579167825677155945571643412098070746597856009006588386930954714608226572441039100117606555701288839850640056934395757209859783177291346360390362277239596718348134473854313898640946075452383944185708575150302005316694525091961970797777449569311962264226409837827982296541859 : Rat)/1181413406670918449973784587247537014742663305666549657971859195728626382564326018845952745440331541048991772104217112647151859702831859420844197420274698516543773872900514880219594786148251951841443849195021163688215772525039527191035260109546726246638344658819258346619317738131635514290119002673377571647666039821218585583975009968208887546498442683109769841096910344035886869415963223076800176175917722923506109340842668196133357680804700855835718487472329447619603361235583003541144545263732540977227813357151198710227450192933683200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := -54 }
def label : String := "504.c4"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := -54 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, -1, 0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 8, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (2078913115487474618053437787810767570454444819079243113557275250515344520853698460834875229175004045428799740813452221406694583382159489082702570018495938006656397406997508354598608141655682545568772514960601234856728680998577004438316147088739699978078116953216773119572424051808199032749177685402474296350141700932747843529163635762513201401379947073018091108369622662708903366824775730309321266759595275773814947723476920754415076794320766483681271730836311149145817250994642881946144504400222988238362386018907509600472263673792402827 : Rat)/8269893846696429149816492110732759103198643139665847605803014370100384677950282131921669218082320787342942404729519788530063017919823015945909381941922889615806417110303604161537163503037763662890106944365148145817510407675276690337246820766827083726468412611734808426335224166921448600030833018713643001533662278748530099087825069777462212825489098781768388887678372408251208085911742561537601233231424060464542765385898677372933503765632905990850029412306306133337223528649081024788011816846127786840594693500058390971592151350535782400,            reHi := (2835451949469044440653748794335743016716301371226453433620601825196576407079384281515211719902795016381220814471860991336879470389904884555154710145751710415728109395495227606559948435544631952288430147909404164884015370544638575594469073025731146841186719843912230579167825677155945571643412098070746597856009006588386930954714608226572441039100117606555701288839850640056934395757209859783177291346360390362277239596718348134473854313898640946075452383944185708575150302005316694525091961970797777449569311962264226409837827982296541859 : Rat)/1181413406670918449973784587247537014742663305666549657971859195728626382564326018845952745440331541048991772104217112647151859702831859420844197420274698516543773872900514880219594786148251951841443849195021163688215772525039527191035260109546726246638344658819258346619317738131635514290119002673377571647666039821218585583975009968208887546498442683109769841096910344035886869415963223076800176175917722923506109340842668196133357680804700855835718487472329447619603361235583003541144545263732540977227813357151198710227450192933683200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -6, a6 := 5 }
def label : String := "504.d1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -6, a6 := 5 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, -6, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, -2, 0, -1, 0, 0, 0, -8, 0, 4, 0,                    0, 0, -2, 0, -6, 0, 0, 0, -10, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 12, 0, 0, 0, 12, 0, -2, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((10399760924081165 : Rat)/4503599627370496, (38815481312391533 : Rat)/9007199254740992),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (159498969130053955005839497850784635086736380891315 : Rat)/181032175478008020185879447595244042629453348601856,            reHi := (2077359332864505955263147769716154558394842316276563 : Rat)/362064350956016040371758895190488085258906697203712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := 26 }
def label : String := "504.d2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := 26 },   conductor := 504,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, -6, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, -2, 0, -1, 0, 0, 0, -8, 0, 4, 0,                    0, 0, -2, 0, -6, 0, 0, 0, -10, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 12, 0, 0, 0, 12, 0, -2, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   finite := ((10399760924081165 : Rat)/4503599627370496, (38815481312391533 : Rat)/9007199254740992),   tail := (123282664615426887940165205282306671142578125 : Rat)/86322868098262796490611766622182866396643328,   box := { reLo := (159498969130053955005839497850784635086736380891315 : Rat)/181032175478008020185879447595244042629453348601856,            reHi := (2077359332864505955263147769716154558394842316276563 : Rat)/362064350956016040371758895190488085258906697203712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -36291, a6 := -2661010 }
def label : String := "504.e1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -36291, a6 := -2661010 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -1, 0, 0, 0, 10, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (763944285746527550634272300999903546438692867493961561370602211364345296904082406635209270556982731820292831313590900077080047285519310009973886694859492869451598283854385937257976421529937863662920409665543890247643624191373174505150430317189764983224623291004519280196140348412076390899755394514683224627020303689421236819983719065281152317769959880446250834801009341486376913844752275091516495065563003533243830950462284902034388636177021330601120231892832979768664722301414499191334743154021549042198729583562860970802349550163084273 : Rat)/2470228032130102213581549591517577394461932366393694739395705591068946072634499857586992104102511404011528250763363053716772070287739342425401503696938005989136981734246531113186425461946344990213928048316862433166269342552355375035800998410870427606607447922985721997476755270638874257152067005589789467990574446898911588039220475388073128506314925610138609667748085264802308908778832193706036732004191602476421864985398306228278838787137101789474684110169416117750079755310764461949665867369622585679658155201316142757748304948861337600,            reHi := (42501497473707895646150729956509702167994109474327409793062979285678409579605382324260090874875684842513036368551841913856720134351467985472965293838871550784690829573767854475728844580353531723681469086848783830855876157205927515749000981069276599440440544336344647647903502623270044507008449736890295898165531384469913592225781976402225961165362544088581012809687557278172846106469614259694284854222492120633658470783933803957497028673776989776470465228568210254975914844873979446747865365997443278711108856276027553540583343868124079209 : Rat)/17291596224910715495070847140623041761233526564755863175769939137482622508441499003108944728717579828080697755343541376017404492014175396977810525878566041923958872139725717792304978233624414931497496338218037032163885397866487625250606988876092993246252135460900053982337286894472119800064469039128526275934021128292381116274543327716511899544204479270970267674236596853616162361451825355942257124029341217334953054897788143597951871509959712526322788771185912824250558287175351233647661071587358099757607086409212999304238134642029363200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3531, a6 := 9686 }
def label : String := "504.e2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],                kodaira := -16 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3531, a6 := 9686 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -1, 0, 0, 0, 10, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (763944285746527550634272300999903546438692867493961561370602211364345296904082406635209270556982731820292831313590900077080047285519310009973886694859492869451598283854385937257976421529937863662920409665543890247643624191373174505150430317189764983224623291004519280196140348412076390899755394514683224627020303689421236819983719065281152317769959880446250834801009341486376913844752275091516495065563003533243830950462284902034388636177021330601120231892832979768664722301414499191334743154021549042198729583562860970802349550163084273 : Rat)/2470228032130102213581549591517577394461932366393694739395705591068946072634499857586992104102511404011528250763363053716772070287739342425401503696938005989136981734246531113186425461946344990213928048316862433166269342552355375035800998410870427606607447922985721997476755270638874257152067005589789467990574446898911588039220475388073128506314925610138609667748085264802308908778832193706036732004191602476421864985398306228278838787137101789474684110169416117750079755310764461949665867369622585679658155201316142757748304948861337600,            reHi := (42501497473707895646150729956509702167994109474327409793062979285678409579605382324260090874875684842513036368551841913856720134351467985472965293838871550784690829573767854475728844580353531723681469086848783830855876157205927515749000981069276599440440544336344647647903502623270044507008449736890295898165531384469913592225781976402225961165362544088581012809687557278172846106469614259694284854222492120633658470783933803957497028673776989776470465228568210254975914844873979446747865365997443278711108856276027553540583343868124079209 : Rat)/17291596224910715495070847140623041761233526564755863175769939137482622508441499003108944728717579828080697755343541376017404492014175396977810525878566041923958872139725717792304978233624414931497496338218037032163885397866487625250606988876092993246252135460900053982337286894472119800064469039128526275934021128292381116274543327716511899544204479270970267674236596853616162361451825355942257124029341217334953054897788143597951871509959712526322788771185912824250558287175351233647661071587358099757607086409212999304238134642029363200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2271, a6 := -41470 }
def label : String := "504.e3"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0, 2, 0],                kodaira := -10 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2271, a6 := -41470 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -1, 0, 0, 0, 10, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (763944285746527550634272300999903546438692867493961561370602211364345296904082406635209270556982731820292831313590900077080047285519310009973886694859492869451598283854385937257976421529937863662920409665543890247643624191373174505150430317189764983224623291004519280196140348412076390899755394514683224627020303689421236819983719065281152317769959880446250834801009341486376913844752275091516495065563003533243830950462284902034388636177021330601120231892832979768664722301414499191334743154021549042198729583562860970802349550163084273 : Rat)/2470228032130102213581549591517577394461932366393694739395705591068946072634499857586992104102511404011528250763363053716772070287739342425401503696938005989136981734246531113186425461946344990213928048316862433166269342552355375035800998410870427606607447922985721997476755270638874257152067005589789467990574446898911588039220475388073128506314925610138609667748085264802308908778832193706036732004191602476421864985398306228278838787137101789474684110169416117750079755310764461949665867369622585679658155201316142757748304948861337600,            reHi := (42501497473707895646150729956509702167994109474327409793062979285678409579605382324260090874875684842513036368551841913856720134351467985472965293838871550784690829573767854475728844580353531723681469086848783830855876157205927515749000981069276599440440544336344647647903502623270044507008449736890295898165531384469913592225781976402225961165362544088581012809687557278172846106469614259694284854222492120633658470783933803957497028673776989776470465228568210254975914844873979446747865365997443278711108856276027553540583343868124079209 : Rat)/17291596224910715495070847140623041761233526564755863175769939137482622508441499003108944728717579828080697755343541376017404492014175396977810525878566041923958872139725717792304978233624414931497496338218037032163885397866487625250606988876092993246252135460900053982337286894472119800064469039128526275934021128292381116274543327716511899544204479270970267674236596853616162361451825355942257124029341217334953054897788143597951871509959712526322788771185912824250558287175351233647661071587358099757607086409212999304238134642029363200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -66, a6 := -1339 }
def label : String := "504.e4"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 0],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -66, a6 := -1339 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -1, 0, 0, 0, 10, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (763944285746527550634272300999903546438692867493961561370602211364345296904082406635209270556982731820292831313590900077080047285519310009973886694859492869451598283854385937257976421529937863662920409665543890247643624191373174505150430317189764983224623291004519280196140348412076390899755394514683224627020303689421236819983719065281152317769959880446250834801009341486376913844752275091516495065563003533243830950462284902034388636177021330601120231892832979768664722301414499191334743154021549042198729583562860970802349550163084273 : Rat)/2470228032130102213581549591517577394461932366393694739395705591068946072634499857586992104102511404011528250763363053716772070287739342425401503696938005989136981734246531113186425461946344990213928048316862433166269342552355375035800998410870427606607447922985721997476755270638874257152067005589789467990574446898911588039220475388073128506314925610138609667748085264802308908778832193706036732004191602476421864985398306228278838787137101789474684110169416117750079755310764461949665867369622585679658155201316142757748304948861337600,            reHi := (42501497473707895646150729956509702167994109474327409793062979285678409579605382324260090874875684842513036368551841913856720134351467985472965293838871550784690829573767854475728844580353531723681469086848783830855876157205927515749000981069276599440440544336344647647903502623270044507008449736890295898165531384469913592225781976402225961165362544088581012809687557278172846106469614259694284854222492120633658470783933803957497028673776989776470465228568210254975914844873979446747865365997443278711108856276027553540583343868124079209 : Rat)/17291596224910715495070847140623041761233526564755863175769939137482622508441499003108944728717579828080697755343541376017404492014175396977810525878566041923958872139725717792304978233624414931497496338218037032163885397866487625250606988876092993246252135460900053982337286894472119800064469039128526275934021128292381116274543327716511899544204479270970267674236596853616162361451825355942257124029341217334953054897788143597951871509959712526322788771185912824250558287175351233647661071587358099757607086409212999304238134642029363200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -999, a6 := -12150 }
def label : String := "504.f1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -999, a6 := -12150 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 2, 0, -1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 6, 0, -1, 0, 0, 0, 0, 0, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (4093272439688367211538799145108876776840409103919399595029492130481607381771257687219075608312323416169456206928469141462810397775084603455250088592565165616401893401890753630906017835540683917162555995803657606757486531851538837666840796904680022850369840192617914937199202954730223882458488861043356864033079811395194259428681903320488194729024553646433937076270890994070527901614679945233390461856269992258232937708057915904516623076405281951260082330455084691055834778439562414023555008126096189340446470586251335524951269097273020129 : Rat)/6558881326690271394682045467132877909433406628010844652878252776286511985960568587386151448823909589961643976164791556420394807315721702301928130505662981419432675639206306748805336571374778077464567576565462322544922047466598754405402650953000790541681844485168985993300350201351493717265833083807372035699111462455730768242068158789021754999525836964850791186779398806544061585378278583288442357390439772092568400133643778606119675400329546130674161258036035898853660039963064261038767992671066865425299239672460103184366189002149068800,            reHi := (2598018044134319547409149024818601144019873524477526511260303810380391503162746770747413330468124460058323854773894627026281475831818079826788316403542838621713935795692587396956629309568294674115336949872774143331290160654288651971589243638024240721832344880923343095863551427253574731963339743321274092001287724095339087845070066864772331272583277140244503843675114741607680632049601882141268833510616071359545185968341973767141720652530307861255121362699177394920322314430133901863673578756345716270330843683178176609566727172193144873 : Rat)/936983046670038770668863638161839701347629518287263521839750396612358855137224083912307349831987084280234853737827365202913543902245957471704018643666140202776096519886615249829333795910682582494938225223637474649274578209514107772200378707571541505954549212166997999042907171621641959609404726258196005099873066065104395463152594112717393571360833852121541598111342686649151655054039797612634622484348538870366914304806254086588525057189935161524880179719433699836237148566152037291252570381580980775042748524637157597766598428878438400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -54, a6 := -243 }
def label : String := "504.f2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -54, a6 := -243 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 2, 0, -1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 6, 0, -1, 0, 0, 0, 0, 0, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (4093272439688367211538799145108876776840409103919399595029492130481607381771257687219075608312323416169456206928469141462810397775084603455250088592565165616401893401890753630906017835540683917162555995803657606757486531851538837666840796904680022850369840192617914937199202954730223882458488861043356864033079811395194259428681903320488194729024553646433937076270890994070527901614679945233390461856269992258232937708057915904516623076405281951260082330455084691055834778439562414023555008126096189340446470586251335524951269097273020129 : Rat)/6558881326690271394682045467132877909433406628010844652878252776286511985960568587386151448823909589961643976164791556420394807315721702301928130505662981419432675639206306748805336571374778077464567576565462322544922047466598754405402650953000790541681844485168985993300350201351493717265833083807372035699111462455730768242068158789021754999525836964850791186779398806544061585378278583288442357390439772092568400133643778606119675400329546130674161258036035898853660039963064261038767992671066865425299239672460103184366189002149068800,            reHi := (2598018044134319547409149024818601144019873524477526511260303810380391503162746770747413330468124460058323854773894627026281475831818079826788316403542838621713935795692587396956629309568294674115336949872774143331290160654288651971589243638024240721832344880923343095863551427253574731963339743321274092001287724095339087845070066864772331272583277140244503843675114741607680632049601882141268833510616071359545185968341973767141720652530307861255121362699177394920322314430133901863673578756345716270330843683178176609566727172193144873 : Rat)/936983046670038770668863638161839701347629518287263521839750396612358855137224083912307349831987084280234853737827365202913543902245957471704018643666140202776096519886615249829333795910682582494938225223637474649274578209514107772200378707571541505954549212166997999042907171621641959609404726258196005099873066065104395463152594112717393571360833852121541598111342686649151655054039797612634622484348538870366914304806254086588525057189935161524880179719433699836237148566152037291252570381580980775042748524637157597766598428878438400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -54, a6 := -135 }
def label : String := "504.g1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -54, a6 := -135 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 6, 0, -6, 0, 0, 0, -2, 0, 4, 0, 0, 0, 2, 0, -1, 0, 0, 0, 8, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (19061420962388707659968630372153236463333562036320729899564922604670573679673618422579563853246345091257780933828267638429107397461620132684284417887940859675447171648287382597680275980181197404172441243331131456985979404844985748559007110441169460949196986773041848686644240361171864680548266090165734919139404560157503601248761455216706596242357813906348221291348377958515349540099036039143183212469583515582217055473336010591024635693251462426739130183455096634182972781853788418260531342437547377361403469843951568233982009665519151963 : Rat)/27172508353431124349397045506693351339081256030330642133352761501758406798979498433456913145127625444126810758396993590884492773165132766679416540666318065880506799076711842245050680081409794892353208531485486764828962768075909125393810982519574703672681927152842941972244307977027616828672737061487684147896318915888027468431425229268804413569464181711524706345228937912825397996567154130766404052046107627240640514839381368511067226658508119684221525211863577295250877308418409081446324541065848442476239707214477570335231354437474713600,            reHi := (542122708945025195330713413035248587778241514897434620229457837504729803025055740441165859885060619197466049250201732582981281933347333038567026882826057939356432400202521248154204184823280789287020828637888933834344771703135892474542911320656431272929246302466348959556626363656262773959961704774928445728167258851042912738072328583712748837800501177887718630742761611729861075103714223877645528066464583086759690937452125710906691319661244413080579196819246167739676349337096328387650857444495544274808834615297583304032228301638350246019 : Rat)/190207558474017870445779318546853459373568792212314494933469330512308847592856489034198392015893378108887675308778955136191449412155929366755915784664226461163547593536982895715354760569868564246472459720398407353802739376531363877756676877637022925708773490069900593805710155839193317800709159430413789035274232411216192279019976604881630894986249271980672944416602565389777785975970078915364828364322753390684483603875669579577470586609556837789550676483045041066756141158928863570124271787460939097333677950501342992346619481062322995200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 81, a6 := -702 }
def label : String := "504.g2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 81, a6 := -702 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 6, 0, -6, 0, 0, 0, -2, 0, 4, 0, 0, 0, 2, 0, -1, 0, 0, 0, 8, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (19061420962388707659968630372153236463333562036320729899564922604670573679673618422579563853246345091257780933828267638429107397461620132684284417887940859675447171648287382597680275980181197404172441243331131456985979404844985748559007110441169460949196986773041848686644240361171864680548266090165734919139404560157503601248761455216706596242357813906348221291348377958515349540099036039143183212469583515582217055473336010591024635693251462426739130183455096634182972781853788418260531342437547377361403469843951568233982009665519151963 : Rat)/27172508353431124349397045506693351339081256030330642133352761501758406798979498433456913145127625444126810758396993590884492773165132766679416540666318065880506799076711842245050680081409794892353208531485486764828962768075909125393810982519574703672681927152842941972244307977027616828672737061487684147896318915888027468431425229268804413569464181711524706345228937912825397996567154130766404052046107627240640514839381368511067226658508119684221525211863577295250877308418409081446324541065848442476239707214477570335231354437474713600,            reHi := (542122708945025195330713413035248587778241514897434620229457837504729803025055740441165859885060619197466049250201732582981281933347333038567026882826057939356432400202521248154204184823280789287020828637888933834344771703135892474542911320656431272929246302466348959556626363656262773959961704774928445728167258851042912738072328583712748837800501177887718630742761611729861075103714223877645528066464583086759690937452125710906691319661244413080579196819246167739676349337096328387650857444495544274808834615297583304032228301638350246019 : Rat)/190207558474017870445779318546853459373568792212314494933469330512308847592856489034198392015893378108887675308778955136191449412155929366755915784664226461163547593536982895715354760569868564246472459720398407353802739376531363877756676877637022925708773490069900593805710155839193317800709159430413789035274232411216192279019976604881630894986249271980672944416602565389777785975970078915364828364322753390684483603875669579577470586609556837789550676483045041066756141158928863570124271787460939097333677950501342992346619481062322995200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -363, a6 := 2630 }
def label : String := "504.h1"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -363, a6 := 2630 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, -8, 0, 11, 0, 0, 0, -2, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (165920501774670050722834373937259778277003164193125650527633786238155727409854028279185550393273144426721356498593586234251293809860609065757794011256494288126005584874221423097527943561593589415205617414751489280099146511239122165771339206451305052910877685890302239163764470774739445740277396129513570783461129404610506547176346383933810141212547860373723306302718298790068827891683463199419780483436272625237373923739408089211951129540003040941865085753482878737162295675696543408720668491332754214430115688183518897784726245925041781 : Rat)/190017540933084785660119199347505953420148643568745749184285045466842005587269219814384008007885492616271403904874081055136313099056872494261654130533692768395152441095887008706648112457411153093379080639758648705097641734796567310446230646990032892815957532537363230575135020818374942857851308122291497537736495915300891387632344260621009885101148123856816128288314251138639146829140937977387440923399354036647835768107562017559910675933623214574975700782262778288467673485443420149974297489970968129204473477024318673672946534527795200,            reHi := (4019434856536705955077023722974316236982235415805404885221610561494572470101248046468640139605745220541057083082521679574040099018366195322637212621041221796062849596279875265894667418316047880034643080199208783713262432411935964005760053432542933711052642145465145491574787592195820318752287297141388744260918042711248987789804881966991421362966033326301406159338746156568921478433931841403235845321924126085769698827339988042464497266604363790152121753418404308730283750836370875566342004841724552121302756736606009383026517170209161933 : Rat)/1330122786531593499620834395432541673941040504981220244289995318267894039110884538700688056055198448313899827334118567385954191693398107459831578913735849378766067087671209060946536787201878071653653564478310540935683492143575971173123614528930230249711702727761542614025945145728624600004959156856040482764155471407106239713426409824347069195708036866997712898018199757970474027803986565841712086463795478256534850376752934122919374731535362502024829905475839448019273714398103941049820082429796776904431314339170230715710625741694566400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := 110 }
def label : String := "504.h2"
def inputConductor : Nat := 504
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 504 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := 110 },   conductor := 504,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, -8, 0, 11, 0, 0, 0, -2, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4821088832709270381927490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/19284355330837081432342529296875,   geometricUpper := (6808343577350055 : Rat)/9007199254740992,   tail := (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/1138056005053010011483537364529595504375937329859463052959398931115738479031347522969069792525402090423507334946572939766826742021320544127786226514428950121334932899649568057517120471766979706551672215264136524797209754664043593765563422105925163211758492266125181076146047744039944131746278911611555637567632817459047714059472875730042757818740573529415155370212512346475154394214902563563244489350646881911972221827411842970314966411333172210908282206338732830459638892141525882319846553243727490868793947041405804679840923648,   box := { reLo := (165920501774670050722834373937259778277003164193125650527633786238155727409854028279185550393273144426721356498593586234251293809860609065757794011256494288126005584874221423097527943561593589415205617414751489280099146511239122165771339206451305052910877685890302239163764470774739445740277396129513570783461129404610506547176346383933810141212547860373723306302718298790068827891683463199419780483436272625237373923739408089211951129540003040941865085753482878737162295675696543408720668491332754214430115688183518897784726245925041781 : Rat)/190017540933084785660119199347505953420148643568745749184285045466842005587269219814384008007885492616271403904874081055136313099056872494261654130533692768395152441095887008706648112457411153093379080639758648705097641734796567310446230646990032892815957532537363230575135020818374942857851308122291497537736495915300891387632344260621009885101148123856816128288314251138639146829140937977387440923399354036647835768107562017559910675933623214574975700782262778288467673485443420149974297489970968129204473477024318673672946534527795200,            reHi := (4019434856536705955077023722974316236982235415805404885221610561494572470101248046468640139605745220541057083082521679574040099018366195322637212621041221796062849596279875265894667418316047880034643080199208783713262432411935964005760053432542933711052642145465145491574787592195820318752287297141388744260918042711248987789804881966991421362966033326301406159338746156568921478433931841403235845321924126085769698827339988042464497266604363790152121753418404308730283750836370875566342004841724552121302756736606009383026517170209161933 : Rat)/1330122786531593499620834395432541673941040504981220244289995318267894039110884538700688056055198448313899827334118567385954191693398107459831578913735849378766067087671209060946536787201878071653653564478310540935683492143575971173123614528930230249711702727761542614025945145728624600004959156856040482764155471407106239713426409824347069195708036866997712898018199757970474027803986565841712086463795478256534850376752934122919374731535362502024829905475839448019273714398103941049820082429796776904431314339170230715710625741694566400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1222651865110808668310925212306612716485614688465333504844126644586076951570988446135223055846680867110514980912237327944074758324056157744921170038081113162702215399139493347813299587619685806864402414105594609500370421552836526389989642691472051935843439779686202494824700761601659472214654412425503526231718319135255014904529137129411918936053008567195942390387429381865741755309653759166646164090596149971528977651019310980648466378818613704809854951027623212625569125809262995188169659317539006543603842146694660186767578125 : Rat)/2276112010106020022967074729059191008751874659718926105918797862231476958062695045938139585050804180847014669893145879533653484042641088255572453028857900242669865799299136115034240943533959413103344430528273049594419509328087187531126844211850326423516984532250362152292095488079888263492557823223111275135265634918095428118945751460085515637481147058830310740425024692950308788429805127126488978701293763823944443654823685940629932822666344421816564412677465660919277784283051764639693106487454981737587894082811609359681847296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N504.C504_h2
