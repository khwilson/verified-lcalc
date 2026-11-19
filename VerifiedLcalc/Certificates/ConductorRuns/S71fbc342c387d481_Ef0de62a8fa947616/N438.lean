module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -65, a6 := -231 }
def label : String := "438.a1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -65, a6 := -231 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 0, 1, -2, -1, 1, 0, 4, -1, -6, 2, 0, 1, 0, -1, -4, 0, 2, -4, 0, 1, -5, 6, -1, -2, -4,                    0, 2, -1, -4, 0, 0, 1, -10, 4, 6, 0, -2, -2, 2, 4, 0, 0, -12, -1, -3, 5, 0, -6, 0, 1, 0, 2, 4, 4, -4,                    0, -6, -2, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((12615612082030753 : Rat)/9007199254740992, (26286504932210681 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (692389150887133671373665215836966536141055805814323 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (5736319131810419564553104276307471036912246922608571 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -5, a6 := -3 }
def label : String := "438.a2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -5, a6 := -3 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 0, 1, -2, -1, 1, 0, 4, -1, -6, 2, 0, 1, 0, -1, -4, 0, 2, -4, 0, 1, -5, 6, -1, -2, -4,                    0, 2, -1, -4, 0, 0, 1, -10, 4, 6, 0, -2, -2, 2, 4, 0, 0, -12, -1, -3, 5, 0, -6, 0, 1, 0, 2, 4, 4, -4,                    0, -6, -2, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((12615612082030753 : Rat)/9007199254740992, (26286504932210681 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (692389150887133671373665215836966536141055805814323 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (5736319131810419564553104276307471036912246922608571 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -98, a6 := 362 }
def label : String := "438.b1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -98, a6 := 362 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -4, -1, 0, -1, 1, 4, 2, 1, 0, 0, -4, 1, -6, -1, -8, -4, 0, -2, -8, -1, 11, 0, 1, 0, -4,                    4, -4, -1, 2, 6, 0, 1, 2, 8, 0, 4, 10, 0, -6, 2, -4, 8, 4, 1, -7, -11, -6, 0, -8, -1, -8, 0, -8, 4,                    14, -4, -2, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((7094403170803339 : Rat)/4503599627370496, (30324451538854839 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (476182449408440857145321759897381813787560835839249 : Rat)/744235287139549353799172776534527016158939878260736,            reHi := (6403603659943443505560044925743769131988822341425749 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 2 }
def label : String := "438.b2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 2 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -4, -1, 0, -1, 1, 4, 2, 1, 0, 0, -4, 1, -6, -1, -8, -4, 0, -2, -8, -1, 11, 0, 1, 0, -4,                    4, -4, -1, 2, 6, 0, 1, 2, 8, 0, 4, 10, 0, -6, 2, -4, 8, 4, 1, -7, -11, -6, 0, -8, -1, -8, 0, -8, 4,                    14, -4, -2, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((7094403170803339 : Rat)/4503599627370496, (30324451538854839 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (476182449408440857145321759897381813787560835839249 : Rat)/744235287139549353799172776534527016158939878260736,            reHi := (6403603659943443505560044925743769131988822341425749 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -32681, a6 := 1883180 }
def label : String := "438.c1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 73, 73, 73, 73, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -32681, a6 := 1883180 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 0, -1, -4, -1, 1, 0, -6, 1, -4, 4, 0, 1, -6, -1, 8, 0, -4, 6, 0, -1, -5, 4, 1, -4, 0, 0,                    8, -1, -6, 6, 0, 1, 2, -8, -4, 0, -6, 4, 2, -6, 0, 0, 0, 1, 9, 5, -6, -4, -12, -1, 0, 4, 8, 0, 6, 0,                    -10, -8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((15512846507458087 : Rat)/9007199254740992, (32328938842844145 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (1171167078084327193588402861974667518025514912894117 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (6734852062928830842145926916896318189092046669564195 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -31106, a6 := 2108972 }
def label : String := "438.c2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -31106, a6 := 2108972 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 0, -1, -4, -1, 1, 0, -6, 1, -4, 4, 0, 1, -6, -1, 8, 0, -4, 6, 0, -1, -5, 4, 1, -4, 0, 0,                    8, -1, -6, 6, 0, 1, 2, -8, -4, 0, -6, 4, 2, -6, 0, 0, 0, 1, 9, 5, -6, -4, -12, -1, 0, 4, 8, 0, 6, 0,                    -10, -8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((15512846507458087 : Rat)/9007199254740992, (32328938842844145 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (1171167078084327193588402861974667518025514912894117 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (6734852062928830842145926916896318189092046669564195 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -9641, a6 := -337876 }
def label : String := "438.c3"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 73, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -9641, a6 := -337876 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 0, -1, -4, -1, 1, 0, -6, 1, -4, 4, 0, 1, -6, -1, 8, 0, -4, 6, 0, -1, -5, 4, 1, -4, 0, 0,                    8, -1, -6, 6, 0, 1, 2, -8, -4, 0, -6, 4, 2, -6, 0, 0, 0, 1, 9, 5, -6, -4, -12, -1, 0, 4, 8, 0, 6, 0,                    -10, -8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((15512846507458087 : Rat)/9007199254740992, (32328938842844145 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (1171167078084327193588402861974667518025514912894117 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (6734852062928830842145926916896318189092046669564195 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1946, a6 := 32780 }
def label : String := "438.c4"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1946, a6 := 32780 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 0, -1, -4, -1, 1, 0, -6, 1, -4, 4, 0, 1, -6, -1, 8, 0, -4, 6, 0, -1, -5, 4, 1, -4, 0, 0,                    8, -1, -6, 6, 0, 1, 2, -8, -4, 0, -6, 4, 2, -6, 0, 0, 0, 1, 9, 5, -6, -4, -12, -1, 0, 4, 8, 0, 6, 0,                    -10, -8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((15512846507458087 : Rat)/9007199254740992, (32328938842844145 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (1171167078084327193588402861974667518025514912894117 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (6734852062928830842145926916896318189092046669564195 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2050, a6 := -35884 }
def label : String := "438.d1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2050, a6 := -35884 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, -2, -1, 1, -2, 2, 1, 4, 2, 2, 1, 4, -1, -4, 2, -2, -2, 0, -1, -1, -4, 1, -2, 6,                    -2, -2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (11590031022277265147840337606181070965678791792474431274047982437155326263510266198392961916095562962554538568369125123793382390193058275198537621780808187450407628069219028266454055404701685315433715264455299818140586918671495315996726793815436101419120046114837805304663830070244506397346447205616349617457717562948722530844343001870372853775595495356088985402024615918196792543835016983677203511211927127218961466609040468285764555322774210859275131563930697531879302200233430605076377555402668418941078545030963294409428885571074773531 : Rat)/12713023019097340124034407799459015694587996091157364770965795198823222673290274769932475727506169325042926590531960131092050046737293865732153663403852736617762179431317044837661792871491474686342127738076789142566722948683949747940176909602229510490143591233778772338676839452074202959644858449561536170945266429580142439808688875848448982026388244755080019326399733015979329977897516867618531483570495227874146854372544899473699766938609386565993620620638560993604091000422238724462044439263055947306524485651971643321813038984383692800,            reHi := (73477551600419561981852198389159403040421217950242101644571093962477411022532660856820845406015050704408812192665245287522707190678918209626276594940695318356426945107476272014321510644369436248328043285472343418253629924394171505625940399325857720346820393472453073045334129449491131775884133997654899344554426656313560807193762634245105510038987634660770289162001442246827311063581321027863173816407398664738544875957970134891415706977017797518414844957427130902991464664963125096100714206966770313799337604418395444652393368818034444719 : Rat)/38139069057292020372103223398377047083763988273472094312897385596469668019870824309797427182518507975128779771595880393276150140211881597196460990211558209853286538293951134512985378614474424059026383214230367427700168846051849243820530728806688531470430773701336317016030518356222608878934575348684608512835799288740427319426066627545346946079164734265240057979199199047937989933692550602855594450711485683622440563117634698421099300815828159697980861861915682980812273001266716173386133317789167841919573456955914929965439116953151078400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -130, a6 := -556 }
def label : String := "438.d2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -130, a6 := -556 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, -2, -1, 1, -2, 2, 1, 4, 2, 2, 1, 4, -1, -4, 2, -2, -2, 0, -1, -1, -4, 1, -2, 6,                    -2, -2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (11590031022277265147840337606181070965678791792474431274047982437155326263510266198392961916095562962554538568369125123793382390193058275198537621780808187450407628069219028266454055404701685315433715264455299818140586918671495315996726793815436101419120046114837805304663830070244506397346447205616349617457717562948722530844343001870372853775595495356088985402024615918196792543835016983677203511211927127218961466609040468285764555322774210859275131563930697531879302200233430605076377555402668418941078545030963294409428885571074773531 : Rat)/12713023019097340124034407799459015694587996091157364770965795198823222673290274769932475727506169325042926590531960131092050046737293865732153663403852736617762179431317044837661792871491474686342127738076789142566722948683949747940176909602229510490143591233778772338676839452074202959644858449561536170945266429580142439808688875848448982026388244755080019326399733015979329977897516867618531483570495227874146854372544899473699766938609386565993620620638560993604091000422238724462044439263055947306524485651971643321813038984383692800,            reHi := (73477551600419561981852198389159403040421217950242101644571093962477411022532660856820845406015050704408812192665245287522707190678918209626276594940695318356426945107476272014321510644369436248328043285472343418253629924394171505625940399325857720346820393472453073045334129449491131775884133997654899344554426656313560807193762634245105510038987634660770289162001442246827311063581321027863173816407398664738544875957970134891415706977017797518414844957427130902991464664963125096100714206966770313799337604418395444652393368818034444719 : Rat)/38139069057292020372103223398377047083763988273472094312897385596469668019870824309797427182518507975128779771595880393276150140211881597196460990211558209853286538293951134512985378614474424059026383214230367427700168846051849243820530728806688531470430773701336317016030518356222608878934575348684608512835799288740427319426066627545346946079164734265240057979199199047937989933692550602855594450711485683622440563117634698421099300815828159697980861861915682980812273001266716173386133317789167841919573456955914929965439116953151078400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1559, a6 := -24343 }
def label : String := "438.e1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1559, a6 := -24343 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -4, 1, 1, -2, 0, -1, -2, -4, 2, 1, -6, 1, -4, -2, 4, 0, 0, -1, -1, -2, -1, -4,                    6, 2, -4, 1, 0, -6, 8, 1, 6, -4, 2, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((11461728355119429 : Rat)/9007199254740992, (52258552083621713 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (501705906842879026542550825677666930319494353177439 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (10028289015602699792096016569864547662616955125647683 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -99, a6 := -399 }
def label : String := "438.e2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -99, a6 := -399 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -4, 1, 1, -2, 0, -1, -2, -4, 2, 1, -6, 1, -4, -2, 4, 0, 0, -1, -1, -2, -1, -4,                    6, 2, -4, 1, 0, -6, 8, 1, 6, -4, 2, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((11461728355119429 : Rat)/9007199254740992, (52258552083621713 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (501705906842879026542550825677666930319494353177439 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (10028289015602699792096016569864547662616955125647683 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -19, a6 := 17 }
def label : String := "438.e3"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -19, a6 := 17 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -4, 1, 1, -2, 0, -1, -2, -4, 2, 1, -6, 1, -4, -2, 4, 0, 0, -1, -1, -2, -1, -4,                    6, 2, -4, 1, 0, -6, 8, 1, 6, -4, 2, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((11461728355119429 : Rat)/9007199254740992, (52258552083621713 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (501705906842879026542550825677666930319494353177439 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (10028289015602699792096016569864547662616955125647683 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 81, a6 := -1479 }
def label : String := "438.e4"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 73, 73, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 81, a6 := -1479 },   conductor := 438,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -4, 1, 1, -2, 0, -1, -2, -4, 2, 1, -6, 1, -4, -2, 4, 0, 0, -1, -1, -2, -1, -4,                    6, 2, -4, 1, 0, -6, 8, 1, 6, -4, 2, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   finite := ((11461728355119429 : Rat)/9007199254740992, (52258552083621713 : Rat)/9007199254740992),   tail := (1327880879454766325797542759366130828857421875 : Rat)/1419516157416437823866220048016599685972099072,   box := { reLo := (501705906842879026542550825677666930319494353177439 : Rat)/1488470574279098707598345553069054032317879756521472,            reHi := (10028289015602699792096016569864547662616955125647683 : Rat)/1488470574279098707598345553069054032317879756521472,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -13, a6 := -19 }
def label : String := "438.f1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -13, a6 := -19 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, -2, 1, 1, 0, 4, 1, 4, -2, 0, 1, -2, 1, 4, 0, -2, 4, 0, 1, -5, 4, 1, -2, 0, 0, -10,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (19556160334717432924324177817263075743734711393061417906238998378185003471813554093058619047592353313583169229276468615780468963941605376247560535128828472646298213195270318097825139591217307985573676531023513970858242202415412714187553072553776849690008782006225990581503065736330473615879240968123963056312601485335634125657502548532288569871520081216236331305877205105889064483950928867261888558144538702138223760383959059925630796079059982799481709753869258001406994425939942754058225504734299143210247706770604291367106038818530131 : Rat)/9741780091262329596961232030236793635699613862955835073537007815190208945050018980791169139851470747159330720714145694323409997499842042706631159696438878634300520637024555431158461970491551483787071063660374821890209156079654979264503379005539854781719226999064193362970758200823144030379201877058648406854610290866009532420451245860880445997232371459831432434022783920290674312565147024995043282429498258907392225572831340592873384627286886257466375954512307274792406896875278716062869302117284250809597307013005090668055968570408960,            reHi := (794964318924182840806505268922555782821381561511492839810789424419603594314521255291875887176463016532226223849641034043144386301839184452670363689987210850824310320224105938705573689580574128509188356636777964356210276225712305596056084745337421670325058708990799835148640353737352613642165500818903798851867232670705952876704599559560594649788869178572860977024260770273296457502101919099779304723830763713247323127137013205270988343851177555007662135701225187150232446790316836165741791534051282558551054868652900748525906681944933951 : Rat)/263028062464082899117953264816393428163889574299807546985499211010135641516350512481361566775989710173301929459281933746732069932495735153079041311803849723126114057199662996641278473203271890062250918718830120191035647214150684440141591233149576079106419128974733220800210471422224888820238450680583506985074477853382257375352183638243772041925274029415448675718615165847848206439258969674866168625596452990499590090466446196007581384936745928951592150771832296419394986215632525333697471157166674771859127289351137448037511151401041920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := -45 }
def label : String := "438.f2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := -45 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, -2, 1, 1, 0, 4, 1, 4, -2, 0, 1, -2, 1, 4, 0, -2, 4, 0, 1, -5, 4, 1, -2, 0, 0, -10,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (19556160334717432924324177817263075743734711393061417906238998378185003471813554093058619047592353313583169229276468615780468963941605376247560535128828472646298213195270318097825139591217307985573676531023513970858242202415412714187553072553776849690008782006225990581503065736330473615879240968123963056312601485335634125657502548532288569871520081216236331305877205105889064483950928867261888558144538702138223760383959059925630796079059982799481709753869258001406994425939942754058225504734299143210247706770604291367106038818530131 : Rat)/9741780091262329596961232030236793635699613862955835073537007815190208945050018980791169139851470747159330720714145694323409997499842042706631159696438878634300520637024555431158461970491551483787071063660374821890209156079654979264503379005539854781719226999064193362970758200823144030379201877058648406854610290866009532420451245860880445997232371459831432434022783920290674312565147024995043282429498258907392225572831340592873384627286886257466375954512307274792406896875278716062869302117284250809597307013005090668055968570408960,            reHi := (794964318924182840806505268922555782821381561511492839810789424419603594314521255291875887176463016532226223849641034043144386301839184452670363689987210850824310320224105938705573689580574128509188356636777964356210276225712305596056084745337421670325058708990799835148640353737352613642165500818903798851867232670705952876704599559560594649788869178572860977024260770273296457502101919099779304723830763713247323127137013205270988343851177555007662135701225187150232446790316836165741791534051282558551054868652900748525906681944933951 : Rat)/263028062464082899117953264816393428163889574299807546985499211010135641516350512481361566775989710173301929459281933746732069932495735153079041311803849723126114057199662996641278473203271890062250918718830120191035647214150684440141591233149576079106419128974733220800210471422224888820238450680583506985074477853382257375352183638243772041925274029415448675718615165847848206439258969674866168625596452990499590090466446196007581384936745928951592150771832296419394986215632525333697471157166674771859127289351137448037511151401041920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -72938, a6 := -7587996 }
def label : String := "438.g1"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 73, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -72938, a6 := -7587996 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 2, 1, 1, 0, 0, 1, -4, 2, 0, 1, 6, 1, -4, 0, 2, 0, 0, 1, -5, -4, 1, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (5598315046432570240781962207706412869884952440832492807003425556247082688012988619886318033469548250356404756816054954591412477146053585111801907674394688631116519998974745980066285108898854948901129792688971522132718357675371319382063028073471907862139137685184583234921171485002552131556497919756743499048545327193625092605435168000548928515785920216946635233363853228973434199536140514116535041910647542405625327188419936115082383291220667260122412113057182768904811630557209454728728341001267579489248146204787599553601515716045963 : Rat)/2656849115798817162807608735519125537008985598987955020055547585960966075922732449306682492686764749225272014740221552997293635681775102556353952644483330536627414719188515117588671446497695859214655744634647678697329769839905903435773648819692687667741607363381143644446570418406312008285236875561449565505802806599820781569213976143876485271972464943590390663824395614624729357972312824998648167935317706974743334247135820161692741261987332615672647987594265620397929153693257831653509809668350250220799265549001388364015264155566080,            reHi := (74652834498512415681870779243590516300478643424734406493410880863270732738554913615648904765090471129802306535787057640189318299543118560108876774784920558036640667352464846062282183712310162835923161005220805480792635221055301262545152199202231044925489770286904464776170595513262119638596816872016570135497563280674311051380347017491771975126697897302954964684066118490467725962723818472759492475074152282125545896886085702700231151725319987582098565046424465116843125252973456137803145222962893171907237571727442426305939329375612701 : Rat)/23911642042189354465268478619672129833080870390891595180499928273648694683304592043760142434180882743027448132661993976975642721135975923007185573800349974829646732472696636058298043018479262732931901701711829108275967928559153130921962839377234189009674466270430292800019133765656808074567131880053046089552225259398387034122925785294888367447752184492313515974419560531622564221750815424987833511417859362772690008224222381455234671357885993541053831888348390583581362383239320484881588287015152251987193389941012495276137377400094720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -72898, a6 := -7596724 }
def label : String := "438.g2"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 73, 73, 73, 73, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -72898, a6 := -7596724 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 2, 1, 1, 0, 0, 1, -4, 2, 0, 1, 6, 1, -4, 0, 2, 0, 0, 1, -5, -4, 1, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (5598315046432570240781962207706412869884952440832492807003425556247082688012988619886318033469548250356404756816054954591412477146053585111801907674394688631116519998974745980066285108898854948901129792688971522132718357675371319382063028073471907862139137685184583234921171485002552131556497919756743499048545327193625092605435168000548928515785920216946635233363853228973434199536140514116535041910647542405625327188419936115082383291220667260122412113057182768904811630557209454728728341001267579489248146204787599553601515716045963 : Rat)/2656849115798817162807608735519125537008985598987955020055547585960966075922732449306682492686764749225272014740221552997293635681775102556353952644483330536627414719188515117588671446497695859214655744634647678697329769839905903435773648819692687667741607363381143644446570418406312008285236875561449565505802806599820781569213976143876485271972464943590390663824395614624729357972312824998648167935317706974743334247135820161692741261987332615672647987594265620397929153693257831653509809668350250220799265549001388364015264155566080,            reHi := (74652834498512415681870779243590516300478643424734406493410880863270732738554913615648904765090471129802306535787057640189318299543118560108876774784920558036640667352464846062282183712310162835923161005220805480792635221055301262545152199202231044925489770286904464776170595513262119638596816872016570135497563280674311051380347017491771975126697897302954964684066118490467725962723818472759492475074152282125545896886085702700231151725319987582098565046424465116843125252973456137803145222962893171907237571727442426305939329375612701 : Rat)/23911642042189354465268478619672129833080870390891595180499928273648694683304592043760142434180882743027448132661993976975642721135975923007185573800349974829646732472696636058298043018479262732931901701711829108275967928559153130921962839377234189009674466270430292800019133765656808074567131880053046089552225259398387034122925785294888367447752184492313515974419560531622564221750815424987833511417859362772690008224222381455234671357885993541053831888348390583581362383239320484881588287015152251987193389941012495276137377400094720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -938, a6 := -9564 }
def label : String := "438.g3"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -938, a6 := -9564 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 2, 1, 1, 0, 0, 1, -4, 2, 0, 1, 6, 1, -4, 0, 2, 0, 0, 1, -5, -4, 1, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (5598315046432570240781962207706412869884952440832492807003425556247082688012988619886318033469548250356404756816054954591412477146053585111801907674394688631116519998974745980066285108898854948901129792688971522132718357675371319382063028073471907862139137685184583234921171485002552131556497919756743499048545327193625092605435168000548928515785920216946635233363853228973434199536140514116535041910647542405625327188419936115082383291220667260122412113057182768904811630557209454728728341001267579489248146204787599553601515716045963 : Rat)/2656849115798817162807608735519125537008985598987955020055547585960966075922732449306682492686764749225272014740221552997293635681775102556353952644483330536627414719188515117588671446497695859214655744634647678697329769839905903435773648819692687667741607363381143644446570418406312008285236875561449565505802806599820781569213976143876485271972464943590390663824395614624729357972312824998648167935317706974743334247135820161692741261987332615672647987594265620397929153693257831653509809668350250220799265549001388364015264155566080,            reHi := (74652834498512415681870779243590516300478643424734406493410880863270732738554913615648904765090471129802306535787057640189318299543118560108876774784920558036640667352464846062282183712310162835923161005220805480792635221055301262545152199202231044925489770286904464776170595513262119638596816872016570135497563280674311051380347017491771975126697897302954964684066118490467725962723818472759492475074152282125545896886085702700231151725319987582098565046424465116843125252973456137803145222962893171907237571727442426305939329375612701 : Rat)/23911642042189354465268478619672129833080870390891595180499928273648694683304592043760142434180882743027448132661993976975642721135975923007185573800349974829646732472696636058298043018479262732931901701711829108275967928559153130921962839377234189009674466270430292800019133765656808074567131880053046089552225259398387034122925785294888367447752184492313515974419560531622564221750815424987833511417859362772690008224222381455234671357885993541053831888348390583581362383239320484881588287015152251987193389941012495276137377400094720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 1622, a6 := -52060 }
def label : String := "438.g4"
def inputConductor : Nat := 438
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 73, 73] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 438 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 1622, a6 := -52060 },   conductor := 438,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 2, 1, 1, 0, 0, 1, -4, 2, 0, 1, 6, 1, -4, 0, 2, 0, 0, 1, -5, -4, 1, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17977401263013276386260986328125,   alphaHi := (1349303770452201895863057907712 : Rat)/4494350315753319072723388671875,   geometricUpper := (6671214770447311 : Rat)/9007199254740992,   tail := (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/3693376866496816123899338623515684935823043697462247457869268422351920923497761813439376236610247720840575258030070761998309090340339752356422006720580701512643152156012699039540520947929319820137005712943744991968262915861995681458770216123739582914891266986927377504078751685059966231256107034164563484657509583724059444320556576577456867988646030045791564198239249903906595989424293742308940881672217065252543367665666910164929334281387260275764605775443648296596157882677200869742352259549666368094750527276520477878120349696,   box := { reLo := (5598315046432570240781962207706412869884952440832492807003425556247082688012988619886318033469548250356404756816054954591412477146053585111801907674394688631116519998974745980066285108898854948901129792688971522132718357675371319382063028073471907862139137685184583234921171485002552131556497919756743499048545327193625092605435168000548928515785920216946635233363853228973434199536140514116535041910647542405625327188419936115082383291220667260122412113057182768904811630557209454728728341001267579489248146204787599553601515716045963 : Rat)/2656849115798817162807608735519125537008985598987955020055547585960966075922732449306682492686764749225272014740221552997293635681775102556353952644483330536627414719188515117588671446497695859214655744634647678697329769839905903435773648819692687667741607363381143644446570418406312008285236875561449565505802806599820781569213976143876485271972464943590390663824395614624729357972312824998648167935317706974743334247135820161692741261987332615672647987594265620397929153693257831653509809668350250220799265549001388364015264155566080,            reHi := (74652834498512415681870779243590516300478643424734406493410880863270732738554913615648904765090471129802306535787057640189318299543118560108876774784920558036640667352464846062282183712310162835923161005220805480792635221055301262545152199202231044925489770286904464776170595513262119638596816872016570135497563280674311051380347017491771975126697897302954964684066118490467725962723818472759492475074152282125545896886085702700231151725319987582098565046424465116843125252973456137803145222962893171907237571727442426305939329375612701 : Rat)/23911642042189354465268478619672129833080870390891595180499928273648694683304592043760142434180882743027448132661993976975642721135975923007185573800349974829646732472696636058298043018479262732931901701711829108275967928559153130921962839377234189009674466270430292800019133765656808074567131880053046089552225259398387034122925785294888367447752184492313515974419560531622564221750815424987833511417859362772690008224222381455234671357885993541053831888348390583581362383239320484881588287015152251987193389941012495276137377400094720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1874209772845832692371737232721957083026673849730179551839101609457924394748922647457677507902428656103888562305473158200149255289810181596637698299532385800680169608894003457292915285887545159365783680279628263846762657782201362301649899283807138996602079862270422711326576924490538971185453199179241427227891828829171035173157395523954849387157942269355563945430609018665328330496893465943081435920181365706902297522917066428487541209279980485827491252482190484957431676116800138363376731470580313034208411986281170043480841551 : Rat)/7386753732993632247798677247031369871646087394924494915738536844703841846995523626878752473220495441681150516060141523996618180680679504712844013441161403025286304312025398079081041895858639640274011425887489983936525831723991362917540432247479165829782533973854755008157503370119932462512214068329126969315019167448118888641113153154913735977292060091583128396478499807813191978848587484617881763344434130505086735331333820329858668562774520551529211550887296593192315765354401739484704519099332736189501054553040955756240699392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N438.C438_g4
