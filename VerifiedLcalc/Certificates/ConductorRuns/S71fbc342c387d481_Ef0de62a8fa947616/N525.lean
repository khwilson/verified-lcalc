module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2813, a6 := -58594 }
def label : String := "525.a1"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2813, a6 := -58594 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, -1, 3, 1, 0, 0, 1, 6, 1, 0, -1, -2, -1, -8, 0, 1, 0, -8, -3, 0, -6, -1, 1, -2,                    0, 4, -5, 0, 2, 0, -1, 2, 8, -6, 0, -6, -1, -4, 0, 0, 8, -8, 1, 1, 0, 2, -6, -10, 1, 0, -3, 8, 2, 4,                    0, -2, -4, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((7499226519467979 : Rat)/4503599627370496, (23245533588738635 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (19469552269400775877039854694802313338403170433411 : Rat)/358638369652055006350474041120263576266047817252864,            reHi := (3006571630870951535120009368453391459278516216051715 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -188, a6 := -844 }
def label : String := "525.a2"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -188, a6 := -844 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, -1, 3, 1, 0, 0, 1, 6, 1, 0, -1, -2, -1, -8, 0, 1, 0, -8, -3, 0, -6, -1, 1, -2,                    0, 4, -5, 0, 2, 0, -1, 2, 8, -6, 0, -6, -1, -4, 0, 0, 8, -8, 1, 1, 0, 2, -6, -10, 1, 0, -3, 8, 2, 4,                    0, -2, -4, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((7499226519467979 : Rat)/4503599627370496, (23245533588738635 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (19469552269400775877039854694802313338403170433411 : Rat)/358638369652055006350474041120263576266047817252864,            reHi := (3006571630870951535120009368453391459278516216051715 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -63, a6 := 156 }
def label : String := "525.a3"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -63, a6 := 156 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, -1, 3, 1, 0, 0, 1, 6, 1, 0, -1, -2, -1, -8, 0, 1, 0, -8, -3, 0, -6, -1, 1, -2,                    0, 4, -5, 0, 2, 0, -1, 2, 8, -6, 0, -6, -1, -4, 0, 0, 8, -8, 1, 1, 0, 2, -6, -10, 1, 0, -3, 8, 2, 4,                    0, -2, -4, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((7499226519467979 : Rat)/4503599627370496, (23245533588738635 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (19469552269400775877039854694802313338403170433411 : Rat)/358638369652055006350474041120263576266047817252864,            reHi := (3006571630870951535120009368453391459278516216051715 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 437, a6 := -4594 }
def label : String := "525.a4"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 437, a6 := -4594 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, -1, 3, 1, 0, 0, 1, 6, 1, 0, -1, -2, -1, -8, 0, 1, 0, -8, -3, 0, -6, -1, 1, -2,                    0, 4, -5, 0, 2, 0, -1, 2, 8, -6, 0, -6, -1, -4, 0, 0, 8, -8, 1, 1, 0, 2, -6, -10, 1, 0, -3, 8, 2, 4,                    0, -2, -4, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((7499226519467979 : Rat)/4503599627370496, (23245533588738635 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (19469552269400775877039854694802313338403170433411 : Rat)/358638369652055006350474041120263576266047817252864,            reHi := (3006571630870951535120009368453391459278516216051715 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -18, a6 := 27 }
def label : String := "525.b1"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -18, a6 := 27 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, 0, -1, -1, 3, 1, 0, -6, -1, -2, 1, 0, -1, 4, -1, -6, 0, -1, 6, 0, 3, 0, 2, 1, 1, -2, 0,                    -10, -5, -6, -4, 0, -1, -4, 6, -2, 0, 2, 1, -4, 6, 0, 0, 0, -1, 1, 0, 4, 2, 6, -1, 0, -3, -6, 2, -8,                    0, -2, 10, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((2161139310692723 : Rat)/1125899906842624, (8414674194447245 : Rat)/2251799813685248),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (27669123196145082994397266261378809946591445433707 : Rat)/89659592413013751587618510280065894066511954313216,            reHi := (958952625390304200831124485868003245670894258573205 : Rat)/179319184826027503175237020560131788133023908626432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 7, a6 := 102 }
def label : String := "525.b2"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 7, a6 := 102 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, 0, -1, -1, 3, 1, 0, -6, -1, -2, 1, 0, -1, 4, -1, -6, 0, -1, 6, 0, 3, 0, 2, 1, 1, -2, 0,                    -10, -5, -6, -4, 0, -1, -4, 6, -2, 0, 2, 1, -4, 6, 0, 0, 0, -1, 1, 0, 4, 2, 6, -1, 0, -3, -6, 2, -8,                    0, -2, 10, -1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((2161139310692723 : Rat)/1125899906842624, (8414674194447245 : Rat)/2251799813685248),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (27669123196145082994397266261378809946591445433707 : Rat)/89659592413013751587618510280065894066511954313216,            reHi := (958952625390304200831124485868003245670894258573205 : Rat)/179319184826027503175237020560131788133023908626432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -450, a6 := 3375 }
def label : String := "525.c1"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -450, a6 := 3375 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, -6, 1, 2, 1, 0, -1, -4, 1, -6, 0, -1, -6, 0, 3, 0, 2, -1, -1, -2,                    0, -10, 5, 6, -4, 0, -1, 4, -6, -2, 0, 2, -1, 4, 6, 0, 0, 0, 1, 1, 0, 4, -2, -6, -1, 0, -3, 6, -2,                    -8, 0, -2, -10, 1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((24379146909229489 : Rat)/9007199254740992, (47142795334590787 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (785958607649336420006612216460965385248819043591001 : Rat)/717276739304110012700948082240527152532095634505728,            reHi := (4909599364418584077523670438127783731546582476221883 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 175, a6 := 12750 }
def label : String := "525.c2"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 175, a6 := 12750 },   conductor := 525,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, -6, 1, 2, 1, 0, -1, -4, 1, -6, 0, -1, -6, 0, 3, 0, 2, -1, -1, -2,                    0, -10, 5, 6, -4, 0, -1, 4, -6, -2, 0, 2, -1, 4, 6, 0, 0, 0, 1, 1, 0, 4, -2, -6, -1, 0, -3, 6, -2,                    -8, 0, -2, -10, 1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   finite := ((24379146909229489 : Rat)/9007199254740992, (47142795334590787 : Rat)/9007199254740992),   tail := (68869795305119250702090959706974029541015625 : Rat)/42753025251871944230851416721375414880043008,   box := { reLo := (785958607649336420006612216460965385248819043591001 : Rat)/717276739304110012700948082240527152532095634505728,            reHi := (4909599364418584077523670438127783731546582476221883 : Rat)/717276739304110012700948082240527152532095634505728,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -19600, a6 := -1064375 }
def label : String := "525.d1"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -19600, a6 := -1064375 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1225, a6 := -17000 }
def label : String := "525.d2"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1225, a6 := -17000 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -975, a6 := 11250 }
def label : String := "525.d3"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -975, a6 := 11250 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -850, a6 := -27125 }
def label : String := "525.d4"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -850, a6 := -27125 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -100, a6 := -125 }
def label : String := "525.d5"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -100, a6 := -125 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 25, a6 := 0 }
def label : String := "525.d6"
def inputConductor : Nat := 525
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 525 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 25, a6 := 0 },   conductor := 525,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, -1, 0, -1, 1, -3, 1, 0, 4, 1, 2, 1, 0, -1, 6, 1, 4, 0, -1, 4, 0, 3, 0, 2, -1, -1, -2, 0, 0,                    5],   alphaLo := (337325942613050473964690735104 : Rat)/1230125796329987812042236328125,   alphaHi := (5397215081808807583452231630848 : Rat)/19682012741279804897308349609375,   geometricUpper := (6846951292591203 : Rat)/9007199254740992,   tail := (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/370617621806411216881907642973252983231644039681741156116285445226190433256862671665342709271943353578940912440714003515701333258322898178574128191113335196177792504470398027872391236088999069640400248032236318559729489955245025916144627043790831335421785962543881904744321028331636616486168769256102356808124644971197465045993659679294985281028548899694763760876282857114460005629477484848764904766971273149407617197611649778080195605112937457721882881312894916264023513546111509947041410001782215340448278628084360390366986240,   box := { reLo := (133447104744107330523009826445363584186693492289701217168879237929281023349243899627744035652463976041467282209693660147957280876681394652052329016037707714017867495766792709683192814156189377148688016153996782375463924057576480085637566918937594493466978859947068875715985662984491856308398118468966270542255691070903777842823244407464435918020018833946525698066818202197851812722906521110535689820594693798940610088337610737264809576339036825695610893263114051085062368094770748735246680748371588472825660441317345205381438300787339 : Rat)/462198348007640847807077667274872715147132976819218441016087927597917767885933208421863888761168372078357948727551755926441679810454261287194330989522013663158913565702546791753742727700299006745752070521746009584794326111655937555101712820192677130898515539246362755052356987395469019329750530645593017482482669117515272251253830967027814028926546418456038970480094979956014416400538259787349259029604175658445687629993081273193146179723159642337333306933955188757612515813896302389485183537452606097719069621919890095907839640862720,            reHi := (1056610225991813534192727503209809803297332353159805953455146638968258774014000598250698881360563760549023102771418398902772660584454186989250963463395264499476458060573186685901032936729244760619882684557796686843856963870129134940974638843151782998184984150680990556091553475157738340923496760447080604988040646440545909215248200722022767910938403998886314539723306753762159349677141045976599176037361766859686018113240981601843223564226372120935314678685719045622491867925028362025873690236972442839784635820575606531108026405413723 : Rat)/359487604005942881627727074547123222892214537526058787456957277020602708355725828772560802369797622727611737899206921276121306519242203223373368547406010626901377217768647504697355454878010338580029388183580229677062253642399062542856887749038748879587734308302726587262944323529809237256472634946572346930819853758067433973197424085466077578053980547688030310373407206632455657200418646501271645911914358845457757045550174323594669250895790832929037016504187369033698623410808235191821809418018693631559276372604358963483875276226560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (491159013026737347233478972271582651465119217022375119896996728519262633274994696785844972101460398747668980456966005458788593507457802051043359648441273965640586647788444187908851522076202100532813766992686376453777152237202895417689291303308039021639271145786858866555251093962852514591138032750722779382326535076915335807628074567767484270716616231321348104827837539394412874109321358656895815092119355621759645164756830714590885837294927192135028089326146285866750385058669191871533577517271796858741301451661986188256568587 : Rat)/741235243612822433763815285946505966463288079363482312232570890452380866513725343330685418543886707157881824881428007031402666516645796357148256382226670392355585008940796055744782472177998139280800496064472637119458979910490051832289254087581662670843571925087763809488642056663273232972337538512204713616249289942394930091987319358589970562057097799389527521752565714228920011258954969697529809533942546298815234395223299556160391210225874915443765762625789832528047027092223019894082820003564430680896557256168720780733972480, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N525.C525_d6
