module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -563, a6 := -5138 }
def label : String := "520.a1"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -563, a6 := -5138 },   conductor := 520,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, -3, 0, -4, 0, -1, 0, 0, 0, -6, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -4,                    0, 0, 0, 0, 0, -6, 0, 0, 0, -6, 0, 8, 0, 3, 0, 0, 0, -7, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -10, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   finite := ((21754605774784099 : Rat)/9007199254740992, (40115633136385777 : Rat)/9007199254740992),   tail := (67113789992662492119772598906421661376953125 : Rat)/42851341237728242614955474783255132345729024,   box := { reLo := (152600350018019686116885911160372445216777900125337 : Rat)/179731551958768518912878207705306134618220628279296,            reHi := (1081971434736409434417943385667823546118406792377251 : Rat)/179731551958768518912878207705306134618220628279296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -43, a6 := -42 }
def label : String := "520.a2"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -43, a6 := -42 },   conductor := 520,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, -3, 0, -4, 0, -1, 0, 0, 0, -6, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -4,                    0, 0, 0, 0, 0, -6, 0, 0, 0, -6, 0, 8, 0, 3, 0, 0, 0, -7, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -10, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   finite := ((21754605774784099 : Rat)/9007199254740992, (40115633136385777 : Rat)/9007199254740992),   tail := (67113789992662492119772598906421661376953125 : Rat)/42851341237728242614955474783255132345729024,   box := { reLo := (152600350018019686116885911160372445216777900125337 : Rat)/179731551958768518912878207705306134618220628279296,            reHi := (1081971434736409434417943385667823546118406792377251 : Rat)/179731551958768518912878207705306134618220628279296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -23, a6 := 42 }
def label : String := "520.a3"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -23, a6 := 42 },   conductor := 520,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, -3, 0, -4, 0, -1, 0, 0, 0, -6, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -4,                    0, 0, 0, 0, 0, -6, 0, 0, 0, -6, 0, 8, 0, 3, 0, 0, 0, -7, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -10, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   finite := ((21754605774784099 : Rat)/9007199254740992, (40115633136385777 : Rat)/9007199254740992),   tail := (67113789992662492119772598906421661376953125 : Rat)/42851341237728242614955474783255132345729024,   box := { reLo := (152600350018019686116885911160372445216777900125337 : Rat)/179731551958768518912878207705306134618220628279296,            reHi := (1081971434736409434417943385667823546118406792377251 : Rat)/179731551958768518912878207705306134618220628279296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 157, a6 := -322 }
def label : String := "520.a4"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 157, a6 := -322 },   conductor := 520,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, -3, 0, -4, 0, -1, 0, 0, 0, -6, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -4,                    0, 0, 0, 0, 0, -6, 0, 0, 0, -6, 0, 8, 0, 3, 0, 0, 0, -7, 0, 0, 0, 2, 0, 4, 0, 0, 0, 4, 0, -10, 0, 0,                    0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   finite := ((21754605774784099 : Rat)/9007199254740992, (40115633136385777 : Rat)/9007199254740992),   tail := (67113789992662492119772598906421661376953125 : Rat)/42851341237728242614955474783255132345729024,   box := { reLo := (152600350018019686116885911160372445216777900125337 : Rat)/179731551958768518912878207705306134618220628279296,            reHi := (1081971434736409434417943385667823546118406792377251 : Rat)/179731551958768518912878207705306134618220628279296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -28 }
def label : String := "520.b1"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -28 },   conductor := 520,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 1, 0, -4, 0, -6, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   geometricUpper := (854744000126177 : Rat)/1125899906842624,   tail := (6677990099674975285249972312483555709220326044929191566497399085968382828301723956752416472757432252297813689420836197387087977232761129537032949934293266262148535268321651060283082424486844931056666269449688628785523887179405483400818934000196486172069897914845249062649238498441035559174742180014034242842798883292773000895721086899185247095953954998607668634916709215206096523586004248748522000910999113894658517094837964766950563658207959013190904771153556341665464397738627760873653251244540257 : Rat)/5291492957907923724823336591657775775586912693559129993614770071824506441136849418185878881573016304077294054345876817002147983793993830635056507086409743773778988922488740794619641493558963295926200553414756837332981418728837932532638432370654140192829374438754410639518290943011925205188091565343136263053411001707452557782933070177938311109474402581170289137183217402888419387107713918616275867295033505573443718160592973609759822723154612151383635419403094140003310990329581704868966497058291712,   box := { reLo := (177502081986254589846857222722488111941847911659312381411722007499567569022133169521731916773752949589407740483268303057815600792673714166664407130539517323490770689678406913024698281470531668746534361278687305287986655922708961417214382740536802246699688413036484126816444148581820409029402124356954296262820539195949364448976921042086715393143075645394327010858414257521269829847599712999253681074160165114220727187563571973702631965132979968112389142909194710130108048817851091808055442098688152725888754063 : Rat)/179537214105584770205846103578263620469852798573376662610937189926906105951461214726283587131539537179586633768678481177875865639711133394760681954764387373298711818520895524409379110598827786657344946197629095643466972146427565335089032442951114091580607677445129781598678131723189935306143236253023401784667640748816326442932421510053701990623787451415715276036194135515090669733343153375818213798117383735587173485645168788486245649857898549166616561962225828098089361435899424298827224674606047000998707200,            reHi := (630662559703055716673585673338786588998534973914987723860262103392078535329521350287104577924510773480660141271221178595408691667578191789510777380370570146556088313893227197740145876266417244514784512284367552442597838386052244002674724875924822493869483669699260477080933192565191747880943808005678182850084603988235715551233671447262643025046101909912085769045148731214397660550163679093533098266121696224603237443302515515519743539217218175620777026602841420050792883740473218102165373104113933653048237681 : Rat)/179537214105584770205846103578263620469852798573376662610937189926906105951461214726283587131539537179586633768678481177875865639711133394760681954764387373298711818520895524409379110598827786657344946197629095643466972146427565335089032442951114091580607677445129781598678131723189935306143236253023401784667640748816326442932421510053701990623787451415715276036194135515090669733343153375818213798117383735587173485645168788486245649857898549166616561962225828098089361435899424298827224674606047000998707200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (6677990099674975285249972312483555709220326044929191566497399085968382828301723956752416472757432252297813689420836197387087977232761129537032949934293266262148535268321651060283082424486844931056666269449688628785523887179405483400818934000196486172069897914845249062649238498441035559174742180014034242842798883292773000895721086899185247095953954998607668634916709215206096523586004248748522000910999113894658517094837964766950563658207959013190904771153556341665464397738627760873653251244540257 : Rat)/10582985915815847449646673183315551551173825387118259987229540143649012882273698836371757763146032608154588108691753634004295967587987661270113014172819487547557977844977481589239282987117926591852401106829513674665962837457675865065276864741308280385658748877508821279036581886023850410376183130686272526106822003414905115565866140355876622218948805162340578274366434805776838774215427837232551734590067011146887436321185947219519645446309224302767270838806188280006621980659163409737932994116583424, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -100 }
def label : String := "520.b2"
def inputConductor : Nat := 520
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 520 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -100 },   conductor := 520,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, 1, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 1, 0, -4, 0, -6, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/19588064650014780712127685546875,   geometricUpper := (854744000126177 : Rat)/1125899906842624,   tail := (6677990099674975285249972312483555709220326044929191566497399085968382828301723956752416472757432252297813689420836197387087977232761129537032949934293266262148535268321651060283082424486844931056666269449688628785523887179405483400818934000196486172069897914845249062649238498441035559174742180014034242842798883292773000895721086899185247095953954998607668634916709215206096523586004248748522000910999113894658517094837964766950563658207959013190904771153556341665464397738627760873653251244540257 : Rat)/5291492957907923724823336591657775775586912693559129993614770071824506441136849418185878881573016304077294054345876817002147983793993830635056507086409743773778988922488740794619641493558963295926200553414756837332981418728837932532638432370654140192829374438754410639518290943011925205188091565343136263053411001707452557782933070177938311109474402581170289137183217402888419387107713918616275867295033505573443718160592973609759822723154612151383635419403094140003310990329581704868966497058291712,   box := { reLo := (177502081986254589846857222722488111941847911659312381411722007499567569022133169521731916773752949589407740483268303057815600792673714166664407130539517323490770689678406913024698281470531668746534361278687305287986655922708961417214382740536802246699688413036484126816444148581820409029402124356954296262820539195949364448976921042086715393143075645394327010858414257521269829847599712999253681074160165114220727187563571973702631965132979968112389142909194710130108048817851091808055442098688152725888754063 : Rat)/179537214105584770205846103578263620469852798573376662610937189926906105951461214726283587131539537179586633768678481177875865639711133394760681954764387373298711818520895524409379110598827786657344946197629095643466972146427565335089032442951114091580607677445129781598678131723189935306143236253023401784667640748816326442932421510053701990623787451415715276036194135515090669733343153375818213798117383735587173485645168788486245649857898549166616561962225828098089361435899424298827224674606047000998707200,            reHi := (630662559703055716673585673338786588998534973914987723860262103392078535329521350287104577924510773480660141271221178595408691667578191789510777380370570146556088313893227197740145876266417244514784512284367552442597838386052244002674724875924822493869483669699260477080933192565191747880943808005678182850084603988235715551233671447262643025046101909912085769045148731214397660550163679093533098266121696224603237443302515515519743539217218175620777026602841420050792883740473218102165373104113933653048237681 : Rat)/179537214105584770205846103578263620469852798573376662610937189926906105951461214726283587131539537179586633768678481177875865639711133394760681954764387373298711818520895524409379110598827786657344946197629095643466972146427565335089032442951114091580607677445129781598678131723189935306143236253023401784667640748816326442932421510053701990623787451415715276036194135515090669733343153375818213798117383735587173485645168788486245649857898549166616561962225828098089361435899424298827224674606047000998707200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (6677990099674975285249972312483555709220326044929191566497399085968382828301723956752416472757432252297813689420836197387087977232761129537032949934293266262148535268321651060283082424486844931056666269449688628785523887179405483400818934000196486172069897914845249062649238498441035559174742180014034242842798883292773000895721086899185247095953954998607668634916709215206096523586004248748522000910999113894658517094837964766950563658207959013190904771153556341665464397738627760873653251244540257 : Rat)/10582985915815847449646673183315551551173825387118259987229540143649012882273698836371757763146032608154588108691753634004295967587987661270113014172819487547557977844977481589239282987117926591852401106829513674665962837457675865065276864741308280385658748877508821279036581886023850410376183130686272526106822003414905115565866140355876622218948805162340578274366434805776838774215427837232551734590067011146887436321185947219519645446309224302767270838806188280006621980659163409737932994116583424, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N520.C520_b2
