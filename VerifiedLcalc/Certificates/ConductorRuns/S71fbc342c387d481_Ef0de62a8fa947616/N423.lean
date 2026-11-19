module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -9, a6 := 10 }
def label : String := "423.a1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -9, a6 := 10 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -2, 0, 2, -3, 0, 1, 0, 0, 6, 3, 0, 0, -2, 0, -4, 0, 0, -4, -6, 0, -6, -7, 0, 4, 0, 0, 2, 1, 0, 0,                    8, 0, 0, -3, 0, -3, 8, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((8439053503855573 : Rat)/9007199254740992, (19676457066203681 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (5798334232039158605227178307021573088705259218259 : Rat)/59877262752282922099673642112223358066584648155136,            reHi := (181105470847205236993185680723025578866225882648423 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -237, a6 := 1404 }
def label : String := "423.b1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -237, a6 := 1404 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, 1, 0, -3, 0, 0, -2, -1, 0, -2, 6, 0, -4, -2, 0, 6, 2, 0, 2, -3, 0, -4, 4, 0, -6, -3, 0,                    2, 8, 0, 4, -3, 0, -7, -12, 0, 0, -10, 0, -10, -2, 0, 6, 1, 0, 2, 8, 0, -4, -4, 0, -1, 0, 0, 6, -8,                    0, -10, -4, 0, -8],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((4499340582814281 : Rat)/4503599627370496, (23412412081254599 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (4759288758703865203612386138312866352785428868223 : Rat)/29938631376141461049836821056111679033292324077568,            reHi := (205941022247843761279848349632572995603926537240817 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := 4 }
def label : String := "423.c1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := 4 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 1, 0, -3, 0, 0, 0, 3, 0, -4, 0, 0, 4, -8, 0, -6, -2, 0, 0, -3, 0, -4, 0, 0, 6, 1, 0, 4,                    0, 0, 0, -3, 0, 1, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((4787048722469291 : Rat)/4503599627370496, (20263442782238987 : Rat)/4503599627370496),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (6671889489172431071277219449721516540120100043053 : Rat)/29938631376141461049836821056111679033292324077568,            reHi := (159856552868948905211753875488778965375012248534221 : Rat)/29938631376141461049836821056111679033292324077568,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6768, a6 := -212625 }
def label : String := "423.d1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6768, a6 := -212625 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, -2, 0, 0, -1, -2, 0, 0, 2, 0, -4, 0, 0, -1, -2, 0, 0, 6, 0,                    -4, 5, 0, -2, 0, 0, -10, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((13138558786961909 : Rat)/9007199254740992, (50452246746727589 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (37039289903602291886517147339860094303013406826547 : Rat)/59877262752282922099673642112223358066584648155136,            reHi := (385694044164241000133645022806965847689195146889987 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -558, a6 := -891 }
def label : String := "423.d2"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 47, 47, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -558, a6 := -891 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, -2, 0, 0, -1, -2, 0, 0, 2, 0, -4, 0, 0, -1, -2, 0, 0, 6, 0,                    -4, 5, 0, -2, 0, 0, -10, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((13138558786961909 : Rat)/9007199254740992, (50452246746727589 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (37039289903602291886517147339860094303013406826547 : Rat)/59877262752282922099673642112223358066584648155136,            reHi := (385694044164241000133645022806965847689195146889987 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -423, a6 := -3240 }
def label : String := "423.d3"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -423, a6 := -3240 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, -2, 0, 0, -1, -2, 0, 0, 2, 0, -4, 0, 0, -1, -2, 0, 0, 6, 0,                    -4, 5, 0, -2, 0, 0, -10, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((13138558786961909 : Rat)/9007199254740992, (50452246746727589 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (37039289903602291886517147339860094303013406826547 : Rat)/59877262752282922099673642112223358066584648155136,            reHi := (385694044164241000133645022806965847689195146889987 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := -81 }
def label : String := "423.d4"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2, 0, 2],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := -81 },   conductor := 423,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, -2, 0, 0, -1, -2, 0, 0, 2, 0, -4, 0, 0, -1, -2, 0, 0, 6, 0,                    -4, 5, 0, -2, 0, 0, -10, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   finite := ((13138558786961909 : Rat)/9007199254740992, (50452246746727589 : Rat)/9007199254740992),   tail := (23985891072882578497799286494419097900390625 : Rat)/28551703811780415582501240783797911675731968,   box := { reLo := (37039289903602291886517147339860094303013406826547 : Rat)/59877262752282922099673642112223358066584648155136,            reHi := (385694044164241000133645022806965847689195146889987 : Rat)/59877262752282922099673642112223358066584648155136,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1287, a6 := 18094 }
def label : String := "423.e1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 1],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1287, a6 := 18094 },   conductor := 423,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, -1, 0, 0, 4, -3, 0, 0, 0, 0, 6, 4, 0, -1, 6, 0, 2, 0, 0, 0, -4, 0, -5, 6, 0, -4, -8, 0, 6,                    5],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   geometricUpper := (829513171431809 : Rat)/1125899906842624,   tail := (2484415382240069324991361392874181243896062825699633613328744217811680952015574374178110877612737154951373248415605581455835995984747687856083388818490065832704203274902088497928397560143808442198215918106630938135727657396001836694599824996172835901549976257847880526166023575080411021482663937011873513352607009260347533893927499786947235954388025822673620523832776665648146623129254702288825873264233280602061412462521036644444318548946036178008342286086136717772255118997292878655532991074564609 : Rat)/5939907006494280205574647134476755016073032551520728325895725227409680076903503222084126522773875988836205571850997873570430332728735759205373785869351861289792930787719425187910234157141499702509796927058585239104124761827817287598835160023934136543222138714383517585138428171758595856290513408454420494274623408501183895443009946822882621091262305142800220231219980504736033373338359204807350362462886306881000317271230001763816190792196900715107637724613420597651366764920581181530667759137980416,   box := { reLo := (5591270881326917201706173025982580821899132770623027593698659971294519982131309010011716364643270125287241111004172817514752982160545655871606220017548853674187632386420941472069766472222877903112062323900485773688364699380784319445768371357009475982187399492313286378885810199575408284415545111398524737515344101352251050067644790172392573463092244259723685752032037594165366960663728213901302358757108012612099145527495082845263677414022253853420955699803141176669998068955732217587163504097478242361463595 : Rat)/3610032304694284639610934507855933354895586170934671969382487948124518625849280905864323198486245986305538781151130499554161456385134012731780078253972355896086800499982348183664072463634444303329133523689811256906383346475322878390635001549930948351354472939465473841420718660683950936297613372330168060899500998879298941682765904294735075107644373878283732758319458235996677695844783625594421942188453429219754591565464828187005271892462434505724046417439229090426653470414740158461349179996673147064549376,            reHi := (43055614005076419508486665713719632274952672584587848170506524394773897163960925733326625469060574605659171081261033019272860866279954873920521627403550581522523220357851761634802925831991425657667782564958236739112588932125635542195797733234981153061802025315011648922278525219269742556068497102227665602786097302019176526489623874450126675109993802408430321233531740583400456243286374620205118221517864808790257836957139414382707495137173709661985483895393344074935571724181272398220875004035059913539706921 : Rat)/18050161523471423198054672539279666774477930854673359846912439740622593129246404529321615992431229931527693905755652497770807281925670063658900391269861779480434002499911740918320362318172221516645667618449056284531916732376614391953175007749654741756772364697327369207103593303419754681488066861650840304497504994396494708413829521473675375538221869391418663791597291179983388479223918127972109710942267146098772957827324140935026359462312172528620232087196145452133267352073700792306745899983365735322746880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2484415382240069324991361392874181243896062825699633613328744217811680952015574374178110877612737154951373248415605581455835995984747687856083388818490065832704203274902088497928397560143808442198215918106630938135727657396001836694599824996172835901549976257847880526166023575080411021482663937011873513352607009260347533893927499786947235954388025822673620523832776665648146623129254702288825873264233280602061412462521036644444318548946036178008342286086136717772255118997292878655532991074564609 : Rat)/11879814012988560411149294268953510032146065103041456651791450454819360153807006444168253045547751977672411143701995747140860665457471518410747571738703722579585861575438850375820468314282999405019593854117170478208249523655634575197670320047868273086444277428767035170276856343517191712581026816908840988549246817002367790886019893645765242182524610285600440462439961009472066746676718409614700724925772613762000634542460003527632381584393801430215275449226841195302733529841162363061335518275960832, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -72, a6 := 355 }
def label : String := "423.e2"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 1, 0, 2, 0],                kodaira := -10 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -72, a6 := 355 },   conductor := 423,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, -1, 0, 0, 4, -3, 0, 0, 0, 0, 6, 4, 0, -1, 6, 0, 2, 0, 0, 0, -4, 0, -5, 6, 0, -4, -8, 0, 6,                    5],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   geometricUpper := (829513171431809 : Rat)/1125899906842624,   tail := (2484415382240069324991361392874181243896062825699633613328744217811680952015574374178110877612737154951373248415605581455835995984747687856083388818490065832704203274902088497928397560143808442198215918106630938135727657396001836694599824996172835901549976257847880526166023575080411021482663937011873513352607009260347533893927499786947235954388025822673620523832776665648146623129254702288825873264233280602061412462521036644444318548946036178008342286086136717772255118997292878655532991074564609 : Rat)/5939907006494280205574647134476755016073032551520728325895725227409680076903503222084126522773875988836205571850997873570430332728735759205373785869351861289792930787719425187910234157141499702509796927058585239104124761827817287598835160023934136543222138714383517585138428171758595856290513408454420494274623408501183895443009946822882621091262305142800220231219980504736033373338359204807350362462886306881000317271230001763816190792196900715107637724613420597651366764920581181530667759137980416,   box := { reLo := (5591270881326917201706173025982580821899132770623027593698659971294519982131309010011716364643270125287241111004172817514752982160545655871606220017548853674187632386420941472069766472222877903112062323900485773688364699380784319445768371357009475982187399492313286378885810199575408284415545111398524737515344101352251050067644790172392573463092244259723685752032037594165366960663728213901302358757108012612099145527495082845263677414022253853420955699803141176669998068955732217587163504097478242361463595 : Rat)/3610032304694284639610934507855933354895586170934671969382487948124518625849280905864323198486245986305538781151130499554161456385134012731780078253972355896086800499982348183664072463634444303329133523689811256906383346475322878390635001549930948351354472939465473841420718660683950936297613372330168060899500998879298941682765904294735075107644373878283732758319458235996677695844783625594421942188453429219754591565464828187005271892462434505724046417439229090426653470414740158461349179996673147064549376,            reHi := (43055614005076419508486665713719632274952672584587848170506524394773897163960925733326625469060574605659171081261033019272860866279954873920521627403550581522523220357851761634802925831991425657667782564958236739112588932125635542195797733234981153061802025315011648922278525219269742556068497102227665602786097302019176526489623874450126675109993802408430321233531740583400456243286374620205118221517864808790257836957139414382707495137173709661985483895393344074935571724181272398220875004035059913539706921 : Rat)/18050161523471423198054672539279666774477930854673359846912439740622593129246404529321615992431229931527693905755652497770807281925670063658900391269861779480434002499911740918320362318172221516645667618449056284531916732376614391953175007749654741756772364697327369207103593303419754681488066861650840304497504994396494708413829521473675375538221869391418663791597291179983388479223918127972109710942267146098772957827324140935026359462312172528620232087196145452133267352073700792306745899983365735322746880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2484415382240069324991361392874181243896062825699633613328744217811680952015574374178110877612737154951373248415605581455835995984747687856083388818490065832704203274902088497928397560143808442198215918106630938135727657396001836694599824996172835901549976257847880526166023575080411021482663937011873513352607009260347533893927499786947235954388025822673620523832776665648146623129254702288825873264233280602061412462521036644444318548946036178008342286086136717772255118997292878655532991074564609 : Rat)/11879814012988560411149294268953510032146065103041456651791450454819360153807006444168253045547751977672411143701995747140860665457471518410747571738703722579585861575438850375820468314282999405019593854117170478208249523655634575197670320047868273086444277428767035170276856343517191712581026816908840988549246817002367790886019893645765242182524610285600440462439961009472066746676718409614700724925772613762000634542460003527632381584393801430215275449226841195302733529841162363061335518275960832, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -111, a6 := -171 }
def label : String := "423.f1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 0, 1, 2, 1, 1],                kodaira := -11 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -111, a6 := -171 },   conductor := 423,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 3, 0, -3, 0, 0, 6, 5, 0, 2, -6, 0, -4, 6, 0, -6, 6, 0, 10, -9, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   geometricUpper := (829513171431809 : Rat)/1125899906842624,   tail := (3650414608669877635735239240431846423286206422895521426488896764822697883463586101626793373320677772380334571174298152459881207274571197855428893487967448948843913449565526666421199302285289394748219188264170995993315166462340683869878601879788367690930435086645928455790833160979524056749176375020925932012278639687763642573610047817968489760450959385098814230376185064550390625 : Rat)/1230574920602061751732840194170610516509389324855564961183226357678344644097048565434815963426261028429707027876650757181128435495676955715162631887396433129535441666824925054604384360180922485138354270537136024623768362832979368085055340254966419916394802699992348079919124448233604902568813377516058720991920049917191599947263478096363684089113590795017591254715365549364215808,   box := { reLo := (346730468534195757883854100667133871364467795834144153812633647738696310958584350701595599447123276718432422925795490308617720632595753523701885857213651733861681989419364675396344644917846752217885800986391244408485600952754024613101024421340347921911416794156267495493366930382112531360399000739863998428714963717598343786770295428272244821200183550668827212199573713305011555521263 : Rat)/2691495007717020432463792080087046762551588690484218849625534941118710230399403166590547952966466727466028765766392386345206397189612202385867981024635167594422974982054473705554890406822310945657331385204765856016736806662849979185111764375558729144839966543382763835177910206309817138824970087102460893672712654378132709530655470340195204384447909083000550328444626799086172352020480,            reHi := (2330713517180207752300816711920829208831656755318430790893890027320717870398987071442663389308826030547765721079412825381088508141704243117067258235904540975182216465804411043210693754537832986158381714896349343998832459081413236772665755888830852466285663193116702770925833869064410331994665442694466314629175913082676572346564816957455075965573970400885838153024594199106907042837543 : Rat)/384499286816717204637684582869578108935941241497745549946504991588387175771343309512935421852352389638004109395198912335029485312801743197981140146376452513488996426007781957936412915260330135093904483600680836573819543808978568455015966339365532734977138077626109119311130029472831019832138583871780127667530379196876101361522210048599314912063987011857221475492089542726596050288640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3650414608669877635735239240431846423286206422895521426488896764822697883463586101626793373320677772380334571174298152459881207274571197855428893487967448948843913449565526666421199302285289394748219188264170995993315166462340683869878601879788367690930435086645928455790833160979524056749176375020925932012278639687763642573610047817968489760450959385098814230376185064550390625 : Rat)/2461149841204123503465680388341221033018778649711129922366452715356689288194097130869631926852522056859414055753301514362256870991353911430325263774792866259070883333649850109208768720361844970276708541074272049247536725665958736170110680509932839832789605399984696159838248896467209805137626755032117441983840099834383199894526956192727368178227181590035182509430731098728431616, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -81, a6 := -277 }
def label : String := "423.g1"
def inputConductor : Nat := 423
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 423 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -81, a6 := -277 },   conductor := 423,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 3, 0, 1, 0, 0, 6, -3, 0, 0, 2, 0, -4, 0, 0, -4, 6, 0, -6, 7, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8833443690418329906463623046875,   alphaHi := (5397215081808807583452231630848 : Rat)/17666887380836659717559814453125,   geometricUpper := (829513171431809 : Rat)/1125899906842624,   tail := (3650414608669877635735239240431846423286206422895521426488896764822697883463586101626793373320677772380334571174298152459881207274571197855428893487967448948843913449565526666421199302285289394748219188264170995993315166462340683869878601879788367690930435086645928455790833160979524056749176375020925932012278639687763642573610047817968489760450959385098814230376185064550390625 : Rat)/1230574920602061751732840194170610516509389324855564961183226357678344644097048565434815963426261028429707027876650757181128435495676955715162631887396433129535441666824925054604384360180922485138354270537136024623768362832979368085055340254966419916394802699992348079919124448233604902568813377516058720991920049917191599947263478096363684089113590795017591254715365549364215808,   box := { reLo := (6484946199368969192297279119776306658015580370980956131388808767301478225890700766128957580487122701133807929517126433055196411026554436931204583971948875782332614708745422196345593605400815210716777793903841971470752857757822772545534512490786964932715120290084963195641484166770833299987590345094414103276691781670694821738008263950442552173312783884163950193689653003405107772413 : Rat)/29576868216670554202898814066890623764303172422903503842038845506799013520872562270225801680950183818308008415015300948848421947138595630613933857413573270268384340462137073687416378096948471930300344892360064351832272600690659111924305103028117902690549082894316086100856156113294693833241429528598471359040798399759700104732477696046101147081845154758247805807083810978968926945280,            reHi := (1273722635066910286780563035164280539413725062716076537308325229184039543099099895874659720482319562561251390806806459693895467781789807595953350534978123650830809681348386213432496174246386783978316921884738166913114745713438804662421395244937646473482856617676795154782607214634693483967368336562625306856499121953171346047767821613022516538303872739684469286943549616707935167568917 : Rat)/207038077516693879420291698468234366350122206960324526894271918547593094646107935891580611766651286728156058905107106641938953629970169414297537001895012891878690383234959515811914646678639303512102414246520450462825908204834613783470135721196825318833843580260212602705993092793062856832690006700189299513285588798317900733127343872322708029572916083307734640649586676852782488616960,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3650414608669877635735239240431846423286206422895521426488896764822697883463586101626793373320677772380334571174298152459881207274571197855428893487967448948843913449565526666421199302285289394748219188264170995993315166462340683869878601879788367690930435086645928455790833160979524056749176375020925932012278639687763642573610047817968489760450959385098814230376185064550390625 : Rat)/2461149841204123503465680388341221033018778649711129922366452715356689288194097130869631926852522056859414055753301514362256870991353911430325263774792866259070883333649850109208768720361844970276708541074272049247536725665958736170110680509932839832789605399984696159838248896467209805137626755032117441983840099834383199894526956192727368178227181590035182509430731098728431616, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N423.C423_g1
