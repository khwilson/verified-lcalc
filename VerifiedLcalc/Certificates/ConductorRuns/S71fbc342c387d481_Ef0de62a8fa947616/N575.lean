module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -18, a6 := 24 }
def label : String := "575.a1"
def inputConductor : Nat := 575
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 575 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -18, a6 := 24 },   conductor := 575,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -2, -2, 2, 0, 4, -1, 0, 1, 0, 0, -4, -2, 2, 0, -4, 5, -2, 8, 0, 2, 0, 1, 0, 0, 4, 4, -2, -5, 0,                    -5, 8, 0, -10, 0, 2, -7, -16, 4, 0, -7, -4, -4, 0, 0, -2, 2, 8, -6, 0, -10, -4, 1, -8, 0, 0, -16, 10,                    3, 0, -6, 10, -1, -8],   alphaLo := (1349303770452201895858762940416 : Rat)/5149484887438498020172119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/20597939549753991985321044921875,   finite := ((4490265470610967 : Rat)/9007199254740992, (6379802796232141 : Rat)/2251799813685248),   tail := (10588982184977067907575116874217987060546875 : Rat)/189550798856136454697378820030593705193766912,   box := { reLo := (703852935308071985756203602299488836601900838746921 : Rat)/1590067347690977112966069548739198600138074668138496,            reHi := (1148452036717592961360685730280926436249088421712883 : Rat)/397516836922744278241517387184799650034518667034624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 175, a6 := -1344 }
def label : String := "575.b1"
def inputConductor : Nat := 575
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 575 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 175, a6 := -1344 },   conductor := 575,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -2, 0, 2, 0, 0, -1, 0, -3, 0, 2, 0, 2, 2, 0, -4, -3, 6, -2, 0, 0, -4, -1, 0, 0, -4, 0, -2, 7, 0,                    -5, 8, 0, 6, 0, -6, -11, 4, 0, 0, 1, 0, 0, 4, 0, 2, 0, 0, -6, 0, 0, 4, -11, 0, 0, 0, 0, -14, -13, 0,                    -8, 10, 3, -8],   alphaLo := (1349303770452201895858762940416 : Rat)/5149484887438498020172119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/20597939549753991985321044921875,   finite := ((12224567194495881 : Rat)/9007199254740992, (7648316862212777 : Rat)/2251799813685248),   tail := (10588982184977067907575116874217987060546875 : Rat)/189550798856136454697378820030593705193766912,   box := { reLo := (2069211942089928297528247964816938923320007736648503 : Rat)/1590067347690977112966069548739198600138074668138496,            reHi := (1372386551693583448185520989962988166107045567740951 : Rat)/397516836922744278241517387184799650034518667034624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -55, a6 := 72 }
def label : String := "575.c1"
def inputConductor : Nat := 575
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 575 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -55, a6 := 72 },   conductor := 575,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 1, 3, -3, 0, -1, 0, 1, -1, 0, -1, 0, 3, -5, 0, 0, 1, 1, 0, 0, -1, 0, -1, -5, 0,                    -2, -5, 0, 0, 0, 3, -4, 5, 0, 0, -5, 0, -9, 1, 0, -1, -6, 0, -6, 0, 0, -1, 2, 0, 0, 3, 0, 5, 8, 0,                    -8, 2, -3, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5149484887438498020172119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/20597939549753991985321044921875,   finite := ((4859096545843787 : Rat)/2251799813685248, (27686240733572851 : Rat)/9007199254740992),   tail := (7008158054463983713157823807735443115234375 : Rat)/3338870920164833290836864708011190755786752,   box := { reLo := (206254028655793294352639675180141429974690086313 : Rat)/3501059913982760232772556248067542357939849265152,            reHi := (72440439872110517975187888861315853215467719044449 : Rat)/14004239655931040931090224992270169431759397060608,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 1 }
def label : String := "575.d1"
def inputConductor : Nat := 575
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 575 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 1 },   conductor := 575,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 0, 0, -1, -3, -3, 0, -1, 0, -1, -1, 0, -1, 0, -3, -5, 0, 0, -1, -1, 0, 0, -1, 0, 1, -5,                    0, -2, 5, 0, 0, 0, 3, 4, -5, 0, 0, -5, 0, 9, 1, 0, -1, 6, 0, -6, 0, 0, 1, -2, 0, 0, 3, 0, -5, 8, 0,                    -8, -2, 3, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5149484887438498020172119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/20597939549753991985321044921875,   finite := ((7071383733575163 : Rat)/2251799813685248, (55493630134081795 : Rat)/9007199254740992),   tail := (7008158054463983713157823807735443115234375 : Rat)/3338870920164833290836864708011190755786752,   box := { reLo := (3645880386252873668217221210612981347145631079737 : Rat)/3501059913982760232772556248067542357939849265152,            reHi := (115674894263196586829844201348011052570856041746705 : Rat)/14004239655931040931090224992270169431759397060608,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -458, a6 := 3943 }
def label : String := "575.e1"
def inputConductor : Nat := 575
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 575 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -458, a6 := 3943 },   conductor := 575,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 2, 2, 2, 0, 4, 1, 0, 1, 0, 0, 4, 2, 2, 0, -4, -5, 2, 8, 0, 2, 0, -1, 0, 0, 4, -4, 2, -5, 0, -5,                    -8],   alphaLo := (1349303770452201895858762940416 : Rat)/5149484887438498020172119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/20597939549753991985321044921875,   geometricUpper := (6930952393084961 : Rat)/9007199254740992,   tail := (6610312345849085460420182186555454104188771040078968012558086607125777921174156624229594119902733734134653884712935094609631995158609962248261471024292511128675521530643201650862195865957055469354604017789535451876866825773099448753049112360532917772536112953982165942308110053670476233456141578669377304786216484024608674002141933261897612192898237773685363453413388854786531925945573854735747806450568040492247050677669753443569702133511394663460844527104253951961462684020157025739628236042408149981327746150113028343963172001 : Rat)/3164523411822629588743209791944581370417006568199567791002339709249244598127121706900710929398964434886256031916307120116975966905606500332760063711951057440715921623613464040523524301968842568745872241217978566530448117458804390093665679351715001472229017400230736746263147079062645095755996226886945207516491508220330025847716618495200143721132127496804709054367462176775239159889586762409577424141509400680658244963425717999672001983226218418633092076905625207891924014994966083364661454291659639502162614259654879257869418496,   box := { reLo := (1127509959254424965827287291579317208777377410532359211607001206962737714010129369270061796862847488737595744610827225917684615136922593729693131796079703118680066330307127813658208402554784787164803109114605367314430108868820894326071565296091076370134132980284506592532968800895755308064436972509387266886250646378452691633971672850669300259923756235170136364340461988506873646812365115359387288042038931138332705443505115833452168239470385694923029225832423974841460134152537808502145785789631696706502432387494766753348301070697471947 : Rat)/570639889962743041208192445478160348555096631193787341694137453004406765074293075548403505016117602435268114391231899335906627942474714521965164661721316780213378414619304252418656737480572897721111209292442989534528810395071185519363810922303140076133397584474243200029355046673100664576580467068720053372793094157829253359576675696372834654786245131192729481670717610557892908970911550426395841351452165724938897001799439893381860047247516647589148675747702957946052629435062018427680965749079384957765793006783874826916918191594668032,            reHi := (18796892729445290396210184773364400825710152303608325706739373276538197093264673888385551942040090270500848746168033869889948065071098774279315526145352219795607515592014548082625743313752736464897302026973917938002789533128589829249131198157670514564080678079845702059114028513356381550766656416583755164140138960454075520586722934404746388693919888683588079633590429170555601662003967910204393678711015876163312939204497502494522710515654637514758436015177781916562631347487349821711169495345073928097765437547849140317569203664323570791 : Rat)/3054601763918212749996794855206623042265517261096155770245088719023589154221215874994395232733335401271141082917770755268676655456776413029342940248037636882318672690020981586476339006513654923095360002683077179273065985055969287191888634937034455701655245893362125364863018191014832969204048382544324991583774798138968356218910440492348703152091076878737551931296194268280485571550173593458942444881302769468790566303749942958691133194089647937094854676061233480770046428152390804524645169598013178303334539036313682897025856202065575936,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (6610312345849085460420182186555454104188771040078968012558086607125777921174156624229594119902733734134653884712935094609631995158609962248261471024292511128675521530643201650862195865957055469354604017789535451876866825773099448753049112360532917772536112953982165942308110053670476233456141578669377304786216484024608674002141933261897612192898237773685363453413388854786531925945573854735747806450568040492247050677669753443569702133511394663460844527104253951961462684020157025739628236042408149981327746150113028343963172001 : Rat)/6329046823645259177486419583889162740834013136399135582004679418498489196254243413801421858797928869772512063832614240233951933811213000665520127423902114881431843247226928081047048603937685137491744482435957133060896234917608780187331358703430002944458034800461473492526294158125290191511992453773890415032983016440660051695433236990400287442264254993609418108734924353550478319779173524819154848283018801361316489926851435999344003966452436837266184153811250415783848029989932166729322908583319279004325228519309758515738836992, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N575.C575_e1
