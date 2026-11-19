module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4942, a6 := 134964 }
def label : String := "406.a1"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4942, a6 := 134964 },   conductor := 406,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, -3, 0, -4, 0, 0, 1, 0, 1, -4, 3, 4, 0, 0, 4, 0, 0, -5, 0, 0, -1, -1, 0,                    -6, -1, 0, 4, 0, -3, -2, -4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   finite := ((3911600500005095 : Rat)/4503599627370496, (8344823103296889 : Rat)/2251799813685248),   tail := (17696192151274760448411972309360504150390625 : Rat)/23940135571519734319722574182279594224123904,   box := { reLo := (3247447752717101568907887953609647515550928535155 : Rat)/25103051597041876934037417945758007793154946760704,            reHi := (55791921588232834881629434048733388774520093687661 : Rat)/12551525798520938467018708972879003896577473380352,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -302, a6 := 2260 }
def label : String := "406.a2"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 29, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -302, a6 := 2260 },   conductor := 406,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, -3, 0, -4, 0, 0, 1, 0, 1, -4, 3, 4, 0, 0, 4, 0, 0, -5, 0, 0, -1, -1, 0,                    -6, -1, 0, 4, 0, -3, -2, -4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   finite := ((3911600500005095 : Rat)/4503599627370496, (8344823103296889 : Rat)/2251799813685248),   tail := (17696192151274760448411972309360504150390625 : Rat)/23940135571519734319722574182279594224123904,   box := { reLo := (3247447752717101568907887953609647515550928535155 : Rat)/25103051597041876934037417945758007793154946760704,            reHi := (55791921588232834881629434048733388774520093687661 : Rat)/12551525798520938467018708972879003896577473380352,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -15, a6 := 210 }
def label : String := "406.b1"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 29, 29, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -15, a6 := 210 },   conductor := 406,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, 1, -1, -2, 3, -3, 1, -1, -1, -3, 1, 0, 2, -4, -3, 1, 3, -6, -1, 4, 1, -5, 1, 1,                    3, 5, -1, -3, 0, -3, -2, 2, 4, -1, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   finite := ((8524837642369513 : Rat)/9007199254740992, (34775894305983381 : Rat)/9007199254740992),   tail := (17696192151274760448411972309360504150390625 : Rat)/23940135571519734319722574182279594224123904,   box := { reLo := (10405816167314860810415545760231983703140616647837 : Rat)/50206103194083753868074835891516015586309893521408,            reHi := (230952341356966350613472139068010810717075517488569 : Rat)/50206103194083753868074835891516015586309893521408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 130, a6 := -5648 }
def label : String := "406.b2"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 130, a6 := -5648 },   conductor := 406,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, 1, -1, -2, 3, -3, 1, -1, -1, -3, 1, 0, 2, -4, -3, 1, 3, -6, -1, 4, 1, -5, 1, 1,                    3, 5, -1, -3, 0, -3, -2, 2, 4, -1, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   finite := ((8524837642369513 : Rat)/9007199254740992, (34775894305983381 : Rat)/9007199254740992),   tail := (17696192151274760448411972309360504150390625 : Rat)/23940135571519734319722574182279594224123904,   box := { reLo := (10405816167314860810415545760231983703140616647837 : Rat)/50206103194083753868074835891516015586309893521408,            reHi := (230952341356966350613472139068010810717075517488569 : Rat)/50206103194083753868074835891516015586309893521408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -39244, a6 := -3007920 }
def label : String := "406.c1"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -39244, a6 := -3007920 },   conductor := 406,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 2, 1, 2, -2, 1, -1, 1, -2, 4, 2, -2, -1, 4, 1, -4, -1, 2, 2, 2, -4, 0, -2, -1, 2, -4, 1, -1,                    -4, -2, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   geometricUpper := (6594229337432819 : Rat)/9007199254740992,   tail := (1277818926796476954484731053018950998132049506209374688445077254736202889428048574087217248098607607348260734214596320026889223451946190058346441387097183973451857389180273575588650851077192818617648370105424481988894607343740757163294176260068293939824060583393673467228422131941706586749725707295411651089181792042109209652765415694419294962272176104680110422498985911723399238513280275386781144357467727623010042309112797500286524187075557743386285005192275936044915115905748355986222501557408707238170103302198357574395889139 : Rat)/3850127404966558053474991974865196936089757832198409733801736683889479214950694091580254608035261808125172667894782070760883584806736460473115376177309067684839104189550590773831408967162762297769494791273741525910195686765121801708120968519260176273151826701138233517959320112535664952432362318367771513263034135864204184977366531376218799096160692279172771704572843013451071817572859823853949420550368189483469324578508712582007932656356420180401981432285953888281330557817165585151972333480071335480222960421330825965608108032,   box := { reLo := (343482236124637247640169275164298621099968504138466058048064772295075018487628213909178033114940408453150871229210473428324727681780815885379386404549946907065709805201297767345871331227182524241813293050815366961968226191371365500853187567524947167333230965752992650177794654148415428444829379742813096763579544364810195473284045717727980232218459609477221183712911603447200611642252815122969732634866624164488454661495020493612293693890700333888344243637302228037812145436307275878677683091189293359704657094768939596565642687724680922141 : Rat)/251798947631425395477405371796776262450370472771321527701469283988937443293790923084031838179698851487104776086040393711306245804579506251596540717661010565010220143406435731531744574057382831062609200358807711120266176511464603067303069341593409119021802322745142981492711543208169473901727518123559790096484539749949718193953635159610586665058474818940542788267301616434334721686818276062369639561460219054814778022919270563018307215143546681963144918418183799396179213044899032397428637523574863792807774738189685357350030218608666214400,            reHi := (1531864080613310602431489515686110138452361980154790710186276824204782743373183445435831763537903277795526272319840135380005115448063285727624832527684172673573943445043820762334574624466355722526472304081409206069607233919703732365762326762858566050245939764511120938568674203525212038620802894531474515690417655866230026948178133499930821283577389812003131693148319738133434961007107613972841266549239430143576544121010741904956112816389497751856342653233530626437707412858182371242513909834368068601362632742712030110758034054889914446761 : Rat)/755396842894276186432216115390328787351111418313964583104407851966812329881372769252095514539096554461314328258121181133918737413738518754789622152983031695030660430219307194595233722172148493187827601076423133360798529534393809201909208024780227357065406968235428944478134629624508421705182554370679370289453619249849154581860905478831759995175424456821628364801904849303004165060454828187108918684380657164444334068757811689054921645430640045889434755254551398188537639134697097192285912570724591378423324214569056072050090655825998643200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1277818926796476954484731053018950998132049506209374688445077254736202889428048574087217248098607607348260734214596320026889223451946190058346441387097183973451857389180273575588650851077192818617648370105424481988894607343740757163294176260068293939824060583393673467228422131941706586749725707295411651089181792042109209652765415694419294962272176104680110422498985911723399238513280275386781144357467727623010042309112797500286524187075557743386285005192275936044915115905748355986222501557408707238170103302198357574395889139 : Rat)/7700254809933116106949983949730393872179515664396819467603473367778958429901388183160509216070523616250345335789564141521767169613472920946230752354618135369678208379101181547662817934325524595538989582547483051820391373530243603416241937038520352546303653402276467035918640225071329904864724636735543026526068271728408369954733062752437598192321384558345543409145686026902143635145719647707898841100736378966938649157017425164015865312712840360803962864571907776562661115634331170303944666960142670960445920842661651931216216064, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2124, a6 := -60592 }
def label : String := "406.c2"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 29, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2124, a6 := -60592 },   conductor := 406,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 2, 1, 2, -2, 1, -1, 1, -2, 4, 2, -2, -1, 4, 1, -4, -1, 2, 2, 2, -4, 0, -2, -1, 2, -4, 1, -1,                    -4, -2, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   geometricUpper := (6594229337432819 : Rat)/9007199254740992,   tail := (1277818926796476954484731053018950998132049506209374688445077254736202889428048574087217248098607607348260734214596320026889223451946190058346441387097183973451857389180273575588650851077192818617648370105424481988894607343740757163294176260068293939824060583393673467228422131941706586749725707295411651089181792042109209652765415694419294962272176104680110422498985911723399238513280275386781144357467727623010042309112797500286524187075557743386285005192275936044915115905748355986222501557408707238170103302198357574395889139 : Rat)/3850127404966558053474991974865196936089757832198409733801736683889479214950694091580254608035261808125172667894782070760883584806736460473115376177309067684839104189550590773831408967162762297769494791273741525910195686765121801708120968519260176273151826701138233517959320112535664952432362318367771513263034135864204184977366531376218799096160692279172771704572843013451071817572859823853949420550368189483469324578508712582007932656356420180401981432285953888281330557817165585151972333480071335480222960421330825965608108032,   box := { reLo := (343482236124637247640169275164298621099968504138466058048064772295075018487628213909178033114940408453150871229210473428324727681780815885379386404549946907065709805201297767345871331227182524241813293050815366961968226191371365500853187567524947167333230965752992650177794654148415428444829379742813096763579544364810195473284045717727980232218459609477221183712911603447200611642252815122969732634866624164488454661495020493612293693890700333888344243637302228037812145436307275878677683091189293359704657094768939596565642687724680922141 : Rat)/251798947631425395477405371796776262450370472771321527701469283988937443293790923084031838179698851487104776086040393711306245804579506251596540717661010565010220143406435731531744574057382831062609200358807711120266176511464603067303069341593409119021802322745142981492711543208169473901727518123559790096484539749949718193953635159610586665058474818940542788267301616434334721686818276062369639561460219054814778022919270563018307215143546681963144918418183799396179213044899032397428637523574863792807774738189685357350030218608666214400,            reHi := (1531864080613310602431489515686110138452361980154790710186276824204782743373183445435831763537903277795526272319840135380005115448063285727624832527684172673573943445043820762334574624466355722526472304081409206069607233919703732365762326762858566050245939764511120938568674203525212038620802894531474515690417655866230026948178133499930821283577389812003131693148319738133434961007107613972841266549239430143576544121010741904956112816389497751856342653233530626437707412858182371242513909834368068601362632742712030110758034054889914446761 : Rat)/755396842894276186432216115390328787351111418313964583104407851966812329881372769252095514539096554461314328258121181133918737413738518754789622152983031695030660430219307194595233722172148493187827601076423133360798529534393809201909208024780227357065406968235428944478134629624508421705182554370679370289453619249849154581860905478831759995175424456821628364801904849303004165060454828187108918684380657164444334068757811689054921645430640045889434755254551398188537639134697097192285912570724591378423324214569056072050090655825998643200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1277818926796476954484731053018950998132049506209374688445077254736202889428048574087217248098607607348260734214596320026889223451946190058346441387097183973451857389180273575588650851077192818617648370105424481988894607343740757163294176260068293939824060583393673467228422131941706586749725707295411651089181792042109209652765415694419294962272176104680110422498985911723399238513280275386781144357467727623010042309112797500286524187075557743386285005192275936044915115905748355986222501557408707238170103302198357574395889139 : Rat)/7700254809933116106949983949730393872179515664396819467603473367778958429901388183160509216070523616250345335789564141521767169613472920946230752354618135369678208379101181547662817934325524595538989582547483051820391373530243603416241937038520352546303653402276467035918640225071329904864724636735543026526068271728408369954733062752437598192321384558345543409145686026902143635145719647707898841100736378966938649157017425164015865312712840360803962864571907776562661115634331170303944666960142670960445920842661651931216216064, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -102, a6 := 355 }
def label : String := "406.d1"
def inputConductor : Nat := 406
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 406 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -102, a6 := 355 },   conductor := 406,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -3, -1, -1, 1, -2, -3, -1, -1, -1, -1, 3, 1, -4, -2, -4, -3, 1, -1, -2, -1, 4, -1, 5,                    -1, 1, 3, -1, 1, 1, -4, 3, -2, 6, -4, 1, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/8654119304658376407623291015625,   alphaHi := (5397215081808807583452231630848 : Rat)/17308238609316752719879150390625,   finite := ((13652993976766933 : Rat)/9007199254740992, (11432624254025705 : Rat)/2251799813685248),   tail := (17696192151274760448411972309360504150390625 : Rat)/23940135571519734319722574182279594224123904,   box := { reLo := (38990145084501084767291950513416422644887652999417 : Rat)/50206103194083753868074835891516015586309893521408,            reHi := (73003316477127117332255702782251160429286014694045 : Rat)/12551525798520938467018708972879003896577473380352,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N406.C406_d1
