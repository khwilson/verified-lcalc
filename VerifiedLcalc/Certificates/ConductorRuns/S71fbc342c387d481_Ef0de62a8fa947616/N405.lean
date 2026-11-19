module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := -2 }
def label : String := "405.a1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := -2 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, -1, 0, 0, 0, 0, 2, -5, 0, 4, 0, 0, -4, 4, 0, -5, -2, 0, 10, -6, 0, 1, -8, 0, 0, 5, 0,                    -9, 8, 0, -8, 0, 0, -10, 10, 0, 0, -7, 0, -2, -10, 0, 12, -2, 0, -7, -2, 0, 8, -8, 0, 5, 0, 0, -10,                    1, 0, -2, 18, 0, -8],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((2118456738280079 : Rat)/2251799813685248, (10757830442231141 : Rat)/4503599627370496),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (19521351027931639169559803423688861000803590009607 : Rat)/94169733644053684748451317803684173022771946717184,            reHi := (588033928962432030071633410097557723464354265920653 : Rat)/188339467288107369496902635607368346045543893434368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2027, a6 := 35776 }
def label : String := "405.b1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2027, a6 := 35776 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -3, 3, 0, -1, 2, 0, -2, 3, 0, -1, -4, 0, -8, -1, 0, -2, -3, 0, 1, 2, 0, 3, 1, 0,                    0, -5, 0, 4, -3, 0, -4, 8, 0, 3],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((6793144532911605 : Rat)/9007199254740992, (15514489941174957 : Rat)/4503599627370496),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (7799664282892730353865316593408424937256228247965 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (786956300004784477055154384639663420496054253634581 : Rat)/188339467288107369496902635607368346045543893434368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -26 }
def label : String := "405.b2"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -26 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -3, 3, 0, -1, 2, 0, -2, 3, 0, -1, -4, 0, -8, -1, 0, -2, -3, 0, 1, 2, 0, 3, 1, 0,                    0, -5, 0, 4, -3, 0, -4, 8, 0, 3],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((6793144532911605 : Rat)/9007199254740992, (15514489941174957 : Rat)/4503599627370496),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (7799664282892730353865316593408424937256228247965 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (786956300004784477055154384639663420496054253634581 : Rat)/188339467288107369496902635607368346045543893434368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -108, a6 := -412 }
def label : String := "405.c1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -108, a6 := -412 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -1, 0, 2, 0, 0, 0, -3, 0, -4, 0, 0, 4, -6, 0, -1, 2, 0, 0, -6, 0, 1, 0, 0, -4, -9, 0,                    -1, 0, 0, 0, -2, 0, 8, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((10386872940465649 : Rat)/9007199254740992, (37162540553911963 : Rat)/9007199254740992),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (158088533156445826524565512719446408480906038743417 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (1830416651222434167331252756838293847483759309393779 : Rat)/376678934576214738993805271214736692091087786868736,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -18, a6 := 29 }
def label : String := "405.c2"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -18, a6 := 29 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -1, 0, 2, 0, 0, 0, -3, 0, -4, 0, 0, 4, -6, 0, -1, 2, 0, 0, -6, 0, 1, 0, 0, -4, -9, 0,                    -1, 0, 0, 0, -2, 0, 8, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((10386872940465649 : Rat)/9007199254740992, (37162540553911963 : Rat)/9007199254740992),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (158088533156445826524565512719446408480906038743417 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (1830416651222434167331252756838293847483759309393779 : Rat)/376678934576214738993805271214736692091087786868736,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -162, a6 := -790 }
def label : String := "405.d1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1.nonsingular
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := 15 }
def label : String := "405.d2"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -12, a6 := 15 },   conductor := 405,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, -2, 1, 0, 2, 0, 0, 0, 3, 0, -4, 0, 0, 4, 6, 0, -1, -2, 0, 0, 6, 0, 1, 0, 0, -4, 9, 0, -1,                    0],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   geometricUpper := (6591692781151997 : Rat)/9007199254740992,   tail := (1261697881451271564920180475850512933296639690648286535917868270915010480412513653538597383514163572786650159588571045999083278922474742860019382919242523060924445669815425438843193908189848946828260567109408147173466884451171771290206066969685399661188844000955975313660328964340395979126355425539118699212883726676285780303069707650546061040244792416832404527483744920192648737937872625453541521767945595657565467159539103669056034899900958986059843000106500787691044432463014391902849482177424926587585207852204701084910584317 : Rat)/3855292103628482934914029327915679991418076812229749155173238870816250870025909474011853593367816365012086516240700330404996681370691787684060114661286099093519481181652438913058005343179490352974859635350764815791174577399110292577103082032647317115567217094170158071471244842875211424735660478686182881104355264787160128649589873378248622363204728782345219963531623537272446366262150760728603364157953152435535001045363989473056258472012897523410016681393690298338583852395974729107552000776411412768312614527611060962625323008,   box := { reLo := (651685883507486244695832922673162687533345820473248295840003917810197050622310287439763487098683729061960831750390681527135790636400906811017247331507092073925189756283085629446253182431204703089976987628820954404816954901582138278588549354599442793924857801014304798443597889048955724941484746222200146559055896018561214628561193538631967883561605368668657131054934017778839008536854006112280456328454349378370316663178276701257987898123864643279178732882019203689662315741368663883360238672376557085312675369375909428505621523940386368109 : Rat)/644349394915039407378915509516636058659203066002322057273748510825395856384529441589023211763042472945549212559332552767065896513941154295900828487376282475293346543746270593093998340623531198130203793361585388271197614142967650754326245790001118818439749094472401057028207029906906034810299726078809380910920839652798971277296333356855152151801349401767396172290469285325005138801395377199734205521571632491707919198690220077473603023509059679147146745476495481436843585105533555424087172300149344572782098418932860670561203661695038259200,            reHi := (13940655316111296670521150134181349487996982965882252319840413735985595013954195822283819412970369867286190325767840696235213895180805742332462851388862272737765866914987297726924227341188350890585068753054968083599503393710701171647793383132608883764031435673124015156068737075028215843947793133891411020585512643141194425677480943096659251271790653697424109408589582649409593954652577704647009827470974408604560516470078688387425747676220066309885426039927549061641313080008507342475395920520842754580186349195636160829200466469860203871 : Rat)/8368173959935576719206694928787481281288351506523663081477253387342803329669213527130171581338213934357781981290033152819037617064170835011699071264627045133679825243458059650571407021084820754937711602098511535989579404454125334471769425844170374265451286941200013727639052336453325127406489949075446505336634281205181445159692640998118859114303238983992158081694406302922144659758381522074470201578852370022180768814158702304851987318299476352560347343850590668010955650721215005507625614287653825620546732713413774942353294307727769600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1261697881451271564920180475850512933296639690648286535917868270915010480412513653538597383514163572786650159588571045999083278922474742860019382919242523060924445669815425438843193908189848946828260567109408147173466884451171771290206066969685399661188844000955975313660328964340395979126355425539118699212883726676285780303069707650546061040244792416832404527483744920192648737937872625453541521767945595657565467159539103669056034899900958986059843000106500787691044432463014391902849482177424926587585207852204701084910584317 : Rat)/7710584207256965869828058655831359982836153624459498310346477741632501740051818948023707186735632730024173032481400660809993362741383575368120229322572198187038962363304877826116010686358980705949719270701529631582349154798220585154206164065294634231134434188340316142942489685750422849471320957372365762208710529574320257299179746756497244726409457564690439927063247074544892732524301521457206728315906304871070002090727978946112516944025795046820033362787380596677167704791949458215104001552822825536625229055222121925250646016, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -225, a6 := -1250 }
def label : String := "405.e1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -225, a6 := -1250 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, -3, -3, 0, -1, -2, 0, -2, -3, 0, -1, 4, 0, -8, 1, 0, -2, 3, 0, 1, -2, 0, 3, -1,                    0, 0, 5, 0, 4, 3, 0, -4, -8, 0, 3],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((14244390900342725 : Rat)/9007199254740992, (23721107279009461 : Rat)/4503599627370496),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (319409018486032749201754049229313651971558505234925 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (1130155088869490671942962670504838622480625176965213 : Rat)/188339467288107369496902635607368346045543893434368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := 1 }
def label : String := "405.e2"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := 1 },   conductor := 405,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, -3, -3, 0, -1, -2, 0, -2, -3, 0, -1, 4, 0, -8, 1, 0, -2, 3, 0, 1, -2, 0, 3, -1,                    0, 0, 5, 0, 4, 3, 0, -4, -8, 0, 3],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   finite := ((14244390900342725 : Rat)/9007199254740992, (23721107279009461 : Rat)/4503599627370496),   tail := (32936099461342542210602441571712493896484375 : Rat)/44903628179575769781327875997392736922632192,   box := { reLo := (319409018486032749201754049229313651971558505234925 : Rat)/376678934576214738993805271214736692091087786868736,            reHi := (1130155088869490671942962670504838622480625176965213 : Rat)/188339467288107369496902635607368346045543893434368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := 47 }
def label : String := "405.f1"
def inputConductor : Nat := 405
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 405 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := 47 },   conductor := 405,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 1, 0, 0, 0, 0, 2, 5, 0, 4, 0, 0, -4, -4, 0, -5, 2, 0, 10, 6, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2160863737873753643035888671875,   alphaHi := (5397215081808807583452231630848 : Rat)/17286909902990029048919677734375,   geometricUpper := (6591692781151997 : Rat)/9007199254740992,   tail := (116596089500187746542157426283449760185374968950009146049838616541291112874173702328775048873613977398325720475396179415237485614431579570599434509916310886824097957804213330893652928678108769436951518566047169598431009887565609671686804979958711791516460308144179681578432790805683020391766577068492352624545381016963971378523245616489876852238134376498030584740091069964502733435005070493824436328125 : Rat)/47710417102834979418434947936125267734391866369366176246198400829838980550729136592553668918523385521311145349597598684407690246072689794310120472942296912112052133094188223271887544772322367356049012573547610800791097485673109881334484359985096761366038136087400778211804413796150629450246329807234639298279227689211626457750494289667389367437749001803679988342511061531541299683876006273676679839744,   box := { reLo := (11840483899544766978292586995928718152994100363677591158536311156410102472491566587076152608539570279931331305183252238197353878354297671184051034026770731951581902143926858645129572890218254771868771291291866160362478944820986605960300918027700701108561738844920049800703813823672841721592599330461633184791060776069327374487733370238610696582837139248886907566963272329076545054083823904756318047235717391 : Rat)/23038644762702469036470959834135849909921816391771386016645514784716796123238839123495278415721165017458332422140436440720207504474810811325442524576741044405228294289187080194645417057382886360725727436577538041540009109369259665048202480171403449612239325344564524786807174355954196702082198968966498797549564862704956242050847435066037314695177426735970011170773453947658320497848465289464363544414781440,            reHi := (1368900381817552346262946275901992524272180485518170829958845401674900051703116749153599429265662430417284887568448770353945840894616485528479276081006884190601821761859496531240577491112003723156080995170605934669441982183916333399033899096933287033854588124110422581852654007480876590843571653160450410855022090146164492325459215826939049063763160204422927772458482150255768397383269038793901315000227007579 : Rat)/253425092389727159401180558175494349009139980309485246183100662631884757355627230358448062572932815192041656643544800847922282549222918924579867770344151488457511237181057882141099587631211749967983001802352918456940100203061856315530227281885437945734632578790209772654878917915496163722904188658631486773045213489754518662559321785726410461646951694095670122878507993424241525476333118184107998988562595840,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (116596089500187746542157426283449760185374968950009146049838616541291112874173702328775048873613977398325720475396179415237485614431579570599434509916310886824097957804213330893652928678108769436951518566047169598431009887565609671686804979958711791516460308144179681578432790805683020391766577068492352624545381016963971378523245616489876852238134376498030584740091069964502733435005070493824436328125 : Rat)/95420834205669958836869895872250535468783732738732352492396801659677961101458273185107337837046771042622290699195197368815380492145379588620240945884593824224104266188376446543775089544644734712098025147095221601582194971346219762668968719970193522732076272174801556423608827592301258900492659614469278596558455378423252915500988579334778734875498003607359976685022123063082599367752012547353359679488, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N405.C405_f1
