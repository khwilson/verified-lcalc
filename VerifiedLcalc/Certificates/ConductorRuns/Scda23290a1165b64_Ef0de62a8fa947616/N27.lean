module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -270, a6 := -1708 }
def label : String := "27.a1"
def inputConductor : Nat := 27
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 27 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -270, a6 := -1708 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 3 = (List.range 3).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 3

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -30, a6 := 63 }
def label : String := "27.a2"
def inputConductor : Nat := 27
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 27 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -30, a6 := 63 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 3 = (List.range 3).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 3

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -7 }
def label : String := "27.a3"
def inputConductor : Nat := 27
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 27 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -7 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 3 = (List.range 3).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 3

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 0 }
def label : String := "27.a4"
def inputConductor : Nat := 27
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 27 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 0 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 3 = (List.range 3).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 3

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N27.C27_a4
