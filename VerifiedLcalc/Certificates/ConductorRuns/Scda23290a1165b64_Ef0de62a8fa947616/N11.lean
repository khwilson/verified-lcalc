module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7820, a6 := -263580 }
def label : String := "11.a1"
def inputConductor : Nat := 11
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.nonsingular
def minimality : MinimalityWitness := { primes := [11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 11 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7820, a6 := -263580 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 1 = (List.range 1).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 1

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -10, a6 := -20 }
def label : String := "11.a2"
def inputConductor : Nat := 11
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.nonsingular
def minimality : MinimalityWitness := { primes := [11, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 11 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -10, a6 := -20 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 1 = (List.range 1).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 1

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 0, a6 := 0 }
def label : String := "11.a3"
def inputConductor : Nat := 11
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.nonsingular
def minimality : MinimalityWitness := { primes := [11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 11 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 0, a6 := 0 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 1 = (List.range 1).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 1

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_Ef0de62a8fa947616.N11.C11_a3
