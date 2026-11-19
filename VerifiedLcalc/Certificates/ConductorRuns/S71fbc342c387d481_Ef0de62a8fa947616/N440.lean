module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -38, a6 := -87 }
def label : String := "440.a1"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -38, a6 := -87 },   conductor := 440,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, -1, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, -8, 0, 1, 0, 0, 0, 10, 0, 8,                    0, 0, 0, 2, 0, -10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   finite := ((8735512405057971 : Rat)/9007199254740992, (45052011276730313 : Rat)/9007199254740992),   tail := (672767606246448567121160207340717315673828125 : Rat)/709210442798726402043767696589547693945126912,   box := { reLo := (15781812750273192513615762689978845535753317927131 : Rat)/743661049268117335749445756219081562726205396877312,            reHi := (4425075457913336944467999221635362673908827932281793 : Rat)/743661049268117335749445756219081562726205396877312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 17, a6 := -318 }
def label : String := "440.a2"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 17, a6 := -318 },   conductor := 440,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, -1, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, -8, 0, 1, 0, 0, 0, 10, 0, 8,                    0, 0, 0, 2, 0, -10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   finite := ((8735512405057971 : Rat)/9007199254740992, (45052011276730313 : Rat)/9007199254740992),   tail := (672767606246448567121160207340717315673828125 : Rat)/709210442798726402043767696589547693945126912,   box := { reLo := (15781812750273192513615762689978845535753317927131 : Rat)/743661049268117335749445756219081562726205396877312,            reHi := (4425075457913336944467999221635362673908827932281793 : Rat)/743661049268117335749445756219081562726205396877312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -23, a6 := -38 }
def label : String := "440.b1"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -23, a6 := -38 },   conductor := 440,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, 1, 0, -4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -6, 0, 0, 0,                    0, 0, 2, 0, -2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   finite := ((4377147427709829 : Rat)/4503599627370496, (704092124058445 : Rat)/140737488355328),   tail := (672767606246448567121160207340717315673828125 : Rat)/709210442798726402043767696589547693945126912,   box := { reLo := (8666273742326039934856432471187134155556302528669 : Rat)/371830524634058667874722878109540781363102698438656,            reHi := (69154555702644520146937046515113851560314938180645 : Rat)/11619703894814333371085089940923149417596959326208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 2, a6 := -3 }
def label : String := "440.b2"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 2, a6 := -3 },   conductor := 440,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, 1, 0, -4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -6, 0, 0, 0,                    0, 0, 2, 0, -2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   finite := ((4377147427709829 : Rat)/4503599627370496, (704092124058445 : Rat)/140737488355328),   tail := (672767606246448567121160207340717315673828125 : Rat)/709210442798726402043767696589547693945126912,   box := { reLo := (8666273742326039934856432471187134155556302528669 : Rat)/371830524634058667874722878109540781363102698438656,            reHi := (69154555702644520146937046515113851560314938180645 : Rat)/11619703894814333371085089940923149417596959326208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7547, a6 := -12986 }
def label : String := "440.c1"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7547, a6 := -12986 },   conductor := 440,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, -3, 0, -1, 0, 6, 0, 0, 0, -6, 0, 4, 0, 0, 0, 4, 0, 1, 0, 0, 0, -2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   geometricUpper := (6675773436307851 : Rat)/9007199254740992,   tail := (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/1228031645810326314882858548424862774855858273936149141079364917565881710572562209538762216099518038041019232100500622736041417498346819520199302734705362521529630776826099669555915110202029202379687790368890212215703656211309974674126413956401461978208284886735673122936848321313397572197797300076322409580135558141746431334481631911692613928224923761804048907423133208313928565577337178759724388868450709474951231585484239664002331505487480945276549610803302448453313122400300352046497299239167729892772822046458402370373025792,   box := { reLo := (171703372674738153621393219275847795964528156004799434246509994940589499845742654613746252770326537652044273780748359627121252209600555112340469810619394649132909861532676483665758802545271775973113351837886772357312644352925706592140389265151403426488449947876603594741387284753310524136106862684350687718882928201558270602354229095881954547850399328319633873914391113775383422750820431541603903864588184419206408591716068664915118155349027617418109371564354204138680336113542972940926179522681173576518101374723057691980301355680131577 : Rat)/148477591499197978495383906442941172897927884930341135796754247104015120833154014754647884792889024937474561270094426280630991264437181449058249090762452898756520030092943812094505289331318989721390852177936649666108776568949449825175235479066282653362679645593427861883097446563830927426779773215395411667045210424855182229697387307506221079904542651645348096148586081239281953230044966838872527691808048219220191683525353327949538295275687221463528151879654619052583518357225054657377047796677571738952236275850594893934632170107699200,            reHi := (1387511921805570153883995891100097520793244045869086106745068516863581744936252032009340259535924522697901177922327142157696657435392313342743778384663089687080580820189007797792110280554760970676681571006106939857391638704865798540052922703930906979811231454420036573075195594037832990158534220717804448325654969965694920151145483661896754192127332510268754073254175230446413995375111576296097208460700795361503442798939787445844778877332614629527547052405588013067589633359272135408212130969031690135119943544501055487671805707328265867 : Rat)/631524689176588735200366215403976455392519937237050964255528064349077647277015076089769003319087986067391800602134959780283816178072811763327752799376299662711065194661987680775295830622543436281649091263490549913182663006598326589745334904295255552302597425924046505876107806051494211321903302076148484290498961673717375083646220681259793659860654744998213902285319465537745907738457925621337817782490231759083215293927836154878702882572589648624873072661464313036988564746063899142710376628535271796343511626617863615535302163524747264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/2456063291620652629765717096849725549711716547872298282158729835131763421145124419077524432199036076082038464201001245472082834996693639040398605469410725043059261553652199339111830220404058404759375580737780424431407312422619949348252827912802923956416569773471346245873696642626795144395594600152644819160271116283492862668963263823385227856449847523608097814846266416627857131154674357519448777736901418949902463170968479328004663010974961890553099221606604896906626244800600704092994598478335459785545644092916804740746051584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -5047, a6 := 137514 }
def label : String := "440.c2"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -5047, a6 := 137514 },   conductor := 440,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, -3, 0, -1, 0, 6, 0, 0, 0, -6, 0, 4, 0, 0, 0, 4, 0, 1, 0, 0, 0, -2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   geometricUpper := (6675773436307851 : Rat)/9007199254740992,   tail := (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/1228031645810326314882858548424862774855858273936149141079364917565881710572562209538762216099518038041019232100500622736041417498346819520199302734705362521529630776826099669555915110202029202379687790368890212215703656211309974674126413956401461978208284886735673122936848321313397572197797300076322409580135558141746431334481631911692613928224923761804048907423133208313928565577337178759724388868450709474951231585484239664002331505487480945276549610803302448453313122400300352046497299239167729892772822046458402370373025792,   box := { reLo := (171703372674738153621393219275847795964528156004799434246509994940589499845742654613746252770326537652044273780748359627121252209600555112340469810619394649132909861532676483665758802545271775973113351837886772357312644352925706592140389265151403426488449947876603594741387284753310524136106862684350687718882928201558270602354229095881954547850399328319633873914391113775383422750820431541603903864588184419206408591716068664915118155349027617418109371564354204138680336113542972940926179522681173576518101374723057691980301355680131577 : Rat)/148477591499197978495383906442941172897927884930341135796754247104015120833154014754647884792889024937474561270094426280630991264437181449058249090762452898756520030092943812094505289331318989721390852177936649666108776568949449825175235479066282653362679645593427861883097446563830927426779773215395411667045210424855182229697387307506221079904542651645348096148586081239281953230044966838872527691808048219220191683525353327949538295275687221463528151879654619052583518357225054657377047796677571738952236275850594893934632170107699200,            reHi := (1387511921805570153883995891100097520793244045869086106745068516863581744936252032009340259535924522697901177922327142157696657435392313342743778384663089687080580820189007797792110280554760970676681571006106939857391638704865798540052922703930906979811231454420036573075195594037832990158534220717804448325654969965694920151145483661896754192127332510268754073254175230446413995375111576296097208460700795361503442798939787445844778877332614629527547052405588013067589633359272135408212130969031690135119943544501055487671805707328265867 : Rat)/631524689176588735200366215403976455392519937237050964255528064349077647277015076089769003319087986067391800602134959780283816178072811763327752799376299662711065194661987680775295830622543436281649091263490549913182663006598326589745334904295255552302597425924046505876107806051494211321903302076148484290498961673717375083646220681259793659860654744998213902285319465537745907738457925621337817782490231759083215293927836154878702882572589648624873072661464313036988564746063899142710376628535271796343511626617863615535302163524747264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/2456063291620652629765717096849725549711716547872298282158729835131763421145124419077524432199036076082038464201001245472082834996693639040398605469410725043059261553652199339111830220404058404759375580737780424431407312422619949348252827912802923956416569773471346245873696642626795144395594600152644819160271116283492862668963263823385227856449847523608097814846266416627857131154674357519448777736901418949902463170968479328004663010974961890553099221606604896906626244800600704092994598478335459785545644092916804740746051584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -5042, a6 := 137801 }
def label : String := "440.c3"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -5042, a6 := 137801 },   conductor := 440,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, -3, 0, -1, 0, 6, 0, 0, 0, -6, 0, 4, 0, 0, 0, 4, 0, 1, 0, 0, 0, -2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   geometricUpper := (6675773436307851 : Rat)/9007199254740992,   tail := (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/1228031645810326314882858548424862774855858273936149141079364917565881710572562209538762216099518038041019232100500622736041417498346819520199302734705362521529630776826099669555915110202029202379687790368890212215703656211309974674126413956401461978208284886735673122936848321313397572197797300076322409580135558141746431334481631911692613928224923761804048907423133208313928565577337178759724388868450709474951231585484239664002331505487480945276549610803302448453313122400300352046497299239167729892772822046458402370373025792,   box := { reLo := (171703372674738153621393219275847795964528156004799434246509994940589499845742654613746252770326537652044273780748359627121252209600555112340469810619394649132909861532676483665758802545271775973113351837886772357312644352925706592140389265151403426488449947876603594741387284753310524136106862684350687718882928201558270602354229095881954547850399328319633873914391113775383422750820431541603903864588184419206408591716068664915118155349027617418109371564354204138680336113542972940926179522681173576518101374723057691980301355680131577 : Rat)/148477591499197978495383906442941172897927884930341135796754247104015120833154014754647884792889024937474561270094426280630991264437181449058249090762452898756520030092943812094505289331318989721390852177936649666108776568949449825175235479066282653362679645593427861883097446563830927426779773215395411667045210424855182229697387307506221079904542651645348096148586081239281953230044966838872527691808048219220191683525353327949538295275687221463528151879654619052583518357225054657377047796677571738952236275850594893934632170107699200,            reHi := (1387511921805570153883995891100097520793244045869086106745068516863581744936252032009340259535924522697901177922327142157696657435392313342743778384663089687080580820189007797792110280554760970676681571006106939857391638704865798540052922703930906979811231454420036573075195594037832990158534220717804448325654969965694920151145483661896754192127332510268754073254175230446413995375111576296097208460700795361503442798939787445844778877332614629527547052405588013067589633359272135408212130969031690135119943544501055487671805707328265867 : Rat)/631524689176588735200366215403976455392519937237050964255528064349077647277015076089769003319087986067391800602134959780283816178072811763327752799376299662711065194661987680775295830622543436281649091263490549913182663006598326589745334904295255552302597425924046505876107806051494211321903302076148484290498961673717375083646220681259793659860654744998213902285319465537745907738457925621337817782490231759083215293927836154878702882572589648624873072661464313036988564746063899142710376628535271796343511626617863615535302163524747264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/2456063291620652629765717096849725549711716547872298282158729835131763421145124419077524432199036076082038464201001245472082834996693639040398605469410725043059261553652199339111830220404058404759375580737780424431407312422619949348252827912802923956416569773471346245873696642626795144395594600152644819160271116283492862668963263823385227856449847523608097814846266416627857131154674357519448777736901418949902463170968479328004663010974961890553099221606604896906626244800600704092994598478335459785545644092916804740746051584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2627, a6 := 269646 }
def label : String := "440.c4"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2627, a6 := 269646 },   conductor := 440,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, -3, 0, -1, 0, 6, 0, 0, 0, -6, 0, 4, 0, 0, 0, 4, 0, 1, 0, 0, 0, -2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   geometricUpper := (6675773436307851 : Rat)/9007199254740992,   tail := (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/1228031645810326314882858548424862774855858273936149141079364917565881710572562209538762216099518038041019232100500622736041417498346819520199302734705362521529630776826099669555915110202029202379687790368890212215703656211309974674126413956401461978208284886735673122936848321313397572197797300076322409580135558141746431334481631911692613928224923761804048907423133208313928565577337178759724388868450709474951231585484239664002331505487480945276549610803302448453313122400300352046497299239167729892772822046458402370373025792,   box := { reLo := (171703372674738153621393219275847795964528156004799434246509994940589499845742654613746252770326537652044273780748359627121252209600555112340469810619394649132909861532676483665758802545271775973113351837886772357312644352925706592140389265151403426488449947876603594741387284753310524136106862684350687718882928201558270602354229095881954547850399328319633873914391113775383422750820431541603903864588184419206408591716068664915118155349027617418109371564354204138680336113542972940926179522681173576518101374723057691980301355680131577 : Rat)/148477591499197978495383906442941172897927884930341135796754247104015120833154014754647884792889024937474561270094426280630991264437181449058249090762452898756520030092943812094505289331318989721390852177936649666108776568949449825175235479066282653362679645593427861883097446563830927426779773215395411667045210424855182229697387307506221079904542651645348096148586081239281953230044966838872527691808048219220191683525353327949538295275687221463528151879654619052583518357225054657377047796677571738952236275850594893934632170107699200,            reHi := (1387511921805570153883995891100097520793244045869086106745068516863581744936252032009340259535924522697901177922327142157696657435392313342743778384663089687080580820189007797792110280554760970676681571006106939857391638704865798540052922703930906979811231454420036573075195594037832990158534220717804448325654969965694920151145483661896754192127332510268754073254175230446413995375111576296097208460700795361503442798939787445844778877332614629527547052405588013067589633359272135408212130969031690135119943544501055487671805707328265867 : Rat)/631524689176588735200366215403976455392519937237050964255528064349077647277015076089769003319087986067391800602134959780283816178072811763327752799376299662711065194661987680775295830622543436281649091263490549913182663006598326589745334904295255552302597425924046505876107806051494211321903302076148484290498961673717375083646220681259793659860654744998213902285319465537745907738457925621337817782490231759083215293927836154878702882572589648624873072661464313036988564746063899142710376628535271796343511626617863615535302163524747264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/2456063291620652629765717096849725549711716547872298282158729835131763421145124419077524432199036076082038464201001245472082834996693639040398605469410725043059261553652199339111830220404058404759375580737780424431407312422619949348252827912802923956416569773471346245873696642626795144395594600152644819160271116283492862668963263823385227856449847523608097814846266416627857131154674357519448777736901418949902463170968479328004663010974961890553099221606604896906626244800600704092994598478335459785545644092916804740746051584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -67, a6 := -226 }
def label : String := "440.d1"
def inputConductor : Nat := 440
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 440 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -67, a6 := -226 },   conductor := 440,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 3, 0, 1, 0, 1, 0, 6, 0, -1, 0, -6, 0, 3, 0, 3, 0, -5, 0, 3, 0, -2, 0, 1, 0, 9, 0, -5, 0, 5, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18018398810584921360015869140625,   alphaHi := (168662971306525236982882238464 : Rat)/563074962830778789520263671875,   geometricUpper := (6675773436307851 : Rat)/9007199254740992,   tail := (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/1228031645810326314882858548424862774855858273936149141079364917565881710572562209538762216099518038041019232100500622736041417498346819520199302734705362521529630776826099669555915110202029202379687790368890212215703656211309974674126413956401461978208284886735673122936848321313397572197797300076322409580135558141746431334481631911692613928224923761804048907423133208313928565577337178759724388868450709474951231585484239664002331505487480945276549610803302448453313122400300352046497299239167729892772822046458402370373025792,   box := { reLo := (292604406630153158196505017334618413971584900766904990810752879634642864589335058430875818069818075771436330385519170994877186386527320908617101807709914552006069540754572502056460724578197114870630161681358006327552773105719208948119242270641357530188817662997548867742473696002011512087109086448098276681540969987842325239146636488840368005628396009215243683122661038541863188308700344270978385636821338318135512419595268777480090236450856144821965235492341654875953225813902909750765310858895148261347137513657052022583978508197947897 : Rat)/148477591499197978495383906442941172897927884930341135796754247104015120833154014754647884792889024937474561270094426280630991264437181449058249090762452898756520030092943812094505289331318989721390852177936649666108776568949449825175235479066282653362679645593427861883097446563830927426779773215395411667045210424855182229697387307506221079904542651645348096148586081239281953230044966838872527691808048219220191683525353327949538295275687221463528151879654619052583518357225054657377047796677571738952236275850594893934632170107699200,            reHi := (4075166399062719228511094802710565684265985490958256410691958997526909837213227373672803549554829712665888665380662398151002927842821982224938052369822232744395182549501284210348609025255836064450289024133580485178617905441859332425876573383416602458558866377634820357555335421925110321485854923197032108295629086289514465628992385901408397161846505702855042987552172903481776277036653155967484606243003053818559161566418988312660830948977436880010722787842850994978696495055865398232647733618031120242823624209664674769536159261974970739 : Rat)/1353267191092690146857927604437092404412542722650823494833274423605166387022175163049505007112331398715839572718860628100608177524441739492845184570092070705809425417132830744518491065619735934889248052707479749813962849299853556978025717652061261897791280198408671084020231012967487595689792790163175323479640632157965803750670472888413843556844260167853315504897113140438026945153838412045723895248193353769464032772702506046168649034084120675624728012845994956507832638741565498162950807061147010992164667771323993461861361778981601280,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (638979528682797463281795005646633855820445646912930466996698667040929375489550640258416736801453428064000941361654348863908838359602858634579367872882103932159214569656925999386764529480902385539138627768263881274541136325819934530784581379456466839102238738827320860052670599953135059671313269222095711844125398022694137296942396241085927893233980608365387549846498647090735318113192774974647396664152274333634302370955793142828001383444620915343362604362049583539408280354170163284723448715873314024465203045176641257512733657 : Rat)/2456063291620652629765717096849725549711716547872298282158729835131763421145124419077524432199036076082038464201001245472082834996693639040398605469410725043059261553652199339111830220404058404759375580737780424431407312422619949348252827912802923956416569773471346245873696642626795144395594600152644819160271116283492862668963263823385227856449847523608097814846266416627857131154674357519448777736901418949902463170968479328004663010974961890553099221606604896906626244800600704092994598478335459785545644092916804740746051584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N440.C440_d1
