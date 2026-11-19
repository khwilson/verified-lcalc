module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5442, a6 := -39034 }
def label : String := "450.a1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5442, a6 := -39034 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -6, 0, 4, 2, 0, 1, -6, 0, -4, 0, 0, 6, 0, 0, 0, -4, 0, -2, 6, 0, -4,                    -1, 0, 6, 0, 0, -8, 4, 0, 0, 0, 0, -8, -6, 0, 0, 0, 0, -3, 0, 0, 4, -6, 0, 0, 2, 0, -6, -6, 0, 2, 4,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((3670823885283971 : Rat)/2251799813685248, (1855750248554911 : Rat)/562949953421312),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (227447090355026683310482240035503153576792386725529 : Rat)/370377500302957685297695171089421574174149026250752,            reHi := (399318113240522001116643767841183010145005022284589 : Rat)/92594375075739421324423792772355393543537256562688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3192, a6 := 70216 }
def label : String := "450.a2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3192, a6 := 70216 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -6, 0, 4, 2, 0, 1, -6, 0, -4, 0, 0, 6, 0, 0, 0, -4, 0, -2, 6, 0, -4,                    -1, 0, 6, 0, 0, -8, 4, 0, 0, 0, 0, -8, -6, 0, 0, 0, 0, -3, 0, 0, 4, -6, 0, 0, 2, 0, -6, -6, 0, 2, 4,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((3670823885283971 : Rat)/2251799813685248, (1855750248554911 : Rat)/562949953421312),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (227447090355026683310482240035503153576792386725529 : Rat)/370377500302957685297695171089421574174149026250752,            reHi := (399318113240522001116643767841183010145005022284589 : Rat)/92594375075739421324423792772355393543537256562688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -192, a6 := 1216 }
def label : String := "450.a3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -192, a6 := 1216 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -6, 0, 4, 2, 0, 1, -6, 0, -4, 0, 0, 6, 0, 0, 0, -4, 0, -2, 6, 0, -4,                    -1, 0, 6, 0, 0, -8, 4, 0, 0, 0, 0, -8, -6, 0, 0, 0, 0, -3, 0, 0, 4, -6, 0, 0, 2, 0, -6, -6, 0, 2, 4,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((3670823885283971 : Rat)/2251799813685248, (1855750248554911 : Rat)/562949953421312),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (227447090355026683310482240035503153576792386725529 : Rat)/370377500302957685297695171089421574174149026250752,            reHi := (399318113240522001116643767841183010145005022284589 : Rat)/92594375075739421324423792772355393543537256562688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1308, a6 := -5284 }
def label : String := "450.a4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1308, a6 := -5284 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -6, 0, 4, 2, 0, 1, -6, 0, -4, 0, 0, 6, 0, 0, 0, -4, 0, -2, 6, 0, -4,                    -1, 0, 6, 0, 0, -8, 4, 0, 0, 0, 0, -8, -6, 0, 0, 0, 0, -3, 0, 0, 4, -6, 0, 0, 2, 0, -6, -6, 0, 2, 4,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((3670823885283971 : Rat)/2251799813685248, (1855750248554911 : Rat)/562949953421312),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (227447090355026683310482240035503153576792386725529 : Rat)/370377500302957685297695171089421574174149026250752,            reHi := (399318113240522001116643767841183010145005022284589 : Rat)/92594375075739421324423792772355393543537256562688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7452, a6 := -244944 }
def label : String := "450.b1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0, 2, 2, 1, 0, 0, 1],                kodaira := -14 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7452, a6 := -244944 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -2, 0, -6, 2, 0, 1, 2, 0, 0, 0, 0, 2, -4, 0, 0, 6, 0, -2, 0, 0, -8,                    -1, 0, -2, 0, 0, -2, 0, 0, 0, -2, 0, 4, -2, 0, 4, -8, 0, -3, 0, 0, -6, 6, 0, 0, 2, 0, 0, -10, 0, 2,                    8, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((14787734723129921 : Rat)/9007199254740992, (3712503885580225 : Rat)/1125899906842624),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (926966586111994896075314537686355043610670278654579 : Rat)/1481510001211830741190780684357686296696596105003008,            reHi := (798801264470319108114501542180078896055267901932275 : Rat)/185188750151478842648847585544710787087074513125376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -477, a6 := 4131 }
def label : String := "450.b2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -477, a6 := 4131 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -2, 0, -6, 2, 0, 1, 2, 0, 0, 0, 0, 2, -4, 0, 0, 6, 0, -2, 0, 0, -8,                    -1, 0, -2, 0, 0, -2, 0, 0, 0, -2, 0, 4, -2, 0, 4, -8, 0, -3, 0, 0, -6, 6, 0, 0, 2, 0, 0, -10, 0, 2,                    8, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((14787734723129921 : Rat)/9007199254740992, (3712503885580225 : Rat)/1125899906842624),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (926966586111994896075314537686355043610670278654579 : Rat)/1481510001211830741190780684357686296696596105003008,            reHi := (798801264470319108114501542180078896055267901932275 : Rat)/185188750151478842648847585544710787087074513125376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -252, a6 := -7344 }
def label : String := "450.b3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 1, 2, 1],                kodaira := -9 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -252, a6 := -7344 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -2, 0, -6, 2, 0, 1, 2, 0, 0, 0, 0, 2, -4, 0, 0, 6, 0, -2, 0, 0, -8,                    -1, 0, -2, 0, 0, -2, 0, 0, 0, -2, 0, 4, -2, 0, 4, -8, 0, -3, 0, 0, -6, 6, 0, 0, 2, 0, 0, -10, 0, 2,                    8, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((14787734723129921 : Rat)/9007199254740992, (3712503885580225 : Rat)/1125899906842624),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (926966586111994896075314537686355043610670278654579 : Rat)/1481510001211830741190780684357686296696596105003008,            reHi := (798801264470319108114501542180078896055267901932275 : Rat)/185188750151478842648847585544710787087074513125376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := 81 }
def label : String := "450.b4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := 81 },   conductor := 450,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, -2, 0, -6, 2, 0, 1, 2, 0, 0, 0, 0, 2, -4, 0, 0, 6, 0, -2, 0, 0, -8,                    -1, 0, -2, 0, 0, -2, 0, 0, 0, -2, 0, 4, -2, 0, 4, -8, 0, -3, 0, 0, -6, 6, 0, 0, 2, 0, 0, -10, 0, 2,                    8, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   finite := ((14787734723129921 : Rat)/9007199254740992, (3712503885580225 : Rat)/1125899906842624),   tail := (1435594229415607168136525824989986419677734375 : Rat)/1412878037654715291205197033269583031365009408,   box := { reLo := (926966586111994896075314537686355043610670278654579 : Rat)/1481510001211830741190780684357686296696596105003008,            reHi := (798801264470319108114501542180078896055267901932275 : Rat)/185188750151478842648847585544710787087074513125376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -28242, a6 := 1833916 }
def label : String := "450.c1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -28242, a6 := 1833916 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, 3, 0, 4, 2, 0, 1, -3, 0, 5, 0, 0, -3, 6, 0, 0, -4, 0, -2, 0, 0, 2,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (8106680306019526888747446090563895316183077409572081513744389449230831452275087922625503842739328403760444670224926013250125362134448312537010150768519729260519876500867887667519422766683152031186355389320443641186640656639013325046319577697301809165190246037523671877344480795817070598255441970741096470411935300383072770297996960356868580385834189101974617715738190578916708797161441515006770009192972377830003805837852927901083702996888759609353412662890292779903528145518244495960837531576981507659457210663067 : Rat)/18305443055274106393930013752203620977612800402035075738174974856123288694192229721471527810008608556024466800139317729810618859254115480792803036296064597469487022560366062541626831512378230491832433667963535394207719056657026526694512832995567935787660932724005919544280423535747260349955283208100204971654375518046811335962655575100372511576944997592524809384563027042295092396113008407313780890636585916814917302031888653723972518863699082657111415969532256328042169162584468004079781913521344921237810038439936,            reHi := (21996450022333086896926209361810780215396812271622305582347684663983233912120680632678944470479250664656893065481289877212971144385859032893145914436508733138462846878005072664486565465407672500251068297270192035823414556272360585934401121608587264266120366466863018341668410087180114491766117906950535590228329519117899291171259107242983079366925281814705882919991319115356212446561609189227738648916855906136759399808098932011491946786410003018536380404869949209856465943427296796049033854850120136102506938580877 : Rat)/13581457750687240227754526332280105886615948685380862644452400699704375482787783341736939988070903122211701174296913154375620443962730840588208704348693088445103274802852239950239262089829009719746644334295526260218630267842310003676574037383808468487619401698456004823175798107167322195128113347945313366066149577905698733133583168622857024718378546600905503736933858773315713713245135269942482596278757293120745095055917388246818320447260609713340727977394899856289351314175573035284999484225513973821600996261888,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -117, a6 := 5791 }
def label : String := "450.c2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -117, a6 := 5791 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, 3, 0, 4, 2, 0, 1, -3, 0, 5, 0, 0, -3, 6, 0, 0, -4, 0, -2, 0, 0, 2,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (8106680306019526888747446090563895316183077409572081513744389449230831452275087922625503842739328403760444670224926013250125362134448312537010150768519729260519876500867887667519422766683152031186355389320443641186640656639013325046319577697301809165190246037523671877344480795817070598255441970741096470411935300383072770297996960356868580385834189101974617715738190578916708797161441515006770009192972377830003805837852927901083702996888759609353412662890292779903528145518244495960837531576981507659457210663067 : Rat)/18305443055274106393930013752203620977612800402035075738174974856123288694192229721471527810008608556024466800139317729810618859254115480792803036296064597469487022560366062541626831512378230491832433667963535394207719056657026526694512832995567935787660932724005919544280423535747260349955283208100204971654375518046811335962655575100372511576944997592524809384563027042295092396113008407313780890636585916814917302031888653723972518863699082657111415969532256328042169162584468004079781913521344921237810038439936,            reHi := (21996450022333086896926209361810780215396812271622305582347684663983233912120680632678944470479250664656893065481289877212971144385859032893145914436508733138462846878005072664486565465407672500251068297270192035823414556272360585934401121608587264266120366466863018341668410087180114491766117906950535590228329519117899291171259107242983079366925281814705882919991319115356212446561609189227738648916855906136759399808098932011491946786410003018536380404869949209856465943427296796049033854850120136102506938580877 : Rat)/13581457750687240227754526332280105886615948685380862644452400699704375482787783341736939988070903122211701174296913154375620443962730840588208704348693088445103274802852239950239262089829009719746644334295526260218630267842310003676574037383808468487619401698456004823175798107167322195128113347945313366066149577905698733133583168622857024718378546600905503736933858773315713713245135269942482596278757293120745095055917388246818320447260609713340727977394899856289351314175573035284999484225513973821600996261888,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := -59 }
def label : String := "450.c3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := -59 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, 3, 0, 4, 2, 0, 1, -3, 0, 5, 0, 0, -3, 6, 0, 0, -4, 0, -2, 0, 0, 2,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (8106680306019526888747446090563895316183077409572081513744389449230831452275087922625503842739328403760444670224926013250125362134448312537010150768519729260519876500867887667519422766683152031186355389320443641186640656639013325046319577697301809165190246037523671877344480795817070598255441970741096470411935300383072770297996960356868580385834189101974617715738190578916708797161441515006770009192972377830003805837852927901083702996888759609353412662890292779903528145518244495960837531576981507659457210663067 : Rat)/18305443055274106393930013752203620977612800402035075738174974856123288694192229721471527810008608556024466800139317729810618859254115480792803036296064597469487022560366062541626831512378230491832433667963535394207719056657026526694512832995567935787660932724005919544280423535747260349955283208100204971654375518046811335962655575100372511576944997592524809384563027042295092396113008407313780890636585916814917302031888653723972518863699082657111415969532256328042169162584468004079781913521344921237810038439936,            reHi := (21996450022333086896926209361810780215396812271622305582347684663983233912120680632678944470479250664656893065481289877212971144385859032893145914436508733138462846878005072664486565465407672500251068297270192035823414556272360585934401121608587264266120366466863018341668410087180114491766117906950535590228329519117899291171259107242983079366925281814705882919991319115356212446561609189227738648916855906136759399808098932011491946786410003018536380404869949209856465943427296796049033854850120136102506938580877 : Rat)/13581457750687240227754526332280105886615948685380862644452400699704375482787783341736939988070903122211701174296913154375620443962730840588208704348693088445103274802852239950239262089829009719746644334295526260218630267842310003676574037383808468487619401698456004823175798107167322195128113347945313366066149577905698733133583168622857024718378546600905503736933858773315713713245135269942482596278757293120745095055917388246818320447260609713340727977394899856289351314175573035284999484225513973821600996261888,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 198, a6 := 436 }
def label : String := "450.c4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 198, a6 := 436 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, -2, -1, 0, 0, 3, 0, 4, 2, 0, 1, -3, 0, 5, 0, 0, -3, 6, 0, 0, -4, 0, -2, 0, 0, 2,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (8106680306019526888747446090563895316183077409572081513744389449230831452275087922625503842739328403760444670224926013250125362134448312537010150768519729260519876500867887667519422766683152031186355389320443641186640656639013325046319577697301809165190246037523671877344480795817070598255441970741096470411935300383072770297996960356868580385834189101974617715738190578916708797161441515006770009192972377830003805837852927901083702996888759609353412662890292779903528145518244495960837531576981507659457210663067 : Rat)/18305443055274106393930013752203620977612800402035075738174974856123288694192229721471527810008608556024466800139317729810618859254115480792803036296064597469487022560366062541626831512378230491832433667963535394207719056657026526694512832995567935787660932724005919544280423535747260349955283208100204971654375518046811335962655575100372511576944997592524809384563027042295092396113008407313780890636585916814917302031888653723972518863699082657111415969532256328042169162584468004079781913521344921237810038439936,            reHi := (21996450022333086896926209361810780215396812271622305582347684663983233912120680632678944470479250664656893065481289877212971144385859032893145914436508733138462846878005072664486565465407672500251068297270192035823414556272360585934401121608587264266120366466863018341668410087180114491766117906950535590228329519117899291171259107242983079366925281814705882919991319115356212446561609189227738648916855906136759399808098932011491946786410003018536380404869949209856465943427296796049033854850120136102506938580877 : Rat)/13581457750687240227754526332280105886615948685380862644452400699704375482787783341736939988070903122211701174296913154375620443962730840588208704348693088445103274802852239950239262089829009719746644334295526260218630267842310003676574037383808468487619401698456004823175798107167322195128113347945313366066149577905698733133583168622857024718378546600905503736933858773315713713245135269942482596278757293120745095055917388246818320447260609713340727977394899856289351314175573035284999484225513973821600996261888,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1200042, a6 := 506291116 }
def label : String := "450.d1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1200042, a6 := 506291116 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -102042, a6 := 1733116 }
def label : String := "450.d2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -102042, a6 := 1733116 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -75042, a6 := 7916116 }
def label : String := "450.d3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -75042, a6 := 7916116 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -64917, a6 := -6350009 }
def label : String := "450.d4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 2],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -64917, a6 := -6350009 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15417, a6 := 638491 }
def label : String := "450.d5"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1, 1, 2, 0, 2, 1, 0, 2, 0],                kodaira := -16 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15417, a6 := 638491 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4167, a6 := -92759 }
def label : String := "450.d6"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 2, 1, 2, 1],                kodaira := -10 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4167, a6 := -92759 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3042, a6 := 212116 }
def label : String := "450.d7"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3042, a6 := 212116 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d7

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 333, a6 := -7259 }
def label : String := "450.d8"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 1],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 333, a6 := -7259 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 4, -1, 0, 0, 0, 0, -2, -4, 0, 1, 6, 0, -4, 0, 0, 0, 0, 0, 0, 2, 0, 4, 6, 0, 8,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (29343174645003289592797295939589651577322362326705991699501313464121201091339865828125845848866600245544106239240987295510823833825279989927814188328694894614025799478858420448395647122422655737057768779363409620362996833290728190279518161205998519223274024844310363416556896110895598864340465152549471712903794533839268936602445732532050757884191710016435541536925462990030420535223668800805667042390750821741087945561637865060650991250281125491468905467134594314157481164695720622473560313702273071832504146793229 : Rat)/48259804418449916856724581710355000759161019241728836037006751893415942921052241992970391499113604374973594291276383105864358810760849903908298913871443029692283968568237801246107101259906244023921870579176593312002168422095797206740079286988315467076560640817833787889466571139697322740791201184991449470725171820305229885719728334355527530521036811834838133832029798566050698135207022164736331438950999235239327432629524632545018458822479399732384642101494130319383900519540870192573970499283545701445135555887104,            reHi := (2778461811953111473605550368486372025676479214943566000200715635196427470788986752042542658270231208635758650262639531934325405122372834305979750282437708518316037724524339556680684060081952415639248280682341855988072090632015853217149913423655839372897629222908637739007367299032865865609174173869630989292127953555670420813604507026152478137795857240294115467341669595026568496582324475080783964932354370279847646152308824268676931489484255734802875165908207024999003512281416223942540413409521293401146238970029 : Rat)/1556767884466126350216921990656612927714871588442865678613121028819869126485556193321625532229471108870115944879883325995624477766479029158332223028111065473944644147362509717616358105158265936255544212231503010064586078132122490540002557644784369905695504542510767351273115198054752346477135522096498370023392639364684835023217043043726694532936671349510907542968703179550022520490549102088268756095193523717397659117081439759516724478144496765560794906499810655463996790952931296534644209654307925853068888899584,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_d8

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -28730, a6 := -1867103 }
def label : String := "450.e1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -28730, a6 := -1867103 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -2, 1, 0, 0, 6, 0, 4, -2, 0, 1, 6, 0, -4, 0, 0, 6, 0, 0, 0, 4, 0, -2, -6, 0, -4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (27602209720573091846599007898656397170583104051921099194817821761233241185036803855921222301753622006053437593852823436534196313906110168384348876029683773369423379895277687141414349878777151012024046669518940922596695388698801602030207154668545277565349698421698250738495069824515492720955636938901397919048304271050416727252210532169272871623741740855235938582908112737109789414254490448336675939691079888332659383073761891864555008211057341479146018714251430947535644162172581191982386199671220136097539089121425 : Rat)/17124446729127389852386141897222742204863587472871522464744331317018560391341118126537880854524182197571275393678716585951869255431269320741654453309221720213391085620987606893779939156740925298810986334546533110710446859453347395940028134092628068962650549967618440864004267178602275811248490743061482070257319033011533185255387473480993639862303384844619982972655734975050247725396040122970956317047128760891374250287895837354683969259589464421168743971497917210103964700482244261881086306197387184383757777895424,            reHi := (1480349058118740723720850143333554405529118405615664067435327860566669368596471295452204681798094889893594164861661492077515122517878140525995046235159129721420740269943234134331840751705484228347931048820039415497607505824050612049330073746463857005189481626044993066223981799883398346674752177883829934910991015712926220010517234855375763811468133832018849894275822999037074849849515941065237190237307327810044419980002204134438915428726918397058447009373455653952402333893839825596765866175914770339582058294029937 : Rat)/530857848602949085423970398813905008350771211659017196407074270827575372131574661922674306490249648124709537204040214164507946918369348942991288052585873326615123654250615813707178113858968684263140576370942526432023852643053769274140872156871470137842167048996171666784132282536670550148703213034905944177976890023357528742917011677910802835731404930183219472152327784226557679487277243812099645828460991587632601758924770957995203047047273397056231063116435433513222905714949572118313675492119002715896491114758144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1730, a6 := -31103 }
def label : String := "450.e2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1730, a6 := -31103 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -2, 1, 0, 0, 6, 0, 4, -2, 0, 1, 6, 0, -4, 0, 0, 6, 0, 0, 0, 4, 0, -2, -6, 0, -4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (27602209720573091846599007898656397170583104051921099194817821761233241185036803855921222301753622006053437593852823436534196313906110168384348876029683773369423379895277687141414349878777151012024046669518940922596695388698801602030207154668545277565349698421698250738495069824515492720955636938901397919048304271050416727252210532169272871623741740855235938582908112737109789414254490448336675939691079888332659383073761891864555008211057341479146018714251430947535644162172581191982386199671220136097539089121425 : Rat)/17124446729127389852386141897222742204863587472871522464744331317018560391341118126537880854524182197571275393678716585951869255431269320741654453309221720213391085620987606893779939156740925298810986334546533110710446859453347395940028134092628068962650549967618440864004267178602275811248490743061482070257319033011533185255387473480993639862303384844619982972655734975050247725396040122970956317047128760891374250287895837354683969259589464421168743971497917210103964700482244261881086306197387184383757777895424,            reHi := (1480349058118740723720850143333554405529118405615664067435327860566669368596471295452204681798094889893594164861661492077515122517878140525995046235159129721420740269943234134331840751705484228347931048820039415497607505824050612049330073746463857005189481626044993066223981799883398346674752177883829934910991015712926220010517234855375763811468133832018849894275822999037074849849515941065237190237307327810044419980002204134438915428726918397058447009373455653952402333893839825596765866175914770339582058294029937 : Rat)/530857848602949085423970398813905008350771211659017196407074270827575372131574661922674306490249648124709537204040214164507946918369348942991288052585873326615123654250615813707178113858968684263140576370942526432023852643053769274140872156871470137842167048996171666784132282536670550148703213034905944177976890023357528742917011677910802835731404930183219472152327784226557679487277243812099645828460991587632601758924770957995203047047273397056231063116435433513222905714949572118313675492119002715896491114758144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -605, a6 := 1647 }
def label : String := "450.e3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -605, a6 := 1647 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -2, 1, 0, 0, 6, 0, 4, -2, 0, 1, 6, 0, -4, 0, 0, 6, 0, 0, 0, 4, 0, -2, -6, 0, -4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (27602209720573091846599007898656397170583104051921099194817821761233241185036803855921222301753622006053437593852823436534196313906110168384348876029683773369423379895277687141414349878777151012024046669518940922596695388698801602030207154668545277565349698421698250738495069824515492720955636938901397919048304271050416727252210532169272871623741740855235938582908112737109789414254490448336675939691079888332659383073761891864555008211057341479146018714251430947535644162172581191982386199671220136097539089121425 : Rat)/17124446729127389852386141897222742204863587472871522464744331317018560391341118126537880854524182197571275393678716585951869255431269320741654453309221720213391085620987606893779939156740925298810986334546533110710446859453347395940028134092628068962650549967618440864004267178602275811248490743061482070257319033011533185255387473480993639862303384844619982972655734975050247725396040122970956317047128760891374250287895837354683969259589464421168743971497917210103964700482244261881086306197387184383757777895424,            reHi := (1480349058118740723720850143333554405529118405615664067435327860566669368596471295452204681798094889893594164861661492077515122517878140525995046235159129721420740269943234134331840751705484228347931048820039415497607505824050612049330073746463857005189481626044993066223981799883398346674752177883829934910991015712926220010517234855375763811468133832018849894275822999037074849849515941065237190237307327810044419980002204134438915428726918397058447009373455653952402333893839825596765866175914770339582058294029937 : Rat)/530857848602949085423970398813905008350771211659017196407074270827575372131574661922674306490249648124709537204040214164507946918369348942991288052585873326615123654250615813707178113858968684263140576370942526432023852643053769274140872156871470137842167048996171666784132282536670550148703213034905944177976890023357528742917011677910802835731404930183219472152327784226557679487277243812099645828460991587632601758924770957995203047047273397056231063116435433513222905714949572118313675492119002715896491114758144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 145, a6 := 147 }
def label : String := "450.e4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 145, a6 := 147 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -2, 1, 0, 0, 6, 0, 4, -2, 0, 1, 6, 0, -4, 0, 0, 6, 0, 0, 0, 4, 0, -2, -6, 0, -4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (27602209720573091846599007898656397170583104051921099194817821761233241185036803855921222301753622006053437593852823436534196313906110168384348876029683773369423379895277687141414349878777151012024046669518940922596695388698801602030207154668545277565349698421698250738495069824515492720955636938901397919048304271050416727252210532169272871623741740855235938582908112737109789414254490448336675939691079888332659383073761891864555008211057341479146018714251430947535644162172581191982386199671220136097539089121425 : Rat)/17124446729127389852386141897222742204863587472871522464744331317018560391341118126537880854524182197571275393678716585951869255431269320741654453309221720213391085620987606893779939156740925298810986334546533110710446859453347395940028134092628068962650549967618440864004267178602275811248490743061482070257319033011533185255387473480993639862303384844619982972655734975050247725396040122970956317047128760891374250287895837354683969259589464421168743971497917210103964700482244261881086306197387184383757777895424,            reHi := (1480349058118740723720850143333554405529118405615664067435327860566669368596471295452204681798094889893594164861661492077515122517878140525995046235159129721420740269943234134331840751705484228347931048820039415497607505824050612049330073746463857005189481626044993066223981799883398346674752177883829934910991015712926220010517234855375763811468133832018849894275822999037074849849515941065237190237307327810044419980002204134438915428726918397058447009373455653952402333893839825596765866175914770339582058294029937 : Rat)/530857848602949085423970398813905008350771211659017196407074270827575372131574661922674306490249648124709537204040214164507946918369348942991288052585873326615123654250615813707178113858968684263140576370942526432023852643053769274140872156871470137842167048996171666784132282536670550148703213034905944177976890023357528742917011677910802835731404930183219472152327784226557679487277243812099645828460991587632601758924770957995203047047273397056231063116435433513222905714949572118313675492119002715896491114758144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -186305, a6 := -30804303 }
def label : String := "450.f1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 2, 0, 0, 1, 2, 0, 2, 0],                kodaira := -14 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -186305, a6 := -30804303 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, -2, 0, 6, 2, 0, 1, -2, 0, 0, 0, 0, -2, 4, 0, 0, 6, 0, 2, 0, 0, -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (53148595276254480364996386642991261153403526706280723939667538716626564967257605157916269491251002709464607221308785702934793750624308520191841512521489752665061853256851463732844261869471092061813633835514909983684880418982309149121272825877576829072417129072286783103148796977160136564245508503889498750445670753325750249112641774121264759926145742065898540063236484859921186695171351266158029222807740481182635406958024584581132819849492275609881639795062961598948511036821610378878716813261717822534245331591 : Rat)/31078850688071487935365048815286283493400340241146138774490619450124429022397673550885446196958588380347142275278977469967094837443320001346015341759023085686735182615222517048602430411508031395301245616236902197296636768517871861960123655340522811184483756747038912638846219924868014176494538553650602668343591711454688176507055305773128203016884545997495431892297159664338017650446533798495383515512030419040606624841916220244435515897621532524807157843008924156268538476374309005228831771683098338264533172224,            reHi := (63970543361120842608303967100547929566436981446091963840909540476842379668342954831548565862462520391490146176959837649683308646855356841809398417755684459294627479818326388217941866062163484585946102204307210892274999640190462847085181661617709408748616149556768189671307651200547562202421306616417441563539004478476723562290702984056844659417772251056514519475247691121921157759363509033775625638117742027465419597933599435921586327405180393947880405684470831409222746132743286063748530486506058599907292821636609 : Rat)/22159220540594970897915279805299120130794442591937196946211811667938717892969541241781323138431473515187512442273910936086538619097087160959708938674183460094642185204653654655653532883405226384849788124376911266672502015953242637577568166257792764374536918560638744711497354806430894107840605988752879702528980890267192669849530433016240408751038681296214242939207874840673006584768378598327208446560077688775952523512286265034282522835004152690187503542065362923419467933654882320728157053210049115182612151795712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11930, a6 := 504447 }
def label : String := "450.f2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11930, a6 := 504447 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, -2, 0, 6, 2, 0, 1, -2, 0, 0, 0, 0, -2, 4, 0, 0, 6, 0, 2, 0, 0, -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (53148595276254480364996386642991261153403526706280723939667538716626564967257605157916269491251002709464607221308785702934793750624308520191841512521489752665061853256851463732844261869471092061813633835514909983684880418982309149121272825877576829072417129072286783103148796977160136564245508503889498750445670753325750249112641774121264759926145742065898540063236484859921186695171351266158029222807740481182635406958024584581132819849492275609881639795062961598948511036821610378878716813261717822534245331591 : Rat)/31078850688071487935365048815286283493400340241146138774490619450124429022397673550885446196958588380347142275278977469967094837443320001346015341759023085686735182615222517048602430411508031395301245616236902197296636768517871861960123655340522811184483756747038912638846219924868014176494538553650602668343591711454688176507055305773128203016884545997495431892297159664338017650446533798495383515512030419040606624841916220244435515897621532524807157843008924156268538476374309005228831771683098338264533172224,            reHi := (63970543361120842608303967100547929566436981446091963840909540476842379668342954831548565862462520391490146176959837649683308646855356841809398417755684459294627479818326388217941866062163484585946102204307210892274999640190462847085181661617709408748616149556768189671307651200547562202421306616417441563539004478476723562290702984056844659417772251056514519475247691121921157759363509033775625638117742027465419597933599435921586327405180393947880405684470831409222746132743286063748530486506058599907292821636609 : Rat)/22159220540594970897915279805299120130794442591937196946211811667938717892969541241781323138431473515187512442273910936086538619097087160959708938674183460094642185204653654655653532883405226384849788124376911266672502015953242637577568166257792764374536918560638744711497354806430894107840605988752879702528980890267192669849530433016240408751038681296214242939207874840673006584768378598327208446560077688775952523512286265034282522835004152690187503542065362923419467933654882320728157053210049115182612151795712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6305, a6 := -924303 }
def label : String := "450.f3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 0, 2, 1],                kodaira := -9 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6305, a6 := -924303 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, -2, 0, 6, 2, 0, 1, -2, 0, 0, 0, 0, -2, 4, 0, 0, 6, 0, 2, 0, 0, -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (53148595276254480364996386642991261153403526706280723939667538716626564967257605157916269491251002709464607221308785702934793750624308520191841512521489752665061853256851463732844261869471092061813633835514909983684880418982309149121272825877576829072417129072286783103148796977160136564245508503889498750445670753325750249112641774121264759926145742065898540063236484859921186695171351266158029222807740481182635406958024584581132819849492275609881639795062961598948511036821610378878716813261717822534245331591 : Rat)/31078850688071487935365048815286283493400340241146138774490619450124429022397673550885446196958588380347142275278977469967094837443320001346015341759023085686735182615222517048602430411508031395301245616236902197296636768517871861960123655340522811184483756747038912638846219924868014176494538553650602668343591711454688176507055305773128203016884545997495431892297159664338017650446533798495383515512030419040606624841916220244435515897621532524807157843008924156268538476374309005228831771683098338264533172224,            reHi := (63970543361120842608303967100547929566436981446091963840909540476842379668342954831548565862462520391490146176959837649683308646855356841809398417755684459294627479818326388217941866062163484585946102204307210892274999640190462847085181661617709408748616149556768189671307651200547562202421306616417441563539004478476723562290702984056844659417772251056514519475247691121921157759363509033775625638117742027465419597933599435921586327405180393947880405684470831409222746132743286063748530486506058599907292821636609 : Rat)/22159220540594970897915279805299120130794442591937196946211811667938717892969541241781323138431473515187512442273910936086538619097087160959708938674183460094642185204653654655653532883405226384849788124376911266672502015953242637577568166257792764374536918560638744711497354806430894107840605988752879702528980890267192669849530433016240408751038681296214242939207874840673006584768378598327208446560077688775952523512286265034282522835004152690187503542065362923419467933654882320728157053210049115182612151795712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -680, a6 := 9447 }
def label : String := "450.f4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -680, a6 := 9447 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, -2, 0, 6, 2, 0, 1, -2, 0, 0, 0, 0, -2, 4, 0, 0, 6, 0, 2, 0, 0, -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (53148595276254480364996386642991261153403526706280723939667538716626564967257605157916269491251002709464607221308785702934793750624308520191841512521489752665061853256851463732844261869471092061813633835514909983684880418982309149121272825877576829072417129072286783103148796977160136564245508503889498750445670753325750249112641774121264759926145742065898540063236484859921186695171351266158029222807740481182635406958024584581132819849492275609881639795062961598948511036821610378878716813261717822534245331591 : Rat)/31078850688071487935365048815286283493400340241146138774490619450124429022397673550885446196958588380347142275278977469967094837443320001346015341759023085686735182615222517048602430411508031395301245616236902197296636768517871861960123655340522811184483756747038912638846219924868014176494538553650602668343591711454688176507055305773128203016884545997495431892297159664338017650446533798495383515512030419040606624841916220244435515897621532524807157843008924156268538476374309005228831771683098338264533172224,            reHi := (63970543361120842608303967100547929566436981446091963840909540476842379668342954831548565862462520391490146176959837649683308646855356841809398417755684459294627479818326388217941866062163484585946102204307210892274999640190462847085181661617709408748616149556768189671307651200547562202421306616417441563539004478476723562290702984056844659417772251056514519475247691121921157759363509033775625638117742027465419597933599435921586327405180393947880405684470831409222746132743286063748530486506058599907292821636609 : Rat)/22159220540594970897915279805299120130794442591937196946211811667938717892969541241781323138431473515187512442273910936086538619097087160959708938674183460094642185204653654655653532883405226384849788124376911266672502015953242637577568166257792764374536918560638744711497354806430894107840605988752879702528980890267192669849530433016240408751038681296214242939207874840673006584768378598327208446560077688775952523512286265034282522835004152690187503542065362923419467933654882320728157053210049115182612151795712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_f4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1130, a6 := 14897 }
def label : String := "450.g1"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1130, a6 := 14897 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 3, 0, -4, 2, 0, 1, 3, 0, 5, 0, 0, 3, -6, 0, 0, -4, 0, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (723118017076566113472476734949626770157410787716204762107103127382236114514629390899123419465353378764642646086421116658759363318622135636209228364072818056061500217127129932361195399799139675426954323440822496051774568444742925716523517916456376264547639833688155527655625948064599624318013683679846741225007287321698904514588883759456205791006887014045267343801898726612550036919811490543015934873235238717860478209922005485361082365489397440402161038301112177262204900911295822382139328284343511771448360238927341 : Rat)/421025190271304447060390316300683282485094409246806741978024421690835639966421283593845139630197996788562736403204307785644233762844656058234469834809485741798201518888419438457417124784699301312145974363161314066777538303111610113973795158898062523116201452652136149518449741322186988048971513786304714348050636915076660727141078227308567766269734944628070615844949621972787125110599193368216960484641476086743097946733439035651367933865078901113562567299241895544969890739442764093834984010990933188469630884118528,            reHi := (1709052343240452579012619866876285223790324246446477363735989333286686174457283966748645315101270120732841660169940819842368282560296570080709001744640441809764223437342672887247310246273583486980997569006771732699870525366744456387692289480062608479660582798454228110895404772038415918377122262928847301125681613612262424718154258058598462696363792988717718803449721228434093016028763282698345193237334371834516033758348464286104358410855071617057027124271534177882151750085024403439775756743936411380727292411899 : Rat)/590498163073358270771935927490439386374606464581776636715321769552364151425555797466823477742213179226595703230300571929374801911423080025574291493421438628047968469689227823923446177818652596510723666708501141748636098601839565377242349451469933412505191378193739340138078178572492269353396232519361450698528242517639075353634050809689435857320806373952413205953646033622422335358484142171412286794728577961771525871996408184644274802054809117971335999017169558969102231051111871099347803661978868427026130272256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -680, a6 := -8053 }
def label : String := "450.g2"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -680, a6 := -8053 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 3, 0, -4, 2, 0, 1, 3, 0, 5, 0, 0, 3, -6, 0, 0, -4, 0, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (723118017076566113472476734949626770157410787716204762107103127382236114514629390899123419465353378764642646086421116658759363318622135636209228364072818056061500217127129932361195399799139675426954323440822496051774568444742925716523517916456376264547639833688155527655625948064599624318013683679846741225007287321698904514588883759456205791006887014045267343801898726612550036919811490543015934873235238717860478209922005485361082365489397440402161038301112177262204900911295822382139328284343511771448360238927341 : Rat)/421025190271304447060390316300683282485094409246806741978024421690835639966421283593845139630197996788562736403204307785644233762844656058234469834809485741798201518888419438457417124784699301312145974363161314066777538303111610113973795158898062523116201452652136149518449741322186988048971513786304714348050636915076660727141078227308567766269734944628070615844949621972787125110599193368216960484641476086743097946733439035651367933865078901113562567299241895544969890739442764093834984010990933188469630884118528,            reHi := (1709052343240452579012619866876285223790324246446477363735989333286686174457283966748645315101270120732841660169940819842368282560296570080709001744640441809764223437342672887247310246273583486980997569006771732699870525366744456387692289480062608479660582798454228110895404772038415918377122262928847301125681613612262424718154258058598462696363792988717718803449721228434093016028763282698345193237334371834516033758348464286104358410855071617057027124271534177882151750085024403439775756743936411380727292411899 : Rat)/590498163073358270771935927490439386374606464581776636715321769552364151425555797466823477742213179226595703230300571929374801911423080025574291493421438628047968469689227823923446177818652596510723666708501141748636098601839565377242349451469933412505191378193739340138078178572492269353396232519361450698528242517639075353634050809689435857320806373952413205953646033622422335358484142171412286794728577961771525871996408184644274802054809117971335999017169558969102231051111871099347803661978868427026130272256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 47 }
def label : String := "450.g3"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 47 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 3, 0, -4, 2, 0, 1, 3, 0, 5, 0, 0, 3, -6, 0, 0, -4, 0, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (723118017076566113472476734949626770157410787716204762107103127382236114514629390899123419465353378764642646086421116658759363318622135636209228364072818056061500217127129932361195399799139675426954323440822496051774568444742925716523517916456376264547639833688155527655625948064599624318013683679846741225007287321698904514588883759456205791006887014045267343801898726612550036919811490543015934873235238717860478209922005485361082365489397440402161038301112177262204900911295822382139328284343511771448360238927341 : Rat)/421025190271304447060390316300683282485094409246806741978024421690835639966421283593845139630197996788562736403204307785644233762844656058234469834809485741798201518888419438457417124784699301312145974363161314066777538303111610113973795158898062523116201452652136149518449741322186988048971513786304714348050636915076660727141078227308567766269734944628070615844949621972787125110599193368216960484641476086743097946733439035651367933865078901113562567299241895544969890739442764093834984010990933188469630884118528,            reHi := (1709052343240452579012619866876285223790324246446477363735989333286686174457283966748645315101270120732841660169940819842368282560296570080709001744640441809764223437342672887247310246273583486980997569006771732699870525366744456387692289480062608479660582798454228110895404772038415918377122262928847301125681613612262424718154258058598462696363792988717718803449721228434093016028763282698345193237334371834516033758348464286104358410855071617057027124271534177882151750085024403439775756743936411380727292411899 : Rat)/590498163073358270771935927490439386374606464581776636715321769552364151425555797466823477742213179226595703230300571929374801911423080025574291493421438628047968469689227823923446177818652596510723666708501141748636098601839565377242349451469933412505191378193739340138078178572492269353396232519361450698528242517639075353634050809689435857320806373952413205953646033622422335358484142171412286794728577961771525871996408184644274802054809117971335999017169558969102231051111871099347803661978868427026130272256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4945, a6 := 59447 }
def label : String := "450.g4"
def inputConductor : Nat := 450
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 450 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4945, a6 := 59447 },   conductor := 450,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 3, 0, -4, 2, 0, 1, 3, 0, 5, 0, 0, 3, -6, 0, 0, -4, 0, 2, 0, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18222002999856298160552978515625,   alphaHi := (674651885226100947931528953856 : Rat)/2277750374982037258148193359375,   geometricUpper := (1674538521507099 : Rat)/2251799813685248,   tail := (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/1826341346187429507866548088105205588141290488402546792883035755428361580913067729381527072748345089049018174488980282656584288502281248242699379547453904077495162638257184994335219510578129599535831557632773238367317198596572360695782079998855427583268716974028260718037622373207264157988748813166280934850067092404929668949112963846337674267901777398924336363183708036924135726064907668713368015250163390670541612789675984030348211547136483077205568422342887944776901832072298819135501661378803451740291072,   box := { reLo := (723118017076566113472476734949626770157410787716204762107103127382236114514629390899123419465353378764642646086421116658759363318622135636209228364072818056061500217127129932361195399799139675426954323440822496051774568444742925716523517916456376264547639833688155527655625948064599624318013683679846741225007287321698904514588883759456205791006887014045267343801898726612550036919811490543015934873235238717860478209922005485361082365489397440402161038301112177262204900911295822382139328284343511771448360238927341 : Rat)/421025190271304447060390316300683282485094409246806741978024421690835639966421283593845139630197996788562736403204307785644233762844656058234469834809485741798201518888419438457417124784699301312145974363161314066777538303111610113973795158898062523116201452652136149518449741322186988048971513786304714348050636915076660727141078227308567766269734944628070615844949621972787125110599193368216960484641476086743097946733439035651367933865078901113562567299241895544969890739442764093834984010990933188469630884118528,            reHi := (1709052343240452579012619866876285223790324246446477363735989333286686174457283966748645315101270120732841660169940819842368282560296570080709001744640441809764223437342672887247310246273583486980997569006771732699870525366744456387692289480062608479660582798454228110895404772038415918377122262928847301125681613612262424718154258058598462696363792988717718803449721228434093016028763282698345193237334371834516033758348464286104358410855071617057027124271534177882151750085024403439775756743936411380727292411899 : Rat)/590498163073358270771935927490439386374606464581776636715321769552364151425555797466823477742213179226595703230300571929374801911423080025574291493421438628047968469689227823923446177818652596510723666708501141748636098601839565377242349451469933412505191378193739340138078178572492269353396232519361450698528242517639075353634050809689435857320806373952413205953646033622422335358484142171412286794728577961771525871996408184644274802054809117971335999017169558969102231051111871099347803661978868427026130272256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1074562551925072435526485921945528882685281973089032762864148070386022112181823904736719807784861431441728886078950348402401297117347946678368085929180342808099465237633034202033450259099486197607913883888213953804105876681048554416023019686416988667608990441806400055814914498669622389608436383359339170915246684988614631871885009016417934301350627873860465897117544838594634132916621436720632384399180556465742890277470579387503649218405731600826812130230406022704270646765470260770870099245020888276574977 : Rat)/3652682692374859015733096176210411176282580976805093585766071510856723161826135458763054145496690178098036348977960565313168577004562496485398759094907808154990325276514369988670439021156259199071663115265546476734634397193144721391564159997710855166537433948056521436075244746414528315977497626332561869700134184809859337898225927692675348535803554797848672726367416073848271452129815337426736030500326781341083225579351968060696423094272966154411136844685775889553803664144597638271003322757606903480582144, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N450.C450_g4
