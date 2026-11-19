module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -513, a6 := -4563 }
def label : String := "540.a1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -513, a6 := -4563 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, 6, 0, -4, 0, 0, 0, -3, 0, -7, 0, 0, 0, -9, 0, 1, 0, 0, 0, 0, 0, -7,                    0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 2, 0, 0, 0, 0, 0, 9, 0, 0, 0, 9, 0, -6, 0, 0, 0, -12, 0, -7, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((10884294823786965 : Rat)/4503599627370496, (40903592305417319 : Rat)/9007199254740992),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (14856243476850768023689936652954507081914788559995 : Rat)/22258234424283487922256570134545574982549690646528,            reHi := (280033545822641552664797686349891037684313163595017 : Rat)/44516468848566975844513140269091149965099381293056,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := -27 }
def label : String := "540.a2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := -27 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, 6, 0, -4, 0, 0, 0, -3, 0, -7, 0, 0, 0, -9, 0, 1, 0, 0, 0, 0, 0, -7,                    0, 0, 0, 4, 0, 2, 0, 0, 0, 6, 0, 2, 0, 0, 0, 0, 0, 9, 0, 0, 0, 9, 0, -6, 0, 0, 0, -12, 0, -7, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((10884294823786965 : Rat)/4503599627370496, (40903592305417319 : Rat)/9007199254740992),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (14856243476850768023689936652954507081914788559995 : Rat)/22258234424283487922256570134545574982549690646528,            reHi := (280033545822641552664797686349891037684313163595017 : Rat)/44516468848566975844513140269091149965099381293056,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -648, a6 := 6372 }
def label : String := "540.b1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -648, a6 := 6372 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -6, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 1, 0, 0, 0, -6, 0, 8,                    0, 0, 0, 1, 0, -7, 0, 0, 0, 6, 0, -4, 0, 0, 0, -12, 0, -6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 11, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((22484327521374103 : Rat)/9007199254740992, (41170434057632517 : Rat)/9007199254740992),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (33249893184167032653061325374999041399514905357529 : Rat)/44516468848566975844513140269091149965099381293056,            reHi := (281352363383353600428387478066047031330845175021131 : Rat)/44516468848566975844513140269091149965099381293056,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1512, a6 := 33588 }
def label : String := "540.b2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1512, a6 := 33588 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -6, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 1, 0, 0, 0, -6, 0, 8,                    0, 0, 0, 1, 0, -7, 0, 0, 0, 6, 0, -4, 0, 0, 0, -12, 0, -6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 11, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((22484327521374103 : Rat)/9007199254740992, (41170434057632517 : Rat)/9007199254740992),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (33249893184167032653061325374999041399514905357529 : Rat)/44516468848566975844513140269091149965099381293056,            reHi := (281352363383353600428387478066047031330845175021131 : Rat)/44516468848566975844513140269091149965099381293056,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -33, a6 := 73 }
def label : String := "540.c1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -33, a6 := 73 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 0, 0, -1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 5, 0, 0, 0, -3, 0, 1, 0, 0, 0, 6, 0, 5, 0, 0,                    0, -2, 0, 2, 0, 0, 0, -12, 0, 8, 0, 0, 0, 12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (605018818850073997881940406672902525396016089471507588638245651038311548811522507321103390671294102845129498969581404825882377044240522437412531255170599721748210925287868300166380809869704595197830854563178778857585942224008832285972668605725878204627403791347398564647626180393870164563346262575686041397698737824633157639070807256330093221345585001809293230840357520994700125811186411044783456635493368575703763966034386490257597636712248911124639776193231471866541654461375218628805152643294631921901107583800287521366788427367810923917115103189510117701615680851317400869903509051322163282460666863315764840154669403069338133446961662644687523849820828486720186972390337280780063902956845920803899984258961494054417432095156769786170914522283634795485340873710811138153076171875 : Rat)/14688174910247175739773084181905933507683471700478112684272499773249127567696242777834595343063944191600276979677702222182851926654848130546517722928226981243660141742509273265610588123071808253869340044456035091861264928508595586985418997432655173287584261248136680544563316583630399107688839494163582464834037218020648503434348329011722082497596757804813349524354847173272908783405211515363427400040879502743876179985385125495064349887290109875799809863180631569406746444600840610526202922475385817028070853425708060713206685235445769767737032323594614751393703721018488150828357965339400958400061245053914163958106813143643148974409964966468930068126693323290998095409852347710126397824888124739057901985627512561163949973030636782656348057550083245314220423368970735633506538356736,   box := { reLo := (1014813317918462040672716739223481259885722467263987415731545542178510166880908310097074803340499500563545016951310384036275819934293252854455176683733091482079004864823284716562844432243178239043048461575692444434174833935818830969437616673246990384549709518733763759106606046452730677664211919184159519471054003717048369772376377091917689272963567671223147517993830371076092928758039876282986179543731435444501204962939153925211166472301212946167369679722638726732734638718772251069123312074461640860454564472022590892045332189847972989012680384221621819279055410904777275332406602877260006148056070964909789245747710193634571500853355743485009232258133009128925494706321289089117535079220484157552163288501303565725829866142154056226630258043416023651422970127970220681832795398306738890825912556217 : Rat)/684212778574516683333541239522472968886704889107049098402516244081410128604166085414031903529166789110029907624984689834848614516030254876756362363004407234807113517444374056524156196215294913866916752044594515511387722754076609679484768076882634426053373687674440060755643486795084461096728903798922915857942214132580379409153147139284208888089812180882993685735111251320265792550591222052517049303668427394934974420912786744448169096498856631681158333505829042155296147547013260509002984724430218575147186719722652178786718947185339080374217989994923089559562862170009633707337036111725822600645448963791912478109547563127797723952845167700779690949361438100191754084097319712933814844449491540104353474035146601750007383870287749349015503897453935956933572142245120545247651949049056308585352396800,            reHi := (1071179967916139668577872202401023233290876931070466895076291858986266387434788749719805012470734939242114404978145645414415980379125906719755902028186030572382121103541289353487736553389714847971299357258008267807886020363640525831252007962296548085557712061024574393518628966645163287152741189339513810729834918088903737568459599368269638819827115980097043912807343407348911002176640270650761127277171782580902421410547156775682553140043604702336753762190798330219130817351018612322313567283868399991960018275479844200416784907590423408002872354456908147137239909818289991158227349171398224346682619068109382976451463900851265834760487369101037327941565442364390713799011401062055044123194140873619111886046574269778893304338570711984060794591886881476834841401876146362867693262708835484234806715719 : Rat)/684212778574516683333541239522472968886704889107049098402516244081410128604166085414031903529166789110029907624984689834848614516030254876756362363004407234807113517444374056524156196215294913866916752044594515511387722754076609679484768076882634426053373687674440060755643486795084461096728903798922915857942214132580379409153147139284208888089812180882993685735111251320265792550591222052517049303668427394934974420912786744448169096498856631681158333505829042155296147547013260509002984724430218575147186719722652178786718947185339080374217989994923089559562862170009633707337036111725822600645448963791912478109547563127797723952845167700779690949361438100191754084097319712933814844449491540104353474035146601750007383870287749349015503897453935956933572142245120545247651949049056308585352396800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (605018818850073997881940406672902525396016089471507588638245651038311548811522507321103390671294102845129498969581404825882377044240522437412531255170599721748210925287868300166380809869704595197830854563178778857585942224008832285972668605725878204627403791347398564647626180393870164563346262575686041397698737824633157639070807256330093221345585001809293230840357520994700125811186411044783456635493368575703763966034386490257597636712248911124639776193231471866541654461375218628805152643294631921901107583800287521366788427367810923917115103189510117701615680851317400869903509051322163282460666863315764840154669403069338133446961662644687523849820828486720186972390337280780063902956845920803899984258961494054417432095156769786170914522283634795485340873710811138153076171875 : Rat)/29376349820494351479546168363811867015366943400956225368544999546498255135392485555669190686127888383200553959355404444365703853309696261093035445856453962487320283485018546531221176246143616507738680088912070183722529857017191173970837994865310346575168522496273361089126633167260798215377678988327164929668074436041297006868696658023444164995193515609626699048709694346545817566810423030726854800081759005487752359970770250990128699774580219751599619726361263138813492889201681221052405844950771634056141706851416121426413370470891539535474064647189229502787407442036976301656715930678801916800122490107828327916213626287286297948819929932937860136253386646581996190819704695420252795649776249478115803971255025122327899946061273565312696115100166490628440846737941471267013076713472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := 297 }
def label : String := "540.c2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := 297 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 0, 0, -1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 5, 0, 0, 0, -3, 0, 1, 0, 0, 0, 6, 0, 5, 0, 0,                    0, -2, 0, 2, 0, 0, 0, -12, 0, 8, 0, 0, 0, 12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (605018818850073997881940406672902525396016089471507588638245651038311548811522507321103390671294102845129498969581404825882377044240522437412531255170599721748210925287868300166380809869704595197830854563178778857585942224008832285972668605725878204627403791347398564647626180393870164563346262575686041397698737824633157639070807256330093221345585001809293230840357520994700125811186411044783456635493368575703763966034386490257597636712248911124639776193231471866541654461375218628805152643294631921901107583800287521366788427367810923917115103189510117701615680851317400869903509051322163282460666863315764840154669403069338133446961662644687523849820828486720186972390337280780063902956845920803899984258961494054417432095156769786170914522283634795485340873710811138153076171875 : Rat)/14688174910247175739773084181905933507683471700478112684272499773249127567696242777834595343063944191600276979677702222182851926654848130546517722928226981243660141742509273265610588123071808253869340044456035091861264928508595586985418997432655173287584261248136680544563316583630399107688839494163582464834037218020648503434348329011722082497596757804813349524354847173272908783405211515363427400040879502743876179985385125495064349887290109875799809863180631569406746444600840610526202922475385817028070853425708060713206685235445769767737032323594614751393703721018488150828357965339400958400061245053914163958106813143643148974409964966468930068126693323290998095409852347710126397824888124739057901985627512561163949973030636782656348057550083245314220423368970735633506538356736,   box := { reLo := (1014813317918462040672716739223481259885722467263987415731545542178510166880908310097074803340499500563545016951310384036275819934293252854455176683733091482079004864823284716562844432243178239043048461575692444434174833935818830969437616673246990384549709518733763759106606046452730677664211919184159519471054003717048369772376377091917689272963567671223147517993830371076092928758039876282986179543731435444501204962939153925211166472301212946167369679722638726732734638718772251069123312074461640860454564472022590892045332189847972989012680384221621819279055410904777275332406602877260006148056070964909789245747710193634571500853355743485009232258133009128925494706321289089117535079220484157552163288501303565725829866142154056226630258043416023651422970127970220681832795398306738890825912556217 : Rat)/684212778574516683333541239522472968886704889107049098402516244081410128604166085414031903529166789110029907624984689834848614516030254876756362363004407234807113517444374056524156196215294913866916752044594515511387722754076609679484768076882634426053373687674440060755643486795084461096728903798922915857942214132580379409153147139284208888089812180882993685735111251320265792550591222052517049303668427394934974420912786744448169096498856631681158333505829042155296147547013260509002984724430218575147186719722652178786718947185339080374217989994923089559562862170009633707337036111725822600645448963791912478109547563127797723952845167700779690949361438100191754084097319712933814844449491540104353474035146601750007383870287749349015503897453935956933572142245120545247651949049056308585352396800,            reHi := (1071179967916139668577872202401023233290876931070466895076291858986266387434788749719805012470734939242114404978145645414415980379125906719755902028186030572382121103541289353487736553389714847971299357258008267807886020363640525831252007962296548085557712061024574393518628966645163287152741189339513810729834918088903737568459599368269638819827115980097043912807343407348911002176640270650761127277171782580902421410547156775682553140043604702336753762190798330219130817351018612322313567283868399991960018275479844200416784907590423408002872354456908147137239909818289991158227349171398224346682619068109382976451463900851265834760487369101037327941565442364390713799011401062055044123194140873619111886046574269778893304338570711984060794591886881476834841401876146362867693262708835484234806715719 : Rat)/684212778574516683333541239522472968886704889107049098402516244081410128604166085414031903529166789110029907624984689834848614516030254876756362363004407234807113517444374056524156196215294913866916752044594515511387722754076609679484768076882634426053373687674440060755643486795084461096728903798922915857942214132580379409153147139284208888089812180882993685735111251320265792550591222052517049303668427394934974420912786744448169096498856631681158333505829042155296147547013260509002984724430218575147186719722652178786718947185339080374217989994923089559562862170009633707337036111725822600645448963791912478109547563127797723952845167700779690949361438100191754084097319712933814844449491540104353474035146601750007383870287749349015503897453935956933572142245120545247651949049056308585352396800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (605018818850073997881940406672902525396016089471507588638245651038311548811522507321103390671294102845129498969581404825882377044240522437412531255170599721748210925287868300166380809869704595197830854563178778857585942224008832285972668605725878204627403791347398564647626180393870164563346262575686041397698737824633157639070807256330093221345585001809293230840357520994700125811186411044783456635493368575703763966034386490257597636712248911124639776193231471866541654461375218628805152643294631921901107583800287521366788427367810923917115103189510117701615680851317400869903509051322163282460666863315764840154669403069338133446961662644687523849820828486720186972390337280780063902956845920803899984258961494054417432095156769786170914522283634795485340873710811138153076171875 : Rat)/29376349820494351479546168363811867015366943400956225368544999546498255135392485555669190686127888383200553959355404444365703853309696261093035445856453962487320283485018546531221176246143616507738680088912070183722529857017191173970837994865310346575168522496273361089126633167260798215377678988327164929668074436041297006868696658023444164995193515609626699048709694346545817566810423030726854800081759005487752359970770250990128699774580219751599619726361263138813492889201681221052405844950771634056141706851416121426413370470891539535474064647189229502787407442036976301656715930678801916800122490107828327916213626287286297948819929932937860136253386646581996190819704695420252795649776249478115803971255025122327899946061273565312696115100166490628440846737941471267013076713472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -57, a6 := 169 }
def label : String := "540.d1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -57, a6 := 169 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 1, 0, -4, 0, 0, 0, -6, 0, -4, 0, 0, 0, 3, 0, -7, 0, 0, 0, 9, 0, 1, 0, 0, 0, 0, 0, -7, 0,                    0, 0, -4, 0, 2, 0, 0, 0, -6, 0, 2, 0, 0, 0, 0, 0, 9, 0, 0, 0, -9, 0, -6, 0, 0, 0, 12, 0, -7, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((5742006766571875 : Rat)/2251799813685248, (21188289846595683 : Rat)/4503599627370496),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (8910122884837894006745797045288494355508809778125 : Rat)/11129117212141743961128285067272787491274845323264,            reHi := (143656761064556150701260555805766584289317797131469 : Rat)/22258234424283487922256570134545574982549690646528,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := 1 }
def label : String := "540.d2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := 1 },   conductor := 540,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 1, 0, -4, 0, 0, 0, -6, 0, -4, 0, 0, 0, 3, 0, -7, 0, 0, 0, 9, 0, 1, 0, 0, 0, 0, 0, -7, 0,                    0, 0, -4, 0, 2, 0, 0, 0, -6, 0, 2, 0, 0, 0, 0, 0, 9, 0, 0, 0, -9, 0, -6, 0, 0, 0, 12, 0, -7, 0, 0,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   finite := ((5742006766571875 : Rat)/2251799813685248, (21188289846595683 : Rat)/4503599627370496),   tail := (74267261459061846487950050514507293701171875 : Rat)/42454212997977233738434925335971021618937856,   box := { reLo := (8910122884837894006745797045288494355508809778125 : Rat)/11129117212141743961128285067272787491274845323264,            reHi := (143656761064556150701260555805766584289317797131469 : Rat)/22258234424283487922256570134545574982549690646528,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -72, a6 := -236 }
def label : String := "540.e1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -72, a6 := -236 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 6, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, 1, 0, 0, 0, 6, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/1093995180570554865551461326472104741011901778991144380429496795098352977024584473237365249218733728042379263463561523440443108065841066146779997218414167579750933711988730881963933086471873557569918406123993493302932571942722432197364497568118223362163708293509782215754347767985204013376175258627374283612358942157858958253587106015320875421376164471869160593214974871034453141795147204684279724683062032151555965609145059570069445777233252628141582158814209513435844216477920509365119073156650301067967396803298608427814617088,   box := { reLo := (168953054205096827212032777389330930031258748257719901589546706460674276247625202761133919399376967737304293167660623539062723721041073217005076777817541418779342325404729415298840816906581173110937468600758616367208051551725540406775649253288857277803779686636754281361406745725200373188653101834656729561334160005146547132948206691669479051902608846809777429309704983777181274531339920679307847437391090010962255724993915489585265044601196360554899225616674173984123427444753715188405038066578972617621728614976941559077582747649074167 : Rat)/1536500067332551378718888910188972483403667597744277688155007402900489178065793354426287410456154314244689849380954485550593512731552104601400187418803796296434195578442577890219563002838393789675137305856698379340105246464803202297262720773970475765408752329444452514994743669646947055397540517752700961878517761657342524501054893649026793163388472167910164186322667455114169903606114225679121663084428431915335314458652361047907388818062744694917271350178160781675082187444940894127783868614209458341761929591945126799926108739128524800,            reHi := (4866369178965639831530780578396528476848838312677919588566353818702163017458921723623660559990342204585664637046184218737932088985017150225426397046446562390510137820374257561128821310293985514995249192560164412514724752065180157707168476529282623441467454732968488924667204995148257095545260166431465449650026093276855102642981325116365250132407591524532145433683017471930022348527673351490831109772055879017556784279203869491522473865337816161751492812059727072474470029476301223114432468285193499918861726843019074579038201133424286729 : Rat)/1536500067332551378718888910188972483403667597744277688155007402900489178065793354426287410456154314244689849380954485550593512731552104601400187418803796296434195578442577890219563002838393789675137305856698379340105246464803202297262720773970475765408752329444452514994743669646947055397540517752700961878517761657342524501054893649026793163388472167910164186322667455114169903606114225679121663084428431915335314458652361047907388818062744694917271350178160781675082187444940894127783868614209458341761929591945126799926108739128524800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/2187990361141109731102922652944209482023803557982288760858993590196705954049168946474730498437467456084758526927123046880886216131682132293559994436828335159501867423977461763927866172943747115139836812247986986605865143885444864394728995136236446724327416587019564431508695535970408026752350517254748567224717884315717916507174212030641750842752328943738321186429949742068906283590294409368559449366124064303111931218290119140138891554466505256283164317628419026871688432955841018730238146313300602135934793606597216855629234176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 168, a6 := -1244 }
def label : String := "540.e2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 168, a6 := -1244 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 6, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, 1, 0, 0, 0, 6, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/1093995180570554865551461326472104741011901778991144380429496795098352977024584473237365249218733728042379263463561523440443108065841066146779997218414167579750933711988730881963933086471873557569918406123993493302932571942722432197364497568118223362163708293509782215754347767985204013376175258627374283612358942157858958253587106015320875421376164471869160593214974871034453141795147204684279724683062032151555965609145059570069445777233252628141582158814209513435844216477920509365119073156650301067967396803298608427814617088,   box := { reLo := (168953054205096827212032777389330930031258748257719901589546706460674276247625202761133919399376967737304293167660623539062723721041073217005076777817541418779342325404729415298840816906581173110937468600758616367208051551725540406775649253288857277803779686636754281361406745725200373188653101834656729561334160005146547132948206691669479051902608846809777429309704983777181274531339920679307847437391090010962255724993915489585265044601196360554899225616674173984123427444753715188405038066578972617621728614976941559077582747649074167 : Rat)/1536500067332551378718888910188972483403667597744277688155007402900489178065793354426287410456154314244689849380954485550593512731552104601400187418803796296434195578442577890219563002838393789675137305856698379340105246464803202297262720773970475765408752329444452514994743669646947055397540517752700961878517761657342524501054893649026793163388472167910164186322667455114169903606114225679121663084428431915335314458652361047907388818062744694917271350178160781675082187444940894127783868614209458341761929591945126799926108739128524800,            reHi := (4866369178965639831530780578396528476848838312677919588566353818702163017458921723623660559990342204585664637046184218737932088985017150225426397046446562390510137820374257561128821310293985514995249192560164412514724752065180157707168476529282623441467454732968488924667204995148257095545260166431465449650026093276855102642981325116365250132407591524532145433683017471930022348527673351490831109772055879017556784279203869491522473865337816161751492812059727072474470029476301223114432468285193499918861726843019074579038201133424286729 : Rat)/1536500067332551378718888910188972483403667597744277688155007402900489178065793354426287410456154314244689849380954485550593512731552104601400187418803796296434195578442577890219563002838393789675137305856698379340105246464803202297262720773970475765408752329444452514994743669646947055397540517752700961878517761657342524501054893649026793163388472167910164186322667455114169903606114225679121663084428431915335314458652361047907388818062744694917271350178160781675082187444940894127783868614209458341761929591945126799926108739128524800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/2187990361141109731102922652944209482023803557982288760858993590196705954049168946474730498437467456084758526927123046880886216131682132293559994436828335159501867423977461763927866172943747115139836812247986986605865143885444864394728995136236446724327416587019564431508695535970408026752350517254748567224717884315717916507174212030641750842752328943738321186429949742068906283590294409368559449366124064303111931218290119140138891554466505256283164317628419026871688432955841018730238146313300602135934793606597216855629234176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -297, a6 := -1971 }
def label : String := "540.f1"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -297, a6 := -1971 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, -3, 0, 5, 0, 0, 0, 3, 0, 1, 0, 0, 0, -6, 0, 5, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/1093995180570554865551461326472104741011901778991144380429496795098352977024584473237365249218733728042379263463561523440443108065841066146779997218414167579750933711988730881963933086471873557569918406123993493302932571942722432197364497568118223362163708293509782215754347767985204013376175258627374283612358942157858958253587106015320875421376164471869160593214974871034453141795147204684279724683062032151555965609145059570069445777233252628141582158814209513435844216477920509365119073156650301067967396803298608427814617088,   box := { reLo := (466275729185868624908064981550458832374322859963860381424079469494442792456076600156900852842063031255165722585495041335343443547318209397575153261347685689854461988482341305204015574513791274377337071887690433355489442743657848900488539411154935752047015848837669678623344808711139433419794934753334083910920724976693081991350471852665559143442181202813644838783089141241504249947109136210146328531134369230437935125502997653960235748131425546958370135629641468263675489511322742992807712473394264249618442887694709980966437731109369749 : Rat)/2374591013150306676201919224837502928896577196513883699875920531755301457010771547749716907068602122014520676316020568578189974221489616202163926010878594276307393166683984012157506458932063129497939472687624768071071744536514039913951477559772553455631708145505062977719149307636190903796198981981446941084981995288620265137993926548495953070691275168588435560680486066994626214663994712413188024766843940232790940527008194346765964537006059983053964813911703026225127016960363200015665978767414617437268436642097014145340349869562265600,            reHi := (1103702690155503701107535004592905436113473161472366147594412069823471869539832380221293681537370888636763389945216672890718516783035233432689001493937687601130545129403555293218646903581081792204632136646783955285039187897360731628868215207560393006739200991615124641956490469355853660260739755890907792534908944392754879138599587715456329600629319539004899157519293329338438535464977029423621281831829669534722167392822476190808929278848694164605849076087800232376062986187890772704504418238774418929153654291099295220843890383867581309 : Rat)/339227287592900953743131317833928989842368170930554814267988647393614493858681649678530986724086017430645810902288652654027139174498516600309132287268370610901056166669140573165358065561723304213991353241089252581581677790930577130564496794253221922233101163643580425388449901090884414828028425997349563012140285041231466448284846649785136152955896452655490794382926580999232316380570673201884003538120562890398705789572599192395137791000865711864852116273100432317875288137194742859380854109630659633895490948871002020762907124223180800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/2187990361141109731102922652944209482023803557982288760858993590196705954049168946474730498437467456084758526927123046880886216131682132293559994436828335159501867423977461763927866172943747115139836812247986986605865143885444864394728995136236446724327416587019564431508695535970408026752350517254748567224717884315717916507174212030641750842752328943738321186429949742068906283590294409368559449366124064303111931218290119140138891554466505256283164317628419026871688432955841018730238146313300602135934793606597216855629234176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := -11 }
def label : String := "540.f2"
def inputConductor : Nat := 540
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 540 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := -11 },   conductor := 540,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, -3, 0, 5, 0, 0, 0, 3, 0, 1, 0, 0, 0, -6, 0, 5, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19961204171896201419830322265625,   alphaHi := (674651885226100947931528953856 : Rat)/2495150521487025165557861328125,   geometricUpper := (6873262811788515 : Rat)/9007199254740992,   tail := (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/1093995180570554865551461326472104741011901778991144380429496795098352977024584473237365249218733728042379263463561523440443108065841066146779997218414167579750933711988730881963933086471873557569918406123993493302932571942722432197364497568118223362163708293509782215754347767985204013376175258627374283612358942157858958253587106015320875421376164471869160593214974871034453141795147204684279724683062032151555965609145059570069445777233252628141582158814209513435844216477920509365119073156650301067967396803298608427814617088,   box := { reLo := (466275729185868624908064981550458832374322859963860381424079469494442792456076600156900852842063031255165722585495041335343443547318209397575153261347685689854461988482341305204015574513791274377337071887690433355489442743657848900488539411154935752047015848837669678623344808711139433419794934753334083910920724976693081991350471852665559143442181202813644838783089141241504249947109136210146328531134369230437935125502997653960235748131425546958370135629641468263675489511322742992807712473394264249618442887694709980966437731109369749 : Rat)/2374591013150306676201919224837502928896577196513883699875920531755301457010771547749716907068602122014520676316020568578189974221489616202163926010878594276307393166683984012157506458932063129497939472687624768071071744536514039913951477559772553455631708145505062977719149307636190903796198981981446941084981995288620265137993926548495953070691275168588435560680486066994626214663994712413188024766843940232790940527008194346765964537006059983053964813911703026225127016960363200015665978767414617437268436642097014145340349869562265600,            reHi := (1103702690155503701107535004592905436113473161472366147594412069823471869539832380221293681537370888636763389945216672890718516783035233432689001493937687601130545129403555293218646903581081792204632136646783955285039187897360731628868215207560393006739200991615124641956490469355853660260739755890907792534908944392754879138599587715456329600629319539004899157519293329338438535464977029423621281831829669534722167392822476190808929278848694164605849076087800232376062986187890772704504418238774418929153654291099295220843890383867581309 : Rat)/339227287592900953743131317833928989842368170930554814267988647393614493858681649678530986724086017430645810902288652654027139174498516600309132287268370610901056166669140573165358065561723304213991353241089252581581677790930577130564496794253221922233101163643580425388449901090884414828028425997349563012140285041231466448284846649785136152955896452655490794382926580999232316380570673201884003538120562890398705789572599192395137791000865711864852116273100432317875288137194742859380854109630659633895490948871002020762907124223180800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1672291043417897725990312129938562110343006028536937158232221063896859778571328183065769665812827149621013432359797102206107310941892064361735657825297382447691243659569597191494214706408326408290363851982499249713772961085445511812997837508350422413090563130855356003809916002162578364965468780979765156893304969583217973032416929622286390207839222940311446328701081398748436191603070164457797856127573497306226519824841196396942043881873510464857740694156798806743392537461514654604676348103866758870107703842222690582275390625 : Rat)/2187990361141109731102922652944209482023803557982288760858993590196705954049168946474730498437467456084758526927123046880886216131682132293559994436828335159501867423977461763927866172943747115139836812247986986605865143885444864394728995136236446724327416587019564431508695535970408026752350517254748567224717884315717916507174212030641750842752328943738321186429949742068906283590294409368559449366124064303111931218290119140138891554466505256283164317628419026871688432955841018730238146313300602135934793606597216855629234176, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N540.C540_f2
