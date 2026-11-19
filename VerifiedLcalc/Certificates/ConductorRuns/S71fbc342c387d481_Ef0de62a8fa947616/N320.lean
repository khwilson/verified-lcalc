module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -165, a6 := 763 }
def label : String := "320.a1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -165, a6 := 763 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -6, 0, -4, 0, 4, 0, -6, 0, 1, 0, 4, 0, -6, 0, 4,                    0, 0, 0, -2, 0, -2, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((10671231745915863 : Rat)/9007199254740992, (12843125785165965 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (653209154202877888061563095816600715003914892978903 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1234284617064610394663510374730571338078941310113165 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -145, a6 := 975 }
def label : String := "320.a2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -145, a6 := 975 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -6, 0, -4, 0, 4, 0, -6, 0, 1, 0, 4, 0, -6, 0, 4,                    0, 0, 0, -2, 0, -2, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((10671231745915863 : Rat)/9007199254740992, (12843125785165965 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (653209154202877888061563095816600715003914892978903 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1234284617064610394663510374730571338078941310113165 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -5 }
def label : String := "320.a3"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -5 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -6, 0, -4, 0, 4, 0, -6, 0, 1, 0, 4, 0, -6, 0, 4,                    0, 0, 0, -2, 0, -2, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((10671231745915863 : Rat)/9007199254740992, (12843125785165965 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (653209154202877888061563095816600715003914892978903 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1234284617064610394663510374730571338078941310113165 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 15, a6 := -17 }
def label : String := "320.a4"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 15, a6 := -17 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -2, 0, 1, 0, 0, 0, -2, 0, -2, 0, -6, 0, -4, 0, 4, 0, -6, 0, 1, 0, 4, 0, -6, 0, 4,                    0, 0, 0, -2, 0, -2, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((10671231745915863 : Rat)/9007199254740992, (12843125785165965 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (653209154202877888061563095816600715003914892978903 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1234284617064610394663510374730571338078941310113165 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -25, a6 := -57 }
def label : String := "320.b1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -25, a6 := -57 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -2, 0, 1, 0, 2, 0, 1, 0, -4, 0, 6, 0, -2, 0, 2, 0, 8, 0, -4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (4762070251987587306639024162719942829708288465316927033840824756393607773867868158513632049871967963243367612039016827011139702252946310744199863141304066333262716920173417809104554785106614523099334075768516808587561902021710044785786638950578168098560756777955467263878550148136006846271036000472063884042252039489683800503230486158446499735393258765199220029363369362539842670750907365578640279425804123667 : Rat)/18286168080435235084642193194741593889299225360460119090387640301117292093416796297732343295934674831301060682661483502151358707570520219573306767438709642139491033270014518415687374403083990573576673896027364776984826994598003425163905954683016985790674424461014517870832594066678811971190562898371089046029438438863042691651826918829950340818669693172629715738373070757137117089765945516441948465586839224320,            reHi := (2010394141476156165069181070151233999663685500324869786349681182994976943665759400685507261798969929158563745365194735220497417823923524641312645243435547274651392456176173907841567420170659518839435058091106336373485458942522607905681211284681528499411677314684217439458801645133614964022777006869544345350064275614066903068029832512698151876006783425357040570943102242460153046388409659431644516205860503581 : Rat)/1075656945907955004978952540867152581723483844732948181787508253006899534906870370454843723290274990076532981333028441303021100445324718798429809849335861302323001957059677553863963200181411210210392582119256751587342764388117848539053291451942175634745554380059677521813682003922283057128856641080652296825261084639002511273636877578232372989333511363095865631669004162184536299397996795084820497975696424960,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := -2 }
def label : String := "320.b2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := -2 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -2, 0, 1, 0, 2, 0, 1, 0, -4, 0, 6, 0, -2, 0, 2, 0, 8, 0, -4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (4762070251987587306639024162719942829708288465316927033840824756393607773867868158513632049871967963243367612039016827011139702252946310744199863141304066333262716920173417809104554785106614523099334075768516808587561902021710044785786638950578168098560756777955467263878550148136006846271036000472063884042252039489683800503230486158446499735393258765199220029363369362539842670750907365578640279425804123667 : Rat)/18286168080435235084642193194741593889299225360460119090387640301117292093416796297732343295934674831301060682661483502151358707570520219573306767438709642139491033270014518415687374403083990573576673896027364776984826994598003425163905954683016985790674424461014517870832594066678811971190562898371089046029438438863042691651826918829950340818669693172629715738373070757137117089765945516441948465586839224320,            reHi := (2010394141476156165069181070151233999663685500324869786349681182994976943665759400685507261798969929158563745365194735220497417823923524641312645243435547274651392456176173907841567420170659518839435058091106336373485458942522607905681211284681528499411677314684217439458801645133614964022777006869544345350064275614066903068029832512698151876006783425357040570943102242460153046388409659431644516205860503581 : Rat)/1075656945907955004978952540867152581723483844732948181787508253006899534906870370454843723290274990076532981333028441303021100445324718798429809849335861302323001957059677553863963200181411210210392582119256751587342764388117848539053291451942175634745554380059677521813682003922283057128856641080652296825261084639002511273636877578232372989333511363095865631669004162184536299397996795084820497975696424960,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -428, a6 := -3408 }
def label : String := "320.c1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 0, 1, 0],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -428, a6 := -3408 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, -3, 0, -4, 0, 2, 0, 0, 0, 2, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 0, -8, 0,                    0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((12279209155321463 : Rat)/9007199254740992, (14355166929300193 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (791275617218082294847164895353630795736337667632503 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1364113662847813363069069883949492494602556961649633 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28, a6 := -48 }
def label : String := "320.c2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 0],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28, a6 := -48 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, -3, 0, -4, 0, 2, 0, 0, 0, 2, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 0, -8, 0,                    0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((12279209155321463 : Rat)/9007199254740992, (14355166929300193 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (791275617218082294847164895353630795736337667632503 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1364113662847813363069069883949492494602556961649633 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := 8 }
def label : String := "320.c3"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := 8 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, -3, 0, -4, 0, 2, 0, 0, 0, 2, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 0, -8, 0,                    0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((12279209155321463 : Rat)/9007199254740992, (14355166929300193 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (791275617218082294847164895353630795736337667632503 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1364113662847813363069069883949492494602556961649633 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 52, a6 := -272 }
def label : String := "320.c4"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 0, 0, 1],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 52, a6 := -272 },   conductor := 320,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, -3, 0, -4, 0, 2, 0, 0, 0, 2, 0, -4, 0, 0, 0, 4, 0, 1, 0, 0, 0, 2, 0, -8, 0,                    0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   finite := ((12279209155321463 : Rat)/9007199254740992, (14355166929300193 : Rat)/4503599627370496),   tail := (250873045107875113290929978382587432861328125 : Rat)/737561286441082144592478853372917537363197952,   box := { reLo := (791275617218082294847164895353630795736337667632503 : Rat)/773389063491244150848203106154360379658152655716352,            reHi := (1364113662847813363069069883949492494602556961649633 : Rat)/386694531745622075424101553077180189829076327858176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -428, a6 := 3408 }
def label : String := "320.d1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 0, 0],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -428, a6 := 3408 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 4, 0, -3, 0, 4, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (3799076793102152221094573827453256832932848127137309873120571483726060727857134192497519310109307665474674158291713567514019117119587997229774665226335311517325950228574845683129887473335403411537651135313365634397970890818788365005558407854033028308478667993864406402982062115820039871247588067859875986929860811983809906314672662683748436234460519610397034580214194214110055348551943038944886357491387372721 : Rat)/6095389360145078361547397731580531296433075120153373030129213433705764031138932099244114431978224943767020227553827834050452902523506739857768922479569880713163677756671506138562458134361330191192224632009121592328275664866001141721301984894338995263558141487004839290277531355559603990396854299457029682009812812954347563883942306276650113606223231057543238579457690252379039029921981838813982821862279741440,            reHi := (800232559459088622476928413119862252726029105141132046099402822989355424579316736255838222295389402727638287321420582096300412166716435825759391897317331826265455850556588336999190859964311073094709017049117408661853711986684845228041527871681307838624976567096014014507454980007076805056732685422964162707065875837329046987460016352224233650357082786273186496154201225274007608030433599815748772905136690527 : Rat)/358552315302651668326317513622384193907827948244316060595836084335633178302290123484947907763424996692177660444342813767673700148441572932809936616445287100774333985686559184621321066727137070070130860706418917195780921462705949513017763817314058544915184793353225840604560667974094352376285547026884098941753694879667503757878959192744124329777837121031955210556334720728178766465998931694940165991898808320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28, a6 := 48 }
def label : String := "320.d2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28, a6 := 48 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 4, 0, -3, 0, 4, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (3799076793102152221094573827453256832932848127137309873120571483726060727857134192497519310109307665474674158291713567514019117119587997229774665226335311517325950228574845683129887473335403411537651135313365634397970890818788365005558407854033028308478667993864406402982062115820039871247588067859875986929860811983809906314672662683748436234460519610397034580214194214110055348551943038944886357491387372721 : Rat)/6095389360145078361547397731580531296433075120153373030129213433705764031138932099244114431978224943767020227553827834050452902523506739857768922479569880713163677756671506138562458134361330191192224632009121592328275664866001141721301984894338995263558141487004839290277531355559603990396854299457029682009812812954347563883942306276650113606223231057543238579457690252379039029921981838813982821862279741440,            reHi := (800232559459088622476928413119862252726029105141132046099402822989355424579316736255838222295389402727638287321420582096300412166716435825759391897317331826265455850556588336999190859964311073094709017049117408661853711986684845228041527871681307838624976567096014014507454980007076805056732685422964162707065875837329046987460016352224233650357082786273186496154201225274007608030433599815748772905136690527 : Rat)/358552315302651668326317513622384193907827948244316060595836084335633178302290123484947907763424996692177660444342813767673700148441572932809936616445287100774333985686559184621321066727137070070130860706418917195780921462705949513017763817314058544915184793353225840604560667974094352376285547026884098941753694879667503757878959192744124329777837121031955210556334720728178766465998931694940165991898808320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -8 }
def label : String := "320.d3"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -8 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 4, 0, -3, 0, 4, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (3799076793102152221094573827453256832932848127137309873120571483726060727857134192497519310109307665474674158291713567514019117119587997229774665226335311517325950228574845683129887473335403411537651135313365634397970890818788365005558407854033028308478667993864406402982062115820039871247588067859875986929860811983809906314672662683748436234460519610397034580214194214110055348551943038944886357491387372721 : Rat)/6095389360145078361547397731580531296433075120153373030129213433705764031138932099244114431978224943767020227553827834050452902523506739857768922479569880713163677756671506138562458134361330191192224632009121592328275664866001141721301984894338995263558141487004839290277531355559603990396854299457029682009812812954347563883942306276650113606223231057543238579457690252379039029921981838813982821862279741440,            reHi := (800232559459088622476928413119862252726029105141132046099402822989355424579316736255838222295389402727638287321420582096300412166716435825759391897317331826265455850556588336999190859964311073094709017049117408661853711986684845228041527871681307838624976567096014014507454980007076805056732685422964162707065875837329046987460016352224233650357082786273186496154201225274007608030433599815748772905136690527 : Rat)/358552315302651668326317513622384193907827948244316060595836084335633178302290123484947907763424996692177660444342813767673700148441572932809936616445287100774333985686559184621321066727137070070130860706418917195780921462705949513017763817314058544915184793353225840604560667974094352376285547026884098941753694879667503757878959192744124329777837121031955210556334720728178766465998931694940165991898808320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 52, a6 := 272 }
def label : String := "320.d4"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 1, 1],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 52, a6 := 272 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 4, 0, -3, 0, 4, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (3799076793102152221094573827453256832932848127137309873120571483726060727857134192497519310109307665474674158291713567514019117119587997229774665226335311517325950228574845683129887473335403411537651135313365634397970890818788365005558407854033028308478667993864406402982062115820039871247588067859875986929860811983809906314672662683748436234460519610397034580214194214110055348551943038944886357491387372721 : Rat)/6095389360145078361547397731580531296433075120153373030129213433705764031138932099244114431978224943767020227553827834050452902523506739857768922479569880713163677756671506138562458134361330191192224632009121592328275664866001141721301984894338995263558141487004839290277531355559603990396854299457029682009812812954347563883942306276650113606223231057543238579457690252379039029921981838813982821862279741440,            reHi := (800232559459088622476928413119862252726029105141132046099402822989355424579316736255838222295389402727638287321420582096300412166716435825759391897317331826265455850556588336999190859964311073094709017049117408661853711986684845228041527871681307838624976567096014014507454980007076805056732685422964162707065875837329046987460016352224233650357082786273186496154201225274007608030433599815748772905136690527 : Rat)/358552315302651668326317513622384193907827948244316060595836084335633178302290123484947907763424996692177660444342813767673700148441572932809936616445287100774333985686559184621321066727137070070130860706418917195780921462705949513017763817314058544915184793353225840604560667974094352376285547026884098941753694879667503757878959192744124329777837121031955210556334720728178766465998931694940165991898808320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -25, a6 := 57 }
def label : String := "320.e1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -25, a6 := 57 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, -2, 0, 1, 0, 4, 0, 6, 0, 2, 0, 2, 0, -8, 0, -4, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (20538636225227207291099867405511630663717550660844862313571458329901563369922405202630036488464091963579325636282334137198089469407295120366452600809587995707055002115432599557799735438938684800047838044350620128991620442489612167069769946536722239354582005218274815837919887059356401090370722791879729199860441806398897889497800975406147570545223593487494379291437920430530636068780470275138399410852809915923 : Rat)/18286168080435235084642193194741593889299225360460119090387640301117292093416796297732343295934674831301060682661483502151358707570520219573306767438709642139491033270014518415687374403083990573576673896027364776984826994598003425163905954683016985790674424461014517870832594066678811971190562898371089046029438438863042691651826918829950340818669693172629715738373070757137117089765945516441948465586839224320,            reHi := (2938427434019663222978642437374274460487759747120630685157365510848386096374849815045295758186741929178325982085389871113847404127120513442621629812158131355462703350014949304823636870396075417483464703301818296397253608381810968040033170554454709161530574281761826179108292051675991096028640935775877599221722497196961849479475155409621744276585038409021461704006311128812552658037207477641042112172154961949 : Rat)/1075656945907955004978952540867152581723483844732948181787508253006899534906870370454843723290274990076532981333028441303021100445324718798429809849335861302323001957059677553863963200181411210210392582119256751587342764388117848539053291451942175634745554380059677521813682003922283057128856641080652296825261084639002511273636877578232372989333511363095865631669004162184536299397996795084820497975696424960,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 2 }
def label : String := "320.e2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 2 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, -2, 0, 1, 0, 4, 0, 6, 0, 2, 0, 2, 0, -8, 0, -4, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (20538636225227207291099867405511630663717550660844862313571458329901563369922405202630036488464091963579325636282334137198089469407295120366452600809587995707055002115432599557799735438938684800047838044350620128991620442489612167069769946536722239354582005218274815837919887059356401090370722791879729199860441806398897889497800975406147570545223593487494379291437920430530636068780470275138399410852809915923 : Rat)/18286168080435235084642193194741593889299225360460119090387640301117292093416796297732343295934674831301060682661483502151358707570520219573306767438709642139491033270014518415687374403083990573576673896027364776984826994598003425163905954683016985790674424461014517870832594066678811971190562898371089046029438438863042691651826918829950340818669693172629715738373070757137117089765945516441948465586839224320,            reHi := (2938427434019663222978642437374274460487759747120630685157365510848386096374849815045295758186741929178325982085389871113847404127120513442621629812158131355462703350014949304823636870396075417483464703301818296397253608381810968040033170554454709161530574281761826179108292051675991096028640935775877599221722497196961849479475155409621744276585038409021461704006311128812552658037207477641042112172154961949 : Rat)/1075656945907955004978952540867152581723483844732948181787508253006899534906870370454843723290274990076532981333028441303021100445324718798429809849335861302323001957059677553863963200181411210210392582119256751587342764388117848539053291451942175634745554380059677521813682003922283057128856641080652296825261084639002511273636877578232372989333511363095865631669004162184536299397996795084820497975696424960,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -165, a6 := -763 }
def label : String := "320.f1"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -165, a6 := -763 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, -2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (116648037117811801354435043739049189066052422016075890731438217223236105071702575651896943903470547926134079587037201616324826240102272114341223786014863516445090369884765183906136409029230423174470610869786177580689232653255653285578055571550957968768475718356170157240331092558267529959478278275229459948363301230971240598080054886967160435197532512311491671756671527351781099810125003818072220345495547529 : Rat)/97786995082541364088995685533377507429407622248449834707955295727899957718806397314076702117297726370593907393911676482092827313211338072584528168121441936574818359732697959442178472743764655473672052919932431962485705853465258958095753768358379603158686761823607047437607454902025732466259694643695663347751007694454773752148807052566579362666682851190533239242636742016776027217999708644074590725063311360,            reHi := (4657073917648897429777839544055009772254848006423885572283222484405263920747259622711447922801228121197088905171847611346670890891575021662961196144391142391227027859148104231790572774486506838827578709567028408787927671306139929594784961404440176832718330388172101929134143952479923520611610808396547760276591603120973879513218462500057694036329707331578049132753916514993332938346171688276139030863208753383 : Rat)/1662378916403203189512926654067417626299929578223647190035240027374299281219708754339303935994061348300096425696498500195578064324592747233936978858064512921771912115455865310517034036643999143052424899638851343362256999508909402287627814062092453253697674951001319806439326733334437451926414808942826276911767130805731153786529719893631849165333608470239065067124824614285192462705995046949268042326076293120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -145, a6 := -975 }
def label : String := "320.f2"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -145, a6 := -975 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, -2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (116648037117811801354435043739049189066052422016075890731438217223236105071702575651896943903470547926134079587037201616324826240102272114341223786014863516445090369884765183906136409029230423174470610869786177580689232653255653285578055571550957968768475718356170157240331092558267529959478278275229459948363301230971240598080054886967160435197532512311491671756671527351781099810125003818072220345495547529 : Rat)/97786995082541364088995685533377507429407622248449834707955295727899957718806397314076702117297726370593907393911676482092827313211338072584528168121441936574818359732697959442178472743764655473672052919932431962485705853465258958095753768358379603158686761823607047437607454902025732466259694643695663347751007694454773752148807052566579362666682851190533239242636742016776027217999708644074590725063311360,            reHi := (4657073917648897429777839544055009772254848006423885572283222484405263920747259622711447922801228121197088905171847611346670890891575021662961196144391142391227027859148104231790572774486506838827578709567028408787927671306139929594784961404440176832718330388172101929134143952479923520611610808396547760276591603120973879513218462500057694036329707331578049132753916514993332938346171688276139030863208753383 : Rat)/1662378916403203189512926654067417626299929578223647190035240027374299281219708754339303935994061348300096425696498500195578064324592747233936978858064512921771912115455865310517034036643999143052424899638851343362256999508909402287627814062092453253697674951001319806439326733334437451926414808942826276911767130805731153786529719893631849165333608470239065067124824614285192462705995046949268042326076293120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 5 }
def label : String := "320.f3"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 5 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, -2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (116648037117811801354435043739049189066052422016075890731438217223236105071702575651896943903470547926134079587037201616324826240102272114341223786014863516445090369884765183906136409029230423174470610869786177580689232653255653285578055571550957968768475718356170157240331092558267529959478278275229459948363301230971240598080054886967160435197532512311491671756671527351781099810125003818072220345495547529 : Rat)/97786995082541364088995685533377507429407622248449834707955295727899957718806397314076702117297726370593907393911676482092827313211338072584528168121441936574818359732697959442178472743764655473672052919932431962485705853465258958095753768358379603158686761823607047437607454902025732466259694643695663347751007694454773752148807052566579362666682851190533239242636742016776027217999708644074590725063311360,            reHi := (4657073917648897429777839544055009772254848006423885572283222484405263920747259622711447922801228121197088905171847611346670890891575021662961196144391142391227027859148104231790572774486506838827578709567028408787927671306139929594784961404440176832718330388172101929134143952479923520611610808396547760276591603120973879513218462500057694036329707331578049132753916514993332938346171688276139030863208753383 : Rat)/1662378916403203189512926654067417626299929578223647190035240027374299281219708754339303935994061348300096425696498500195578064324592747233936978858064512921771912115455865310517034036643999143052424899638851343362256999508909402287627814062092453253697674951001319806439326733334437451926414808942826276911767130805731153786529719893631849165333608470239065067124824614285192462705995046949268042326076293120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 15, a6 := 17 }
def label : String := "320.f4"
def inputConductor : Nat := 320
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 320 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 15, a6 := 17 },   conductor := 320,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, -2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15366142135991137027740478515625,   alphaHi := (674651885226100947931528953856 : Rat)/1920767766998892116546630859375,   geometricUpper := (6339395635119237 : Rat)/9007199254740992,   tail := (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/54644412079553043192706227963094753287571002337756227082732078651422289122363543928984502570415853664592868678894380031512911215167985779713792937260342571353030491352516161888656129031477610119877202996304826705831303930654539893823607943134525054642563354776912765435108090684920625122594498869076628778049364042466687204158002057857340878766974767571399646967271435007125409520456497231973238964224,   box := { reLo := (116648037117811801354435043739049189066052422016075890731438217223236105071702575651896943903470547926134079587037201616324826240102272114341223786014863516445090369884765183906136409029230423174470610869786177580689232653255653285578055571550957968768475718356170157240331092558267529959478278275229459948363301230971240598080054886967160435197532512311491671756671527351781099810125003818072220345495547529 : Rat)/97786995082541364088995685533377507429407622248449834707955295727899957718806397314076702117297726370593907393911676482092827313211338072584528168121441936574818359732697959442178472743764655473672052919932431962485705853465258958095753768358379603158686761823607047437607454902025732466259694643695663347751007694454773752148807052566579362666682851190533239242636742016776027217999708644074590725063311360,            reHi := (4657073917648897429777839544055009772254848006423885572283222484405263920747259622711447922801228121197088905171847611346670890891575021662961196144391142391227027859148104231790572774486506838827578709567028408787927671306139929594784961404440176832718330388172101929134143952479923520611610808396547760276591603120973879513218462500057694036329707331578049132753916514993332938346171688276139030863208753383 : Rat)/1662378916403203189512926654067417626299929578223647190035240027374299281219708754339303935994061348300096425696498500195578064324592747233936978858064512921771912115455865310517034036643999143052424899638851343362256999508909402287627814062092453253697674951001319806439326733334437451926414808942826276911767130805731153786529719893631849165333608470239065067124824614285192462705995046949268042326076293120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (43949753829884158910791512869981293114208241315443216845562146925988236949762839300024058707554026044035314568953101415651452946775122525327507210265211662527136447309408265252401303789210882898396599247223117744871261219337917049383808909353355931375309002132759166680635962066574853383792787762909234192173558110184720185025773417573579683791432780713031794192962288353962513496317281550973264453125 : Rat)/109288824159106086385412455926189506575142004675512454165464157302844578244727087857969005140831707329185737357788760063025822430335971559427585874520685142706060982705032323777312258062955220239754405992609653411662607861309079787647215886269050109285126709553825530870216181369841250245188997738153257556098728084933374408316004115714681757533949535142799293934542870014250819040912994463946477928448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N320.C320_f4
