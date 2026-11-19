module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 0 }
def label : String := "288.a1"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 0 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 4, 0, 0, 0,                    0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((11183676750442485 : Rat)/9007199254740992, (12717316061586707 : Rat)/4503599627370496),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (1567290086151918834506725733355877259470620446393515 : Rat)/1558888319307718827778371031168931525166528838238208,            reHi := (2385145407842265522127199484201656581152143598876493 : Rat)/779444159653859413889185515584465762583264419119104,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := 0 }
def label : String := "288.a2"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 3, a6 := 0 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 4, 0, 0, 0,                    0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((11183676750442485 : Rat)/9007199254740992, (12717316061586707 : Rat)/4503599627370496),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (1567290086151918834506725733355877259470620446393515 : Rat)/1558888319307718827778371031168931525166528838238208,            reHi := (2385145407842265522127199484201656581152143598876493 : Rat)/779444159653859413889185515584465762583264419119104,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -291, a6 := -1910 }
def label : String := "288.b1"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -291, a6 := -1910 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 4,                    0, 0, 0, 8, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((5659736296671987 : Rat)/4503599627370496, (25781633982978737 : Rat)/9007199254740992),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (795396229394961555834010777176510259880879261519213 : Rat)/779444159653859413889185515584465762583264419119104,            reHi := (4830346903124125234885391071339452691373451979012463 : Rat)/1558888319307718827778371031168931525166528838238208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -156, a6 := 736 }
def label : String := "288.b2"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -156, a6 := 736 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 4,                    0, 0, 0, 8, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((5659736296671987 : Rat)/4503599627370496, (25781633982978737 : Rat)/9007199254740992),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (795396229394961555834010777176510259880879261519213 : Rat)/779444159653859413889185515584465762583264419119104,            reHi := (4830346903124125234885391071339452691373451979012463 : Rat)/1558888319307718827778371031168931525166528838238208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := -20 }
def label : String := "288.b3"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := -20 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 4,                    0, 0, 0, 8, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((5659736296671987 : Rat)/4503599627370496, (25781633982978737 : Rat)/9007199254740992),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (795396229394961555834010777176510259880879261519213 : Rat)/779444159653859413889185515584465762583264419119104,            reHi := (4830346903124125234885391071339452691373451979012463 : Rat)/1558888319307718827778371031168931525166528838238208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 69, a6 := -146 }
def label : String := "288.b4"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 69, a6 := -146 },   conductor := 288,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 4,                    0, 0, 0, 8, 0, -2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   finite := ((5659736296671987 : Rat)/4503599627370496, (25781633982978737 : Rat)/9007199254740992),   tail := (175611579981177977927994662893390655517578125 : Rat)/743335876134738363160310283264604342063202304,   box := { reLo := (795396229394961555834010777176510259880879261519213 : Rat)/779444159653859413889185515584465762583264419119104,            reHi := (4830346903124125234885391071339452691373451979012463 : Rat)/1558888319307718827778371031168931525166528838238208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -291, a6 := 1910 }
def label : String := "288.c1"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -291, a6 := 1910 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -2, 0, 4, 0, 0, 0, 4, 0, -2, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (82476964270601734617375037976861216576955785768529611976068293241203208049456186724643354539584914952362434013777143642605646048009639013586850580958499452365216425579741247881631392832810126750701945676770572347785616549499909690692402352679855641086082599190698776313930255494667625379170321868104255807601625545214521309523673206048494774237165870293514623401924376078836657490782871904356458109003937383 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            reHi := (170847707257807251366633307670522047221638164168982699959003117210726603355868689957659418408093317598115010313928800753165943601924964298377779726830999394852162715165677933453634400188860853775988706595999125006751604795987493848669340319591506829185625540560457830630686537402941210683906731459201654312050544488133945990246565724837718971445146234930329652783752306445752512503525944076322082998022523289 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -156, a6 := -736 }
def label : String := "288.c2"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -156, a6 := -736 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -2, 0, 4, 0, 0, 0, 4, 0, -2, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (82476964270601734617375037976861216576955785768529611976068293241203208049456186724643354539584914952362434013777143642605646048009639013586850580958499452365216425579741247881631392832810126750701945676770572347785616549499909690692402352679855641086082599190698776313930255494667625379170321868104255807601625545214521309523673206048494774237165870293514623401924376078836657490782871904356458109003937383 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            reHi := (170847707257807251366633307670522047221638164168982699959003117210726603355868689957659418408093317598115010313928800753165943601924964298377779726830999394852162715165677933453634400188860853775988706595999125006751604795987493848669340319591506829185625540560457830630686537402941210683906731459201654312050544488133945990246565724837718971445146234930329652783752306445752512503525944076322082998022523289 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := 20 }
def label : String := "288.c3"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := 20 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -2, 0, 4, 0, 0, 0, 4, 0, -2, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (82476964270601734617375037976861216576955785768529611976068293241203208049456186724643354539584914952362434013777143642605646048009639013586850580958499452365216425579741247881631392832810126750701945676770572347785616549499909690692402352679855641086082599190698776313930255494667625379170321868104255807601625545214521309523673206048494774237165870293514623401924376078836657490782871904356458109003937383 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            reHi := (170847707257807251366633307670522047221638164168982699959003117210726603355868689957659418408093317598115010313928800753165943601924964298377779726830999394852162715165677933453634400188860853775988706595999125006751604795987493848669340319591506829185625540560457830630686537402941210683906731459201654312050544488133945990246565724837718971445146234930329652783752306445752512503525944076322082998022523289 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 69, a6 := 146 }
def label : String := "288.c4"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 2, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 69, a6 := 146 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -2, 0, 4, 0, 0, 0, 4, 0, -2, 0, 0, 0, 6, 0, 4, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (82476964270601734617375037976861216576955785768529611976068293241203208049456186724643354539584914952362434013777143642605646048009639013586850580958499452365216425579741247881631392832810126750701945676770572347785616549499909690692402352679855641086082599190698776313930255494667625379170321868104255807601625545214521309523673206048494774237165870293514623401924376078836657490782871904356458109003937383 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            reHi := (170847707257807251366633307670522047221638164168982699959003117210726603355868689957659418408093317598115010313928800753165943601924964298377779726830999394852162715165677933453634400188860853775988706595999125006751604795987493848669340319591506829185625540560457830630686537402941210683906731459201654312050544488133945990246565724837718971445146234930329652783752306445752512503525944076322082998022523289 : Rat)/93639866920776903545591670638803875883686721005222581168974813670810563890875856848504293298941977139741794477290870861731532707474284841701864381465847881261080388565577902443849930038153434984352885476318242829504166052434457883362528733198286510971625479379029543751206007798250188024715241351562664347156486759341465037923548315086111955066809409426768795454967487505139863759154814243354312793590333440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -99, a6 := -378 }
def label : String := "288.d1"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -99, a6 := -378 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (66691912799582033166759058809490792029988022084937930669922003526739639853840287214981757024093095982251598226238124767134206726787815508225761563823910715655431717752199081416841307613370669428285110635042704042253983798576476791902804443212079050172975081429928390869648353382332518640777419429790431453440688030513654671778566275439646284072888092435999091869233286088572514494105770687827642539332817 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (127095701580993854380145429387832449983169797108548476931240812139776046966080532223948263109561843705596343670650165149361643600822238878753507383488377504453929931016232066910670696775246520372396070345241434143856006471835986363265706435480446067268225843549926107838018319445420980805525415804096290201802755864137455098422207482879009643690383148610349485631309517422654298654325039793646798739319599 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -99, a6 := 378 }
def label : String := "288.d2"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -99, a6 := 378 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (66691912799582033166759058809490792029988022084937930669922003526739639853840287214981757024093095982251598226238124767134206726787815508225761563823910715655431717752199081416841307613370669428285110635042704042253983798576476791902804443212079050172975081429928390869648353382332518640777419429790431453440688030513654671778566275439646284072888092435999091869233286088572514494105770687827642539332817 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (127095701580993854380145429387832449983169797108548476931240812139776046966080532223948263109561843705596343670650165149361643600822238878753507383488377504453929931016232066910670696775246520372396070345241434143856006471835986363265706435480446067268225843549926107838018319445420980805525415804096290201802755864137455098422207482879009643690383148610349485631309517422654298654325039793646798739319599 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -9, a6 := 0 }
def label : String := "288.d3"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -9, a6 := 0 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (66691912799582033166759058809490792029988022084937930669922003526739639853840287214981757024093095982251598226238124767134206726787815508225761563823910715655431717752199081416841307613370669428285110635042704042253983798576476791902804443212079050172975081429928390869648353382332518640777419429790431453440688030513654671778566275439646284072888092435999091869233286088572514494105770687827642539332817 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (127095701580993854380145429387832449983169797108548476931240812139776046966080532223948263109561843705596343670650165149361643600822238878753507383488377504453929931016232066910670696775246520372396070345241434143856006471835986363265706435480446067268225843549926107838018319445420980805525415804096290201802755864137455098422207482879009643690383148610349485631309517422654298654325039793646798739319599 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 36, a6 := 0 }
def label : String := "288.d4"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 36, a6 := 0 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (66691912799582033166759058809490792029988022084937930669922003526739639853840287214981757024093095982251598226238124767134206726787815508225761563823910715655431717752199081416841307613370669428285110635042704042253983798576476791902804443212079050172975081429928390869648353382332518640777419429790431453440688030513654671778566275439646284072888092435999091869233286088572514494105770687827642539332817 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (127095701580993854380145429387832449983169797108548476931240812139776046966080532223948263109561843705596343670650165149361643600822238878753507383488377504453929931016232066910670696775246520372396070345241434143856006471835986363265706435480446067268225843549926107838018319445420980805525415804096290201802755864137455098422207482879009643690383148610349485631309517422654298654325039793646798739319599 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := 0 }
def label : String := "288.e1"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := 0 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (73912782009874551757896725204318715208637292153595583860670454661245000518366549371981062414138752327695211490361517945794070999718317485948571079450864729847566320226170162988580869180531056510496838494676485355770336859567573114848203241081362233147040021327055799146905464752947803359667719494949256813745477152555087643951834373837609685358147162711162193927730798138065375721470305833337052555924689 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (134316570791286383672119767906906221184941268153630579684385852549943817613316617556985466333117052987998783067585489904959509051195687563316756564888912360263057923336022685714273878042322944379372700247706032864837801905948587070812731962256527849282146326321726065099199837387004332092259442813729250341094263720162042228228581163993448785310680203531386229171461412946923404813639255148942501004946223 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := 0 }
def label : String := "288.e2"
def inputConductor : Nat := 288
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 288 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 27, a6 := 0 },   conductor := 288,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7288801199942519283294677734375,   alphaHi := (5397215081808807583452231630848 : Rat)/14577602399885038471221923828125,   geometricUpper := (6220087224721503 : Rat)/9007199254740992,   tail := (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/57923418328282802983760308198800503449297897771097373938120587567732925830130152725605226537513246592257151193877868794816040125493258964999003709272676476007633473996949120504170708572018343875538013365160067690516397566788912563203068592830257365527120235417232639652116309571697768500672851205489658544029646365610528813553968208315592738572145754819031615724812331634396478913751767887440307552256,   box := { reLo := (73912782009874551757896725204318715208637292153595583860670454661245000518366549371981062414138752327695211490361517945794070999718317485948571079450864729847566320226170162988580869180531056510496838494676485355770336859567573114848203241081362233147040021327055799146905464752947803359667719494949256813745477152555087643951834373837609685358147162711162193927730798138065375721470305833337052555924689 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            reHi := (134316570791286383672119767906906221184941268153630579684385852549943817613316617556985466333117052987998783067585489904959509051195687563316756564888912360263057923336022685714273878042322944379372700247706032864837801905948587070812731962256527849282146326321726065099199837387004332092259442813729250341094263720162042228228581163993448785310680203531386229171461412946923404813639255148942501004946223 : Rat)/64005377252752497297055140559674556311474177037062598201623249262344883042293818761793775323952137484444152069235045018271724338670051156323899098746307505988434988766628778157108632972080269982469504768501874798020619311301748382339390795077434388907467860136042066815588522076726034193243500582066072691152759233999634338977134870188729976122221059075029935375917626456008109199695703515621539845242880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (27332031122810766101857628342246013417202718893688926697080527769411655980898397016111887890067332618720564010448096088175371401914873279465629879978471473451088784503822287245899492853161076852940892420387196405328685386646787914554786373916699020037354551980143380117604167352170226536501534848077761549878875830117605623598975143136865793100106494907617186787367999374902321590632875738143337109375 : Rat)/115846836656565605967520616397601006898595795542194747876241175135465851660260305451210453075026493184514302387755737589632080250986517929998007418545352952015266947993898241008341417144036687751076026730320135381032795133577825126406137185660514731054240470834465279304232619143395537001345702410979317088059292731221057627107936416631185477144291509638063231449624663268792957827503535774880615104512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N288.C288_e2
