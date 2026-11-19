module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 32, a6 := -212 }
def label : String := "560.a1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 32, a6 := -212 },   conductor := 560,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, 0, -3, 0, -1, 0, 1, 0, 6, 0, 5, 0, -3, 0, 3, 0, -1, 0, -6, 0, -3, 0, -6, 0, 1, 0, -9, 0, -9, 0, 4,                    0, -15, 0, -1, 0, 2, 0, 9, 0, -4, 0, -10, 0, -6, 0, 1, 0, 1, 0, 3, 0, 4, 0, -5, 0, 18, 0, 8, 0, -8,                    0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20327495351151699542999267578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5081873837787924861907958984375,   finite := ((2205830961094249 : Rat)/1125899906842624, (27729971930183733 : Rat)/9007199254740992),   tail := (872125162856242195648025667696475982666015625 : Rat)/448503512386749926100121414263336950766239744,   box := { reLo := (861158381130037349081209746121250874876224568193 : Rat)/58786252375556086313795114010324100810832575725568,            reHi := (2362345685948734012558903471679957709943697063804781 : Rat)/470290019004448690510360912082592806486660605804544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2101, a6 := 39485 }
def label : String := "560.b1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -21, a6 := -35 }
def label : String := "560.b2"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 139, a6 := 61 }
def label : String := "560.b3"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -805, a6 := 9065 }
def label : String := "560.c1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -805, a6 := 9065 },   conductor := 560,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 1, 0, -1, 0, -2, 0, -3, 0, -1, 0, -1, 0, -3, 0, -2, 0, 1, 0, 6, 0, 1, 0, 5, 0, -9, 0,                    -8, 0, 3, 0, -1, 0, -10, 0, 1, 0, 0, 0, -2, 0, -2, 0, 3, 0, 1, 0, 3, 0, 0, 0, -3, 0, 2, 0, -12, 0, 8,                    0, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20327495351151699542999267578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5081873837787924861907958984375,   finite := ((21577629871546359 : Rat)/9007199254740992, (40137000381487363 : Rat)/9007199254740992),   tail := (872125162856242195648025667696475982666015625 : Rat)/448503512386749926100121414263336950766239744,   box := { reLo := (212136384734207142376078200797004261951797356778463 : Rat)/470290019004448690510360912082592806486660605804544,            reHi := (3010149901346887345786559175508320297243954326631691 : Rat)/470290019004448690510360912082592806486660605804544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 25 }
def label : String := "560.c2"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 25 },   conductor := 560,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 1, 0, -1, 0, -2, 0, -3, 0, -1, 0, -1, 0, -3, 0, -2, 0, 1, 0, 6, 0, 1, 0, 5, 0, -9, 0,                    -8, 0, 3, 0, -1, 0, -10, 0, 1, 0, 0, 0, -2, 0, -2, 0, 3, 0, 1, 0, 3, 0, 0, 0, -3, 0, 2, 0, -12, 0, 8,                    0, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20327495351151699542999267578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5081873837787924861907958984375,   finite := ((21577629871546359 : Rat)/9007199254740992, (40137000381487363 : Rat)/9007199254740992),   tail := (872125162856242195648025667696475982666015625 : Rat)/448503512386749926100121414263336950766239744,   box := { reLo := (212136384734207142376078200797004261951797356778463 : Rat)/470290019004448690510360912082592806486660605804544,            reHi := (3010149901346887345786559175508320297243954326631691 : Rat)/470290019004448690510360912082592806486660605804544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4283, a6 := 107882 }
def label : String := "560.d1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 0],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1403, a6 := -18902 }
def label : String := "560.d2"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 0],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -283, a6 := 1482 }
def label : String := "560.d3"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 1],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 37, a6 := 138 }
def label : String := "560.d4"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 1, 0],              kodaira := -12 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := -5 }
def label : String := "560.e1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := -5 },   conductor := 560,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, -1, 0, 1, 0, -2, 0, 5, 0, 1, 0, -1, 0, 3, 0, 6, 0, 1, 0, 6, 0, 1, 0, -5, 0, -9, 0, 0, 0,                    5, 0, -1, 0, 6, 0, 1, 0, 8, 0, -6, 0, 2, 0, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20327495351151699542999267578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5081873837787924861907958984375,   geometricUpper := (6906832471911341 : Rat)/9007199254740992,   tail := (768159675249998410256484059828577996691236017366514375825232162042909085820629445556704376756425712966439663072926822801849201777530602817174095431858649209215243501727717210817802113991094524478461800653749450561803450911429530910988617499705743282253479855547919278011188056185059190188514078423024941640003097063550042413013532371014134318588485145711586582038665080789819564873748830366244536889363499806973248464017781518155522281086757654773689522869032324551246397870863168519480349708027000642891497072660816476055033914022407536187252666857212458095096384186768502437709464149318896256194102236792681490976300133194244969114840861071352130354134323987015295973785286979581283405890368361917121177154840136250061183990439605054917832681813067377661227365711748189560135350061 : Rat)/14410736922155166574328411074849233899242911963462525821531457609708487085276999752995426870422056176952180973629864092558534635622110743430303429435123667042764546116538854886639493665464003790416018476625128950140379028820156506427793152751060520906331440665936693267904938043397216691999513899165284255865986789251865476300179692409946988494349326561525045141969468260340476532938192565527435213682553274466268516331825756829619304622505070321585001593499627655978835638908166884415198088781089111461744237162221618193752441129311179757706953266100263211282503723873500020756695598311254301491925104268089066006263819954377032456808533175891023267420344563186850600233365676228408755340016341907160852517376259286395407649227799336900545510804937862345472882203453379583594238836736,   box := { reLo := (745661845054472222998581361578246634543011746919138128984280544241431885045242828434396364456108493735670640711959734842215341194385870126396564531203200505335640836047845994312879487232988382839902461853234487022984895134503069816167514636660504685820209319704977967762174439239807247458927905762325829007697661458718925304647378004939486216280748427538654070696191540646400815504869345061227834185627105804338220807935482349070431808213289288554459746873232011699851566755921570592220927589464465135729611108529715889921431604412393588990093662334516259675585943294966203394911220534514349993183410833917666737719834865603711788475310794874833610329578341437355398110501012031857303166117358803923744052052774899911267596031408471665272445000353171042787737284990122725308466634115095052554111054943 : Rat)/428758785145351753331643759596701333145328643405351144909102218321791059137501631041041791962614073540214989579368388595623712368158306354458518701451439194536008392643285215382614580866358452019889960577448298504945840696541730841035735612478630304179882270047994302941839929461043831271216684841001997027024748040806524635342587914757759136768208077043049523336843110733932455544798152953156148675765145615660342737976345285177764171288880451183141843064291113987589030146647743655338629384946490878969706187171150482281316344094823180766592087970306554701591988085429023296740970338843731541060440235997451463466125323185971338876358010438052422969656919023057423815470669659986219562605180717973686160419233152226126714671511674239937452957560997296318803877374179279870662831380215440925461053440,            reHi := (3956857710292227357743860585461363463981368456295034445333891485440785902003513860676449827006533932052584383468825108419002428462987076678966550136876895911510371021000176711240547730373866763427595569137742702093972480399491014790929304444185130151771127179895467595091313663259540143561701302253324262263540282408166058011955962300648928943061009521742619055950083886531671720518795994137728292428748416974964117960548025246269169265479918687003728338652836436575541868412685707800974663413470233213174310835866310353867001038985891393003445251194015279112444984580472986705855265449235852535722205047169563583545899744919700757298845536631045024590517021077323256912766575260959479649264951015643868133617876637186225341262771418706968969257461082364487001448811883288126018124185913168437184150053 : Rat)/2143793925726758766658218797983506665726643217026755724545511091608955295687508155205208959813070367701074947896841942978118561840791531772292593507257195972680041963216426076913072904331792260099449802887241492524729203482708654205178678062393151520899411350239971514709199647305219156356083424205009985135123740204032623176712939573788795683841040385215247616684215553669662277723990764765780743378825728078301713689881726425888820856444402255915709215321455569937945150733238718276693146924732454394848530935855752411406581720474115903832960439851532773507959940427145116483704851694218657705302201179987257317330626615929856694381790052190262114848284595115287119077353348299931097813025903589868430802096165761130633573357558371199687264787804986481594019386870896399353314156901077204627305267200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (768159675249998410256484059828577996691236017366514375825232162042909085820629445556704376756425712966439663072926822801849201777530602817174095431858649209215243501727717210817802113991094524478461800653749450561803450911429530910988617499705743282253479855547919278011188056185059190188514078423024941640003097063550042413013532371014134318588485145711586582038665080789819564873748830366244536889363499806973248464017781518155522281086757654773689522869032324551246397870863168519480349708027000642891497072660816476055033914022407536187252666857212458095096384186768502437709464149318896256194102236792681490976300133194244969114840861071352130354134323987015295973785286979581283405890368361917121177154840136250061183990439605054917832681813067377661227365711748189560135350061 : Rat)/28821473844310333148656822149698467798485823926925051643062915219416974170553999505990853740844112353904361947259728185117069271244221486860606858870247334085529092233077709773278987330928007580832036953250257900280758057640313012855586305502121041812662881331873386535809876086794433383999027798330568511731973578503730952600359384819893976988698653123050090283938936520680953065876385131054870427365106548932537032663651513659238609245010140643170003186999255311957671277816333768830396177562178222923488474324443236387504882258622359515413906532200526422565007447747000041513391196622508602983850208536178132012527639908754064913617066351782046534840689126373701200466731352456817510680032683814321705034752518572790815298455598673801091021609875724690945764406906759167188477673472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := -3316 }
def label : String := "560.f1"
def inputConductor : Nat := 560
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 560 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := -3316 },   conductor := 560,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 3, 0, 1, 0, -1, 0, 6, 0, 5, 0, -5, 0, 3, 0, -7, 0, 2, 0, -3, 0, 2, 0, 1, 0, 9, 0, 7, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20327495351151699542999267578125,   alphaHi := (1349303770452201895863057907712 : Rat)/5081873837787924861907958984375,   geometricUpper := (6906832471911341 : Rat)/9007199254740992,   tail := (5891965431716157960223078587123948995944184700606589860125661292618317560625904322782271856200656833366220466790607471412426464862267904893958190550826674192536974127843272546279540201277735603765208617911922188342904188880084504932974473739675624171515767884956062812292338184435961988628260257450676190718413323336871056657963440392755137117190020106085391717146732176301711746654798085024716392353096784202811302630638793531763644270722636314407348072194577526124032227900474555073008220791987179473475782979784144046953479341 : Rat)/3213634139446918615683380662873416068726578002289237570332363555561022548510803854563708338743497726006169112384185756244548111570193032738329715935883973627345434677190100909320058205320944539653427243303149601658469500457554068818389057898979961255954479065140738766133416377460855446544258366008925246516028414929558458241537611258127114608746736044816941937687417443545288331587215985811583414993946970825937453304244253263739379070022708027992200958123043001251128735747172516017020727124947126048378179710440549631924371456,   box := { reLo := (12432923949130261793092171232399013576502172022100775652403531101266399360733812359807694894458117589595049475251196539424068563398313933137948547902926564422209489027319771780743516258235799273509778128089842719287292442601567935638239962749396548585618052563863879117234260994490919303425226128507080527775173502075666524222066081733184730832674182305884842396038541917791650013257341487383128711418857535080808866319873956646710672101252818969510099410954138535941571546728083517864726874744185737422878907363472416248403254177117951167 : Rat)/15345905669189875349516188824791824306933815454685851169758790040587337367935917206466442422113427911388993442462841622223125652306758060588346282515346700131247484516074880227556894254745162162558061625027962959079450092319602459599806176410675453727205731006510732484904986515117101267809439824383404271328231757125696519271664791399032858375545918242529131455960484790746538872269095213251007036727742748859019679795790843900271952925371855055333371047109835932809347201361432656524736963203532889299943281293409002676317691293036707840,            reHi := (2404644796242909541142163816344741322951537605982459820934962472640242861062181720204629666044474584663354989981561905159126245574651151109833798116584199843514250917965093973808894344439606427923782219627711730032849671395163497855946448673673911655560733303149232981396952655346574517532615731091182293548266049801238171059883621720365374975580254920104074833381225167539325768241041472077133546423152421243070843178628099600597713108563644271559528425902539921400728007107461056391117051654691370819719728791570408476955368038118953904611 : Rat)/537106698421645637233066608867713850742683540914004790941557651420556807877757102226325484773969976898614770486199456777809397830736532120592119888037134504593661958062620807964491298916080675689532156875978703567780753231186086085993216174373640880452200585227875636971674528029098544373330393853419149496488111499399378174508267698966150043144107138488519600958616967676128860529418332463785246285470996210065688792852679536509518352388014926936667986648844257648327152047650142978365793712123651125498014845269315093671119195256284774400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (5891965431716157960223078587123948995944184700606589860125661292618317560625904322782271856200656833366220466790607471412426464862267904893958190550826674192536974127843272546279540201277735603765208617911922188342904188880084504932974473739675624171515767884956062812292338184435961988628260257450676190718413323336871056657963440392755137117190020106085391717146732176301711746654798085024716392353096784202811302630638793531763644270722636314407348072194577526124032227900474555073008220791987179473475782979784144046953479341 : Rat)/6427268278893837231366761325746832137453156004578475140664727111122045097021607709127416677486995452012338224768371512489096223140386065476659431871767947254690869354380201818640116410641889079306854486606299203316939000915108137636778115797959922511908958130281477532266832754921710893088516732017850493032056829859116916483075222516254229217493472089633883875374834887090576663174431971623166829987893941651874906608488506527478758140045416055984401916246086002502257471494345032034041454249894252096756359420881099263848742912, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N560.C560_f1
