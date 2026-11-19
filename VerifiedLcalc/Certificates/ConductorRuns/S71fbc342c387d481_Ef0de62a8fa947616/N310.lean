module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2046, a6 := 15376 }
def label : String := "310.a1"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 5, 31, 31, 31, 31, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2046, a6 := 15376 },   conductor := 310,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -1, -2, -4, 1, 1, -1, 0, -2, -4, -4, 2, 1, 0, 1, -4, -1, 8, 0, -6, -2, 1, -4, 4, -4, 6,                    2, 1, 1, 0, 0, 4, 1, 8, -4, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   finite := ((816000084451661 : Rat)/562949953421312, (983395402640109 : Rat)/281474976710656),   tail := (112843527501729494824626778988552093505859375 : Rat)/369727885392698145065965794209807146017619968,   box := { reLo := (27726954681982817945044681559930156830974605952569 : Rat)/24230486697095865635043134289333921121410742222848,            reHi := (46024952549315761613794298418108704768763334716761 : Rat)/12115243348547932817521567144666960560705371111424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1706, a6 := 26980 }
def label : String := "310.a2"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1706, a6 := 26980 },   conductor := 310,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -1, -2, -4, 1, 1, -1, 0, -2, -4, -4, 2, 1, 0, 1, -4, -1, 8, 0, -6, -2, 1, -4, 4, -4, 6,                    2, 1, 1, 0, 0, 4, 1, 8, -4, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   finite := ((816000084451661 : Rat)/562949953421312, (983395402640109 : Rat)/281474976710656),   tail := (112843527501729494824626778988552093505859375 : Rat)/369727885392698145065965794209807146017619968,   box := { reLo := (27726954681982817945044681559930156830974605952569 : Rat)/24230486697095865635043134289333921121410742222848,            reHi := (46024952549315761613794298418108704768763334716761 : Rat)/12115243348547932817521567144666960560705371111424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -106, a6 := 420 }
def label : String := "310.a3"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -106, a6 := 420 },   conductor := 310,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -1, -2, -4, 1, 1, -1, 0, -2, -4, -4, 2, 1, 0, 1, -4, -1, 8, 0, -6, -2, 1, -4, 4, -4, 6,                    2, 1, 1, 0, 0, 4, 1, 8, -4, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   finite := ((816000084451661 : Rat)/562949953421312, (983395402640109 : Rat)/281474976710656),   tail := (112843527501729494824626778988552093505859375 : Rat)/369727885392698145065965794209807146017619968,   box := { reLo := (27726954681982817945044681559930156830974605952569 : Rat)/24230486697095865635043134289333921121410742222848,            reHi := (46024952549315761613794298418108704768763334716761 : Rat)/12115243348547932817521567144666960560705371111424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 454, a6 := 1876 }
def label : String := "310.a4"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 31, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 454, a6 := 1876 },   conductor := 310,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -1, -2, -4, 1, 1, -1, 0, -2, -4, -4, 2, 1, 0, 1, -4, -1, 8, 0, -6, -2, 1, -4, 4, -4, 6,                    2, 1, 1, 0, 0, 4, 1, 8, -4, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   finite := ((816000084451661 : Rat)/562949953421312, (983395402640109 : Rat)/281474976710656),   tail := (112843527501729494824626778988552093505859375 : Rat)/369727885392698145065965794209807146017619968,   box := { reLo := (27726954681982817945044681559930156830974605952569 : Rat)/24230486697095865635043134289333921121410742222848,            reHi := (46024952549315761613794298418108704768763334716761 : Rat)/12115243348547932817521567144666960560705371111424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1066, a6 := -13841 }
def label : String := "310.b1"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 5, 5, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1066, a6 := -13841 },   conductor := 310,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, 1, -1, 2, 0, 1, 1, -1, 2, 2, 0, 0, -2, 1, 2, 1, -4, -1, 0, 2, -4, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   geometricUpper := (6303866842095331 : Rat)/9007199254740992,   tail := (38188781971863417952796145653018690991433727034827487431609316812373147978350879052865097560022230300419478505956151085325753821330304565082350379292570537201105537099119588154320753076736378743616013276878240798939747851501016502243027182298346965014875341174269798991671604829480814526116560487002308282057193924067353543044384569525308336706263124973725513679888742072874831930286619107677051171875 : Rat)/55620865742348861616736732275417506112481796821456044505973990446034874133959302605015453531682229284683337585621471175751823430325888583171416474588601438145105484788020286476765222973081693238570963946095327802810729686623480990231797364735699365299572208202644360927828835177760664268226569382705970199536661554789854516636227071899885780057171791622545332467167456367286361246091844063511195942912,   box := { reLo := (11280536542216802378936879047433080104000641596142413453809085571219651762391009642268642484787123159345259949376188318752817982187178651803800252558596993862496764379817640848721275694754251864364504850206030710743570646803482705708875126909121262237766698774530516547795223390700792862521380518818204338753048238592270460188663042598824605079014204281750460844911319611176832203509002200360026732745670847 : Rat)/6198111173998645394261057761111149793644409028798954319523211625353896199117754885789897064303009220338687723853728640469904443958365394265706794845780801259699829697353040623538332622005358486040155367333132853706213662628887604146480339339322658772157829021061674359992606248033759622729827759161839789185367880358007438061357963757163771900670938599458339123478805500288555665458244643217370119898398720,            reHi := (2291667096664696047999545112891199435883295272863796096674095550605804667161218209049815971062313124335801019869358129360617565430013779760775029060407348850321674988755463809413592372652445333829274291603917676888349729950422412427977971233228187024743909601838637448580325483083384551349566516143571179258274997702275889318763915981235305569592927365962983933965587185390323834139482618246774962606166037 : Rat)/717676030673527361440754056549712081369352624387247342260582398725187980950476881512514396919295804460269104867273842580725777721494940388660786771616724356386296070219825756409701672021673087857281147796468014639666845146502775216960881397184728910460380202438720189051775460298645851052927424745055133484621544041453492828157237908724226220077687627305702424823861689507095919158323063951484961251393536,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38188781971863417952796145653018690991433727034827487431609316812373147978350879052865097560022230300419478505956151085325753821330304565082350379292570537201105537099119588154320753076736378743616013276878240798939747851501016502243027182298346965014875341174269798991671604829480814526116560487002308282057193924067353543044384569525308336706263124973725513679888742072874831930286619107677051171875 : Rat)/111241731484697723233473464550835012224963593642912089011947980892069748267918605210030907063364458569366675171242942351503646860651777166342832949177202876290210969576040572953530445946163386477141927892190655605621459373246961980463594729471398730599144416405288721855657670355521328536453138765411940399073323109579709033272454143799771560114343583245090664934334912734572722492183688127022391885824, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -66, a6 := -241 }
def label : String := "310.b2"
def inputConductor : Nat := 310
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 310 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -66, a6 := -241 },   conductor := 310,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, 1, -1, 2, 0, 1, 1, -1, 2, 2, 0, 0, -2, 1, 2, 1, -4, -1, 0, 2, -4, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15124140521497360134124755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7562070260748680019378662109375,   geometricUpper := (6303866842095331 : Rat)/9007199254740992,   tail := (38188781971863417952796145653018690991433727034827487431609316812373147978350879052865097560022230300419478505956151085325753821330304565082350379292570537201105537099119588154320753076736378743616013276878240798939747851501016502243027182298346965014875341174269798991671604829480814526116560487002308282057193924067353543044384569525308336706263124973725513679888742072874831930286619107677051171875 : Rat)/55620865742348861616736732275417506112481796821456044505973990446034874133959302605015453531682229284683337585621471175751823430325888583171416474588601438145105484788020286476765222973081693238570963946095327802810729686623480990231797364735699365299572208202644360927828835177760664268226569382705970199536661554789854516636227071899885780057171791622545332467167456367286361246091844063511195942912,   box := { reLo := (11280536542216802378936879047433080104000641596142413453809085571219651762391009642268642484787123159345259949376188318752817982187178651803800252558596993862496764379817640848721275694754251864364504850206030710743570646803482705708875126909121262237766698774530516547795223390700792862521380518818204338753048238592270460188663042598824605079014204281750460844911319611176832203509002200360026732745670847 : Rat)/6198111173998645394261057761111149793644409028798954319523211625353896199117754885789897064303009220338687723853728640469904443958365394265706794845780801259699829697353040623538332622005358486040155367333132853706213662628887604146480339339322658772157829021061674359992606248033759622729827759161839789185367880358007438061357963757163771900670938599458339123478805500288555665458244643217370119898398720,            reHi := (2291667096664696047999545112891199435883295272863796096674095550605804667161218209049815971062313124335801019869358129360617565430013779760775029060407348850321674988755463809413592372652445333829274291603917676888349729950422412427977971233228187024743909601838637448580325483083384551349566516143571179258274997702275889318763915981235305569592927365962983933965587185390323834139482618246774962606166037 : Rat)/717676030673527361440754056549712081369352624387247342260582398725187980950476881512514396919295804460269104867273842580725777721494940388660786771616724356386296070219825756409701672021673087857281147796468014639666845146502775216960881397184728910460380202438720189051775460298645851052927424745055133484621544041453492828157237908724226220077687627305702424823861689507095919158323063951484961251393536,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38188781971863417952796145653018690991433727034827487431609316812373147978350879052865097560022230300419478505956151085325753821330304565082350379292570537201105537099119588154320753076736378743616013276878240798939747851501016502243027182298346965014875341174269798991671604829480814526116560487002308282057193924067353543044384569525308336706263124973725513679888742072874831930286619107677051171875 : Rat)/111241731484697723233473464550835012224963593642912089011947980892069748267918605210030907063364458569366675171242942351503646860651777166342832949177202876290210969576040572953530445946163386477141927892190655605621459373246961980463594729471398730599144416405288721855657670355521328536453138765411940399073323109579709033272454143799771560114343583245090664934334912734572722492183688127022391885824, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N310.C310_b2
