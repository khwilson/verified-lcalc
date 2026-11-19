module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -483, a6 := -4293 }
def label : String := "390.a1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 5, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -483, a6 := -4293 },   conductor := 390,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, -1, -1, 0, 1, 1, -6, -1, 0, -1, 0, 0, -4, 1, 1, 1, -1, 0, -10,                    -1, 0, -1, 0, 6, 0, 1, -6, 0, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   finite := ((868609005922155 : Rat)/1125899906842624, (28252600632040633 : Rat)/9007199254740992),   tail := (235093004979167467092614876849651336669921875 : Rat)/361095864199413782866197629393525523062194176,   box := { reLo := (5699685686204709669587341720375220626888746052465 : Rat)/47329557112345563347838255679868177358807915036672,            reHi := (1434170033357897069674014838333823188497943905501499 : Rat)/378636456898764506782706045438945418870463320293376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -33, a6 := -63 }
def label : String := "390.a2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -33, a6 := -63 },   conductor := 390,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, -1, -1, 0, 1, 1, -6, -1, 0, -1, 0, 0, -4, 1, 1, 1, -1, 0, -10,                    -1, 0, -1, 0, 6, 0, 1, -6, 0, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   finite := ((868609005922155 : Rat)/1125899906842624, (28252600632040633 : Rat)/9007199254740992),   tail := (235093004979167467092614876849651336669921875 : Rat)/361095864199413782866197629393525523062194176,   box := { reLo := (5699685686204709669587341720375220626888746052465 : Rat)/47329557112345563347838255679868177358807915036672,            reHi := (1434170033357897069674014838333823188497943905501499 : Rat)/378636456898764506782706045438945418870463320293376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -13, a6 := 13 }
def label : String := "390.a3"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -13, a6 := 13 },   conductor := 390,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, -1, -1, 0, 1, 1, -6, -1, 0, -1, 0, 0, -4, 1, 1, 1, -1, 0, -10,                    -1, 0, -1, 0, 6, 0, 1, -6, 0, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   finite := ((868609005922155 : Rat)/1125899906842624, (28252600632040633 : Rat)/9007199254740992),   tail := (235093004979167467092614876849651336669921875 : Rat)/361095864199413782866197629393525523062194176,   box := { reLo := (5699685686204709669587341720375220626888746052465 : Rat)/47329557112345563347838255679868177358807915036672,            reHi := (1434170033357897069674014838333823188497943905501499 : Rat)/378636456898764506782706045438945418870463320293376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 97, a6 := -297 }
def label : String := "390.a4"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 97, a6 := -297 },   conductor := 390,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 0, -1, -1, 0, 1, 1, -6, -1, 0, -1, 0, 0, -4, 1, 1, 1, -1, 0, -10,                    -1, 0, -1, 0, 6, 0, 1, -6, 0, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   finite := ((868609005922155 : Rat)/1125899906842624, (28252600632040633 : Rat)/9007199254740992),   tail := (235093004979167467092614876849651336669921875 : Rat)/361095864199413782866197629393525523062194176,   box := { reLo := (5699685686204709669587341720375220626888746052465 : Rat)/47329557112345563347838255679868177358807915036672,            reHi := (1434170033357897069674014838333823188497943905501499 : Rat)/378636456898764506782706045438945418870463320293376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -852, a6 := -9936 }
def label : String := "390.b1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -852, a6 := -9936 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 1, 1, -2, -1, 1, -1, 4, -1, -1, 2, -1, 1, 4, -1, -2, 1, 2, -4, 2, 1, 1, 1, -1, -2, 8,                    1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (29842027082912800608070790166266824603845710158400432879523722457680667573079306375128540239508582056094552920870822912264240448067302916047081688505829357289560446529901340402575188576202651385940904513576681734747765848870271095573769168227099283027141739473173416235455188768054120949576871206197600272413223800430803174698347309496638855808264516542069170710029290047483262613202171590666817537859227328476705459358514885430386958507717858222416408752311751252512545966268390229739947974204841247337828423046705170709 : Rat)/48129295644927301232765757663164973796328662994792206641090751639804177364965219760796728493311682062415998889449983469481832318285716580832651700363028422747009827102024680664290995554455613202249063907084709003236658245105420352467413416936875162678731736062382458788164612269335147847515218730244445449609129425354419364700778846720160534866745720196921952069686846704433494696097816801258915458963322069845109971586389745687303052743304200909782598942709760832489224278430158235458715916378019792286762434716279767040,            reHi := (16237210745059308820761568079423558757744460673212999858489763247261582436580494986796531029344800450355605405962713751205684511286334751619074148209166712634391826141634843845911830717019361726161916931873107910223801122666878517835301113663920335811620538622165400451095923995034342258161873648052045493677676891837428800822607427907853447824381154671666154335120174803462803428129004092930343142981806752274990993377934276851827407157926084905347991156100146741550701995099093362032336129363005557935405474025029242919 : Rat)/14155675189684500362578164018577933469508430292585943129732574011707110989695652870822567203915200606592940849838230432200538917142857817891956382459714241984414655030007259018909116339545768588896783502083737942128428895619241280137474534393198577258450510606583076114166062432157396425739770214777778073414449830986593930794346719623576627901984035352035868255790249030715733734146416706252622193812741785248561756348938160496265603748030647326406646747855812009555654199538281833958445857758241115378459539622435225600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -52, a6 := -176 }
def label : String := "390.b2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -52, a6 := -176 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 1, 1, -2, -1, 1, -1, 4, -1, -1, 2, -1, 1, 4, -1, -2, 1, 2, -4, 2, 1, 1, 1, -1, -2, 8,                    1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (29842027082912800608070790166266824603845710158400432879523722457680667573079306375128540239508582056094552920870822912264240448067302916047081688505829357289560446529901340402575188576202651385940904513576681734747765848870271095573769168227099283027141739473173416235455188768054120949576871206197600272413223800430803174698347309496638855808264516542069170710029290047483262613202171590666817537859227328476705459358514885430386958507717858222416408752311751252512545966268390229739947974204841247337828423046705170709 : Rat)/48129295644927301232765757663164973796328662994792206641090751639804177364965219760796728493311682062415998889449983469481832318285716580832651700363028422747009827102024680664290995554455613202249063907084709003236658245105420352467413416936875162678731736062382458788164612269335147847515218730244445449609129425354419364700778846720160534866745720196921952069686846704433494696097816801258915458963322069845109971586389745687303052743304200909782598942709760832489224278430158235458715916378019792286762434716279767040,            reHi := (16237210745059308820761568079423558757744460673212999858489763247261582436580494986796531029344800450355605405962713751205684511286334751619074148209166712634391826141634843845911830717019361726161916931873107910223801122666878517835301113663920335811620538622165400451095923995034342258161873648052045493677676891837428800822607427907853447824381154671666154335120174803462803428129004092930343142981806752274990993377934276851827407157926084905347991156100146741550701995099093362032336129363005557935405474025029242919 : Rat)/14155675189684500362578164018577933469508430292585943129732574011707110989695652870822567203915200606592940849838230432200538917142857817891956382459714241984414655030007259018909116339545768588896783502083737942128428895619241280137474534393198577258450510606583076114166062432157396425739770214777778073414449830986593930794346719623576627901984035352035868255790249030715733734146416706252622193812741785248561756348938160496265603748030647326406646747855812009555654199538281833958445857758241115378459539622435225600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -86529, a6 := 9789652 }
def label : String := "390.c1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -86529, a6 := 9789652 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, -1, -4, -1, 1, -2, -1, 4, -1, 4, 0, 8, -1, 1, 1, 1, 4, 2, 1,                    -8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (269536719728427798884364699727716670879942041129358367601711071197581197440970157788068282895535581687891437277991274115181915272210323657234883761400907514966965251948125596141212273015261815976799062902061399753883576385096669334880259827608774381324384313034367246552757555178511840429985953915856127825860044756484896832429063743335703056626723774270049992972561933577651110585613172775009955976271386363029028475942487734419214323882514073889253512323378335722574496321790543701872287374869179170670186423168198767 : Rat)/257375912539718188410512073065053335809244187137926238722410436576492927085375506742228494616640011028962560906149644221827980311688323961671934226540258945171175546000131982161983933446286701616305154583340689856880525374895296002499536988967246859244554738301510474803019316948316298649814003905050510425717269654301707832624485811337756870945164279127924877378004527831195158802662121931865858069322577913610213751798875645386647340873284496843757213597378400173739167264332396981062651959240747552335627993135185920,            reHi := (4919990651915899359047348060771206172868083269691820999180309142195791546091944232116624105265138720286305033868650702647850756800352795710505570864107156098874646336769696798510513413346865203958767531329525560521118024737969000373992373486830944061877062579829391541413667664008237594420946186449082323636562108150108487971705366333560671516894620416808650236857028357132601816000145283836685489767279954060795320671054850742868093126059204545865728563751708545380352943829650812121230314437139628382232012495280451699 : Rat)/3125278937982292287841932315789933363397965129531961470200698158428842686036702581869917434630628705351688239574674251265054046641929648106016344179417430048507131630001602640538376334704909948197991162797708376833549236695157165744637234866030854719398164679375484336893805991515269340747741475989899055169423988659377880824725899137672762004334137675124802082447197837950226928318040052029799705127488446093838309843272061408266431996318454604531337593682452002109689888209750534770046488076494791706932625630927257600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6209, a6 := 104276 }
def label : String := "390.c2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6209, a6 := 104276 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, -1, -4, -1, 1, -2, -1, 4, -1, 4, 0, 8, -1, 1, 1, 1, 4, 2, 1,                    -8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (269536719728427798884364699727716670879942041129358367601711071197581197440970157788068282895535581687891437277991274115181915272210323657234883761400907514966965251948125596141212273015261815976799062902061399753883576385096669334880259827608774381324384313034367246552757555178511840429985953915856127825860044756484896832429063743335703056626723774270049992972561933577651110585613172775009955976271386363029028475942487734419214323882514073889253512323378335722574496321790543701872287374869179170670186423168198767 : Rat)/257375912539718188410512073065053335809244187137926238722410436576492927085375506742228494616640011028962560906149644221827980311688323961671934226540258945171175546000131982161983933446286701616305154583340689856880525374895296002499536988967246859244554738301510474803019316948316298649814003905050510425717269654301707832624485811337756870945164279127924877378004527831195158802662121931865858069322577913610213751798875645386647340873284496843757213597378400173739167264332396981062651959240747552335627993135185920,            reHi := (4919990651915899359047348060771206172868083269691820999180309142195791546091944232116624105265138720286305033868650702647850756800352795710505570864107156098874646336769696798510513413346865203958767531329525560521118024737969000373992373486830944061877062579829391541413667664008237594420946186449082323636562108150108487971705366333560671516894620416808650236857028357132601816000145283836685489767279954060795320671054850742868093126059204545865728563751708545380352943829650812121230314437139628382232012495280451699 : Rat)/3125278937982292287841932315789933363397965129531961470200698158428842686036702581869917434630628705351688239574674251265054046641929648106016344179417430048507131630001602640538376334704909948197991162797708376833549236695157165744637234866030854719398164679375484336893805991515269340747741475989899055169423988659377880824725899137672762004334137675124802082447197837950226928318040052029799705127488446093838309843272061408266431996318454604531337593682452002109689888209750534770046488076494791706932625630927257600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5409, a6 := 152596 }
def label : String := "390.c3"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5409, a6 := 152596 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, -1, -4, -1, 1, -2, -1, 4, -1, 4, 0, 8, -1, 1, 1, 1, 4, 2, 1,                    -8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (269536719728427798884364699727716670879942041129358367601711071197581197440970157788068282895535581687891437277991274115181915272210323657234883761400907514966965251948125596141212273015261815976799062902061399753883576385096669334880259827608774381324384313034367246552757555178511840429985953915856127825860044756484896832429063743335703056626723774270049992972561933577651110585613172775009955976271386363029028475942487734419214323882514073889253512323378335722574496321790543701872287374869179170670186423168198767 : Rat)/257375912539718188410512073065053335809244187137926238722410436576492927085375506742228494616640011028962560906149644221827980311688323961671934226540258945171175546000131982161983933446286701616305154583340689856880525374895296002499536988967246859244554738301510474803019316948316298649814003905050510425717269654301707832624485811337756870945164279127924877378004527831195158802662121931865858069322577913610213751798875645386647340873284496843757213597378400173739167264332396981062651959240747552335627993135185920,            reHi := (4919990651915899359047348060771206172868083269691820999180309142195791546091944232116624105265138720286305033868650702647850756800352795710505570864107156098874646336769696798510513413346865203958767531329525560521118024737969000373992373486830944061877062579829391541413667664008237594420946186449082323636562108150108487971705366333560671516894620416808650236857028357132601816000145283836685489767279954060795320671054850742868093126059204545865728563751708545380352943829650812121230314437139628382232012495280451699 : Rat)/3125278937982292287841932315789933363397965129531961470200698158428842686036702581869917434630628705351688239574674251265054046641929648106016344179417430048507131630001602640538376334704909948197991162797708376833549236695157165744637234866030854719398164679375484336893805991515269340747741475989899055169423988659377880824725899137672762004334137675124802082447197837950226928318040052029799705127488446093838309843272061408266431996318454604531337593682452002109689888209750534770046488076494791706932625630927257600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -289, a6 := 3092 }
def label : String := "390.c4"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -289, a6 := 3092 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, -1, -4, -1, 1, -2, -1, 4, -1, 4, 0, 8, -1, 1, 1, 1, 4, 2, 1,                    -8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (269536719728427798884364699727716670879942041129358367601711071197581197440970157788068282895535581687891437277991274115181915272210323657234883761400907514966965251948125596141212273015261815976799062902061399753883576385096669334880259827608774381324384313034367246552757555178511840429985953915856127825860044756484896832429063743335703056626723774270049992972561933577651110585613172775009955976271386363029028475942487734419214323882514073889253512323378335722574496321790543701872287374869179170670186423168198767 : Rat)/257375912539718188410512073065053335809244187137926238722410436576492927085375506742228494616640011028962560906149644221827980311688323961671934226540258945171175546000131982161983933446286701616305154583340689856880525374895296002499536988967246859244554738301510474803019316948316298649814003905050510425717269654301707832624485811337756870945164279127924877378004527831195158802662121931865858069322577913610213751798875645386647340873284496843757213597378400173739167264332396981062651959240747552335627993135185920,            reHi := (4919990651915899359047348060771206172868083269691820999180309142195791546091944232116624105265138720286305033868650702647850756800352795710505570864107156098874646336769696798510513413346865203958767531329525560521118024737969000373992373486830944061877062579829391541413667664008237594420946186449082323636562108150108487971705366333560671516894620416808650236857028357132601816000145283836685489767279954060795320671054850742868093126059204545865728563751708545380352943829650812121230314437139628382232012495280451699 : Rat)/3125278937982292287841932315789933363397965129531961470200698158428842686036702581869917434630628705351688239574674251265054046641929648106016344179417430048507131630001602640538376334704909948197991162797708376833549236695157165744637234866030854719398164679375484336893805991515269340747741475989899055169423988659377880824725899137672762004334137675124802082447197837950226928318040052029799705127488446093838309843272061408266431996318454604531337593682452002109689888209750534770046488076494791706932625630927257600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -872578, a6 := -313799212 }
def label : String := "390.d1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -872578, a6 := -313799212 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 1, -2, 1, 1, 0, -1, 2, 1, 2, 0, -6, -1, 1, -1, 1, 2, 0, -1,                    8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (10138399158768979325205170260100366569574279835516587389262006440347674634291505862027326153523656045274389096725648114452205215405295986932177098420591133743660302608114006294354880232873514753767029905628324192172008803115657303884049833783554896045332923026128144910596448837011563211440991237885851903360919547103147813883380399620863362000023784555679389355278931173644082344436462464438562056132679048088772070948758943561392322388396941116125342843485197150567992312643927887490122324015208212155176068672404731 : Rat)/8875031466886834083121105967760459855491178866825042714565877123327342313288810577318223952297931414791812445039642904200964838334080136609377042294491687764523294689659723522827032187802989710907074295977265167478638806030872275948259896171284374456708784079362430165621355756838493056890138065691396911231629988079369235607740890046129547273971182038893961288896707856248108924229728342478133036873192341848628060406857780875401632443906361960129559089564772419784109216011461964864229377904853363873642344590868480,            reHi := (10582575286253393773714660338995222710768416211777785969171825679744171575011242532540421851578075726532760103492833979190212878590938685434376297845887543250784386533524486378271424054624253550807560554029945465003475712630029732489551653476632918157077142963809068078718047000843719660160468811559421739519267568115667296590825976051034102903062251018587365917626301512613470950424923733472260774856609357181056678392872499365155336928867225826363412381963879236312508317807296854540175269653092834957822860715012063 : Rat)/6339308190633452916515075691257471325350842047732173367547055088090958795206293269513017108784236724851294603599744931572117741667200097578126458781779776974659496206899802516305022991287849793505053068555189405341884861450623054248757068693774553183363417199544592975443825540598923612064384332636712079451164277199549454005529207175806819481407987170638543777783362754462934945878377387484380740623708815606162900290612700625286880317075972828663970778260551728417220868579615689188735269932038117052601674707763200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -53378, a6 := -5124652 }
def label : String := "390.d2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5,              13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -53378, a6 := -5124652 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 1, -2, 1, 1, 0, -1, 2, 1, 2, 0, -6, -1, 1, -1, 1, 2, 0, -1,                    8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (10138399158768979325205170260100366569574279835516587389262006440347674634291505862027326153523656045274389096725648114452205215405295986932177098420591133743660302608114006294354880232873514753767029905628324192172008803115657303884049833783554896045332923026128144910596448837011563211440991237885851903360919547103147813883380399620863362000023784555679389355278931173644082344436462464438562056132679048088772070948758943561392322388396941116125342843485197150567992312643927887490122324015208212155176068672404731 : Rat)/8875031466886834083121105967760459855491178866825042714565877123327342313288810577318223952297931414791812445039642904200964838334080136609377042294491687764523294689659723522827032187802989710907074295977265167478638806030872275948259896171284374456708784079362430165621355756838493056890138065691396911231629988079369235607740890046129547273971182038893961288896707856248108924229728342478133036873192341848628060406857780875401632443906361960129559089564772419784109216011461964864229377904853363873642344590868480,            reHi := (10582575286253393773714660338995222710768416211777785969171825679744171575011242532540421851578075726532760103492833979190212878590938685434376297845887543250784386533524486378271424054624253550807560554029945465003475712630029732489551653476632918157077142963809068078718047000843719660160468811559421739519267568115667296590825976051034102903062251018587365917626301512613470950424923733472260774856609357181056678392872499365155336928867225826363412381963879236312508317807296854540175269653092834957822860715012063 : Rat)/6339308190633452916515075691257471325350842047732173367547055088090958795206293269513017108784236724851294603599744931572117741667200097578126458781779776974659496206899802516305022991287849793505053068555189405341884861450623054248757068693774553183363417199544592975443825540598923612064384332636712079451164277199549454005529207175806819481407987170638543777783362754462934945878377387484380740623708815606162900290612700625286880317075972828663970778260551728417220868579615689188735269932038117052601674707763200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -16003, a6 := 27998 }
def label : String := "390.d3"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -16003, a6 := 27998 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 1, -2, 1, 1, 0, -1, 2, 1, 2, 0, -6, -1, 1, -1, 1, 2, 0, -1,                    8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (10138399158768979325205170260100366569574279835516587389262006440347674634291505862027326153523656045274389096725648114452205215405295986932177098420591133743660302608114006294354880232873514753767029905628324192172008803115657303884049833783554896045332923026128144910596448837011563211440991237885851903360919547103147813883380399620863362000023784555679389355278931173644082344436462464438562056132679048088772070948758943561392322388396941116125342843485197150567992312643927887490122324015208212155176068672404731 : Rat)/8875031466886834083121105967760459855491178866825042714565877123327342313288810577318223952297931414791812445039642904200964838334080136609377042294491687764523294689659723522827032187802989710907074295977265167478638806030872275948259896171284374456708784079362430165621355756838493056890138065691396911231629988079369235607740890046129547273971182038893961288896707856248108924229728342478133036873192341848628060406857780875401632443906361960129559089564772419784109216011461964864229377904853363873642344590868480,            reHi := (10582575286253393773714660338995222710768416211777785969171825679744171575011242532540421851578075726532760103492833979190212878590938685434376297845887543250784386533524486378271424054624253550807560554029945465003475712630029732489551653476632918157077142963809068078718047000843719660160468811559421739519267568115667296590825976051034102903062251018587365917626301512613470950424923733472260774856609357181056678392872499365155336928867225826363412381963879236312508317807296854540175269653092834957822860715012063 : Rat)/6339308190633452916515075691257471325350842047732173367547055088090958795206293269513017108784236724851294603599744931572117741667200097578126458781779776974659496206899802516305022991287849793505053068555189405341884861450623054248757068693774553183363417199544592975443825540598923612064384332636712079451164277199549454005529207175806819481407987170638543777783362754462934945878377387484380740623708815606162900290612700625286880317075972828663970778260551728417220868579615689188735269932038117052601674707763200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 3997, a6 := 3998 }
def label : String := "390.d4"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 3997, a6 := 3998 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 1, -2, 1, 1, 0, -1, 2, 1, 2, 0, -6, -1, 1, -1, 1, 2, 0, -1,                    8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (10138399158768979325205170260100366569574279835516587389262006440347674634291505862027326153523656045274389096725648114452205215405295986932177098420591133743660302608114006294354880232873514753767029905628324192172008803115657303884049833783554896045332923026128144910596448837011563211440991237885851903360919547103147813883380399620863362000023784555679389355278931173644082344436462464438562056132679048088772070948758943561392322388396941116125342843485197150567992312643927887490122324015208212155176068672404731 : Rat)/8875031466886834083121105967760459855491178866825042714565877123327342313288810577318223952297931414791812445039642904200964838334080136609377042294491687764523294689659723522827032187802989710907074295977265167478638806030872275948259896171284374456708784079362430165621355756838493056890138065691396911231629988079369235607740890046129547273971182038893961288896707856248108924229728342478133036873192341848628060406857780875401632443906361960129559089564772419784109216011461964864229377904853363873642344590868480,            reHi := (10582575286253393773714660338995222710768416211777785969171825679744171575011242532540421851578075726532760103492833979190212878590938685434376297845887543250784386533524486378271424054624253550807560554029945465003475712630029732489551653476632918157077142963809068078718047000843719660160468811559421739519267568115667296590825976051034102903062251018587365917626301512613470950424923733472260774856609357181056678392872499365155336928867225826363412381963879236312508317807296854540175269653092834957822860715012063 : Rat)/6339308190633452916515075691257471325350842047732173367547055088090958795206293269513017108784236724851294603599744931572117741667200097578126458781779776974659496206899802516305022991287849793505053068555189405341884861450623054248757068693774553183363417199544592975443825540598923612064384332636712079451164277199549454005529207175806819481407987170638543777783362754462934945878377387484380740623708815606162900290612700625286880317075972828663970778260551728417220868579615689188735269932038117052601674707763200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -46, a6 := -127 }
def label : String := "390.e1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -46, a6 := -127 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, -1, -1, 2, 1, 1, -1, 4, -1, -1, 2, 1, 1, 8, 1, -6, -1, -2, 4, 6, -1, 1, -1, -1, 2, -4,                    1, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (491581774854997624843253508814839225247148801665049408693497659796069114536361777172210369108928872411245415717292889680572048210238635748350795832649261308947640073106804640576531586818590504142278849210376718033120532007175944375679347989680523908490932614449346786540463989562875129093585489415343593485959767893526285603909665458405318536453213530531376790536747749558150825647830216782225616774359457609591169492342530620213609061298872805506221341145715254844399009684433602192170527149698461189005218359486922767 : Rat)/310511584805982588598488759117193379331152664482530365426391946063252757193323998456753087053623755241393541222257957867624724634101397295694527099116312404819418239367901165576070939061003956143542347787643283891849408032938195822370409141528226855991817652015370701859126530769904179661388507937060938384575028550673673320650186107872003450753198194818851303675399010996345127071598818072638164251376271418355548203783159649595503566085833554256661928662643618274124027602775214422314296234696901885721047965911482368,            reHi := (963564179817964753351281158134439571369158171859887586693517795028028692880300344363939996441641685826217035636467876979737476503858781638044111691713212997365364112348722348406305586786208829131067988209238856769231830481258448970178942834062097738442280352158188739233636153674764530996290038087248794397357735480370233236603108387734102819299618738151023427689225268736370025459972230707067307330201604509784270384978511238344645943497612232779618059518363029286865975525615698469630017944339601246325771149829066489 : Rat)/456634683538209689115424645760578499016400977180191713862341097151842289990182350671695716255329051825578737091555820393565771520737348964256657498700459418852085646129266419964810204501476406093444629099475417488013835342556170327015307561070921847046790664728486326263421368779270852443218394025089615271433865515696578412720861923341181545225291462968898975993233839700507539811174732459762006252023928556405217946739940661169858185420343462142149895092122968050182393533492962385756317992201326302530952891046297600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 4, a6 := -7 }
def label : String := "390.e2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 4, a6 := -7 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, -1, -1, 2, 1, 1, -1, 4, -1, -1, 2, 1, 1, 8, 1, -6, -1, -2, 4, 6, -1, 1, -1, -1, 2, -4,                    1, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (491581774854997624843253508814839225247148801665049408693497659796069114536361777172210369108928872411245415717292889680572048210238635748350795832649261308947640073106804640576531586818590504142278849210376718033120532007175944375679347989680523908490932614449346786540463989562875129093585489415343593485959767893526285603909665458405318536453213530531376790536747749558150825647830216782225616774359457609591169492342530620213609061298872805506221341145715254844399009684433602192170527149698461189005218359486922767 : Rat)/310511584805982588598488759117193379331152664482530365426391946063252757193323998456753087053623755241393541222257957867624724634101397295694527099116312404819418239367901165576070939061003956143542347787643283891849408032938195822370409141528226855991817652015370701859126530769904179661388507937060938384575028550673673320650186107872003450753198194818851303675399010996345127071598818072638164251376271418355548203783159649595503566085833554256661928662643618274124027602775214422314296234696901885721047965911482368,            reHi := (963564179817964753351281158134439571369158171859887586693517795028028692880300344363939996441641685826217035636467876979737476503858781638044111691713212997365364112348722348406305586786208829131067988209238856769231830481258448970178942834062097738442280352158188739233636153674764530996290038087248794397357735480370233236603108387734102819299618738151023427689225268736370025459972230707067307330201604509784270384978511238344645943497612232779618059518363029286865975525615698469630017944339601246325771149829066489 : Rat)/456634683538209689115424645760578499016400977180191713862341097151842289990182350671695716255329051825578737091555820393565771520737348964256657498700459418852085646129266419964810204501476406093444629099475417488013835342556170327015307561070921847046790664728486326263421368779270852443218394025089615271433865515696578412720861923341181545225291462968898975993233839700507539811174732459762006252023928556405217946739940661169858185420343462142149895092122968050182393533492962385756317992201326302530952891046297600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -9015, a6 := -333213 }
def label : String := "390.f1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -9015, a6 := -333213 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -845, a6 := 9095 }
def label : String := "390.f2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -845, a6 := 9095 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -565, a6 := -5353 }
def label : String := "390.f3"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 5, 5, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -565, a6 := -5353 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -115, a6 := -13093 }
def label : String := "390.f4"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 5, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -115, a6 := -13093 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -65, a6 := 47 }
def label : String := "390.f5"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -65, a6 := 47 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 15, a6 := 15 }
def label : String := "390.f6"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 15, a6 := 15 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 0, 1, 1, 1, 4, -1, 1, 0, -1, 1, -6, 1, 4, 1, 0, 4, 8, -1, 1, 1, -1, 0, 6, -1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/53327547341320744610480937769319066450311889136688610887006280660879144993835270722677781784377459963497723372693988505751887891135999434515954132309902840945300249038220655165965597801957391716588280232817723378937020245864492063812087104944752252700587758095700947659431335419130010909065846583177336006320628822264657193310777753809786374051617590258320194757501321279175864429595874718611858141014253557730218549375427161155196357155017955457502671637946789269622848288481491695483595635766231752008269824,   box := { reLo := (686081204959120470314794307419206731491538304024805009775142932672319082787466324941721700495431990478130537762065205315805659843067247605883563466963346255058391522255598943305775130672228886297743861476250596666433658075097180617063095737583410233711174634213722715824940927549999260650182824791670517458269608413916122649059649301809677364383379516143467751123017543191711530290634828476599308943601649095398024488147394466379354849375936727944941665046852962796616740238934218569962314243758616318215464030273049043 : Rat)/404447862562414296073661829102226670557383722645312660849502114620203171134161510594930491540434303045512595709663726634301111918367366225484468070277549770983275858000207400540260466844164816825622385773821084060812254160549750861070700982662816493098586017330945031833316069490211326449707720422222230668984280885331255165552763417816475082913829581486739093022578543734735249547040477321503491251792622435673193038541090299893302964229447066468761335653023200273018691415379480970241310221664031867955986846355292160,            reHi := (76434394886017274857689296491793491287425764604754792462888346174883599224379828980629350309659289988965609147548269304388263109556681362090585994424923259300791186668628823668391170357961277633159447106075884743020842657791322477261823775647768080285544557689303519872427798007340356319907079900111504603974835790442734588446706048977717383697330010725589392257076465327259188970580116448765077999517511214047220342307613089236568318993798699543136576187881873018063700570865358683770643938699480602985800514574808225009 : Rat)/34378068317805215166261255473689266997377616424851576172207679742717269546403728400569091780936915758868570635321416763915594513061226129166179785973591730533578447930017629045922139681754009430177902790774792145169041603646728823191009583526339401913379811473130327705831865906667962748225156235888889606863663875253156689071984890514400382047675514426372822906919176217452496211498440572327796756402372907032221408275992675490930751959503000649844713530506972023206588770307255882470511368841442708776258881940199833600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (14052002983044573431850044216739897356834756010525289128167027512669928269491640381311652782721261874260653064377628334274759985861150240332881091295449587599650898709861201632602441345494631975248437622189682611911858366837707648855726872397826374508309854466365978217234533265845842523343799264367128109080786331737743469841412718008159982701295928973038503770777211317791803861711740228230626484046487047047908053489596267486811304213310523266991066977868561550788256994932785766979328440761153737073587899 : Rat)/106655094682641489220961875538638132900623778273377221774012561321758289987670541445355563568754919926995446745387977011503775782271998869031908264619805681890600498076441310331931195603914783433176560465635446757874040491728984127624174209889504505401175516191401895318862670838260021818131693166354672012641257644529314386621555507619572748103235180516640389515002642558351728859191749437223716282028507115460437098750854322310392714310035910915005343275893578539245696576962983390967191271532463504016539648, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_f6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1196, a6 := -15210 }
def label : String := "390.g1"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 5, 5, 5, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1196, a6 := -15210 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 0, 1, 1, 2, -1, 1, 0, 1, 2, -1, 2, 0, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/43329497371777243235194212151376779412486046275227196142095356924870313149841110782132981749724434001720238917418381559464483482057224880357340735238015671188025250452308602565349575672991643164344437638773612040642512771802905085539901065209422044988450229953357400270998463830356026806178344913640647602263600941204009903948059235492695315338203024650055984741175591897528416272908288,   box := { reLo := (9933802685914882898564676874620429480562810904222257797116874765542393031582349191685206960473456532787328413547050315455401899089180423391908917604770167756146263415736872442662225337227837726201178338722560008444734315984205903663057579684135659115232140423289894708466212040217321327839875609972490148189850920657028306153518663729634319423522192119144380108460220418215861936162973358397 : Rat)/25846261829751984476009523519357005803444989033404398634740590882469766145445971787096234278619373504196131115434651692128361719464544927257555535273152537942013002021054342973243848636817880105747278773716653450303462080944291898049978684902746296945835504418327456048651938667126521770019413632711214497988249279432897927754537074267570219075814795218881645178034946444835187948871158333440,            reHi := (23282095384791610800195840906332976582961721919396223586077129532137073361888976062558937955895941141564517714853272765973315280603869455446799629242444280689511783560365377618452234086040963711023358078497319574303605352899124957830900183274103272478392261777851297445160411465368038508086226221473406139304764974330681422020400794483581213103174097711129584954244549465548160740473131773479 : Rat)/5169252365950396895201904703871401160688997806680879726948118176493953229089194357419246855723874700839226223086930338425672343892908985451511107054630507588402600404210868594648769727363576021149455754743330690060692416188858379609995736980549259389167100883665491209730387733425304354003882726542242899597649855886579585550907414853514043815162959043776329035606989288967037589774231666688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/86658994743554486470388424302753558824972092550454392284190713849740626299682221564265963499448868003440477834836763118928966964114449760714681470476031342376050500904617205130699151345983286328688875277547224081285025543605810171079802130418844089976900459906714800541996927660712053612356689827281295204527201882408019807896118470985390630676406049300111969482351183795056832545816576, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -206, a6 := 1116 }
def label : String := "390.g2"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -206, a6 := 1116 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 0, 1, 1, 2, -1, 1, 0, 1, 2, -1, 2, 0, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/43329497371777243235194212151376779412486046275227196142095356924870313149841110782132981749724434001720238917418381559464483482057224880357340735238015671188025250452308602565349575672991643164344437638773612040642512771802905085539901065209422044988450229953357400270998463830356026806178344913640647602263600941204009903948059235492695315338203024650055984741175591897528416272908288,   box := { reLo := (9933802685914882898564676874620429480562810904222257797116874765542393031582349191685206960473456532787328413547050315455401899089180423391908917604770167756146263415736872442662225337227837726201178338722560008444734315984205903663057579684135659115232140423289894708466212040217321327839875609972490148189850920657028306153518663729634319423522192119144380108460220418215861936162973358397 : Rat)/25846261829751984476009523519357005803444989033404398634740590882469766145445971787096234278619373504196131115434651692128361719464544927257555535273152537942013002021054342973243848636817880105747278773716653450303462080944291898049978684902746296945835504418327456048651938667126521770019413632711214497988249279432897927754537074267570219075814795218881645178034946444835187948871158333440,            reHi := (23282095384791610800195840906332976582961721919396223586077129532137073361888976062558937955895941141564517714853272765973315280603869455446799629242444280689511783560365377618452234086040963711023358078497319574303605352899124957830900183274103272478392261777851297445160411465368038508086226221473406139304764974330681422020400794483581213103174097711129584954244549465548160740473131773479 : Rat)/5169252365950396895201904703871401160688997806680879726948118176493953229089194357419246855723874700839226223086930338425672343892908985451511107054630507588402600404210868594648769727363576021149455754743330690060692416188858379609995736980549259389167100883665491209730387733425304354003882726542242899597649855886579585550907414853514043815162959043776329035606989288967037589774231666688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/86658994743554486470388424302753558824972092550454392284190713849740626299682221564265963499448868003440477834836763118928966964114449760714681470476031342376050500904617205130699151345983286328688875277547224081285025543605810171079802130418844089976900459906714800541996927660712053612356689827281295204527201882408019807896118470985390630676406049300111969482351183795056832545816576, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -6, a6 := 36 }
def label : String := "390.g3"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -6, a6 := 36 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 0, 1, 1, 2, -1, 1, 0, 1, 2, -1, 2, 0, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/43329497371777243235194212151376779412486046275227196142095356924870313149841110782132981749724434001720238917418381559464483482057224880357340735238015671188025250452308602565349575672991643164344437638773612040642512771802905085539901065209422044988450229953357400270998463830356026806178344913640647602263600941204009903948059235492695315338203024650055984741175591897528416272908288,   box := { reLo := (9933802685914882898564676874620429480562810904222257797116874765542393031582349191685206960473456532787328413547050315455401899089180423391908917604770167756146263415736872442662225337227837726201178338722560008444734315984205903663057579684135659115232140423289894708466212040217321327839875609972490148189850920657028306153518663729634319423522192119144380108460220418215861936162973358397 : Rat)/25846261829751984476009523519357005803444989033404398634740590882469766145445971787096234278619373504196131115434651692128361719464544927257555535273152537942013002021054342973243848636817880105747278773716653450303462080944291898049978684902746296945835504418327456048651938667126521770019413632711214497988249279432897927754537074267570219075814795218881645178034946444835187948871158333440,            reHi := (23282095384791610800195840906332976582961721919396223586077129532137073361888976062558937955895941141564517714853272765973315280603869455446799629242444280689511783560365377618452234086040963711023358078497319574303605352899124957830900183274103272478392261777851297445160411465368038508086226221473406139304764974330681422020400794483581213103174097711129584954244549465548160740473131773479 : Rat)/5169252365950396895201904703871401160688997806680879726948118176493953229089194357419246855723874700839226223086930338425672343892908985451511107054630507588402600404210868594648769727363576021149455754743330690060692416188858379609995736980549259389167100883665491209730387733425304354003882726542242899597649855886579585550907414853514043815162959043776329035606989288967037589774231666688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/86658994743554486470388424302753558824972092550454392284190713849740626299682221564265963499448868003440477834836763118928966964114449760714681470476031342376050500904617205130699151345983286328688875277547224081285025543605810171079802130418844089976900459906714800541996927660712053612356689827281295204527201882408019807896118470985390630676406049300111969482351183795056832545816576, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 54, a6 := -960 }
def label : String := "390.g4"
def inputConductor : Nat := 390
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 5, 5, 5, 5, 5, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 390 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 54, a6 := -960 },   conductor := 390,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 0, 1, 1, 2, -1, 1, 0, 1, 2, -1, 2, 0, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16963761597884739398956298828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4240940399471184825897216796875,   geometricUpper := (1638151313393339 : Rat)/2251799813685248,   tail := (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/43329497371777243235194212151376779412486046275227196142095356924870313149841110782132981749724434001720238917418381559464483482057224880357340735238015671188025250452308602565349575672991643164344437638773612040642512771802905085539901065209422044988450229953357400270998463830356026806178344913640647602263600941204009903948059235492695315338203024650055984741175591897528416272908288,   box := { reLo := (9933802685914882898564676874620429480562810904222257797116874765542393031582349191685206960473456532787328413547050315455401899089180423391908917604770167756146263415736872442662225337227837726201178338722560008444734315984205903663057579684135659115232140423289894708466212040217321327839875609972490148189850920657028306153518663729634319423522192119144380108460220418215861936162973358397 : Rat)/25846261829751984476009523519357005803444989033404398634740590882469766145445971787096234278619373504196131115434651692128361719464544927257555535273152537942013002021054342973243848636817880105747278773716653450303462080944291898049978684902746296945835504418327456048651938667126521770019413632711214497988249279432897927754537074267570219075814795218881645178034946444835187948871158333440,            reHi := (23282095384791610800195840906332976582961721919396223586077129532137073361888976062558937955895941141564517714853272765973315280603869455446799629242444280689511783560365377618452234086040963711023358078497319574303605352899124957830900183274103272478392261777851297445160411465368038508086226221473406139304764974330681422020400794483581213103174097711129584954244549465548160740473131773479 : Rat)/5169252365950396895201904703871401160688997806680879726948118176493953229089194357419246855723874700839226223086930338425672343892908985451511107054630507588402600404210868594648769727363576021149455754743330690060692416188858379609995736980549259389167100883665491209730387733425304354003882726542242899597649855886579585550907414853514043815162959043776329035606989288967037589774231666688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (89250445711304296443204242695420018794158192926852379950494809487169064809641378129409841110217135285656632876953445103794086917349158748508818682915144344994970617962602121491352253660288132636559155700402990584732323918445126866005148135280428147304824458700735679615102932379534127570334030530983647125421423739119801841175706385481518341001988171738215662378464949678615372460546875 : Rat)/86658994743554486470388424302753558824972092550454392284190713849740626299682221564265963499448868003440477834836763118928966964114449760714681470476031342376050500904617205130699151345983286328688875277547224081285025543605810171079802130418844089976900459906714800541996927660712053612356689827281295204527201882408019807896118470985390630676406049300111969482351183795056832545816576, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N390.C390_g4
