module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -226, a6 := -1406 }
def label : String := "462.a1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 7, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -226, a6 := -1406 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 1, -1, 1, 2, 1, -1, 2, -1, 2, 1, -6, -1, -4, -2, -1, -1, -4, 1, -1, -2, -1, 1,                    2, -2, -4, -1, -1, 6, -2, 1, -2, 4, -2, 2, -6, 1, 0, 1, -2, 4, -8, -1, 1, 1, 6, 2, -14, 1, -2, -1, 4,                    -2, 12, 2, -14, 4, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((3032470983293653 : Rat)/2251799813685248, (13314501900012699 : Rat)/4503599627370496),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (45348505920492289104355415344983343617195035709691 : Rat)/184298262093143466571145694567769518158338542534656,            reHi := (1495411044141490973893789775440315661756532557960853 : Rat)/368596524186286933142291389135539036316677085069312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -126, a6 := 486 }
def label : String := "462.a2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 7, 7, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -126, a6 := 486 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 1, -1, 1, 2, 1, -1, 2, -1, 2, 1, -6, -1, -4, -2, -1, -1, -4, 1, -1, -2, -1, 1,                    2, -2, -4, -1, -1, 6, -2, 1, -2, 4, -2, 2, -6, 1, 0, 1, -2, 4, -8, -1, 1, 1, 6, 2, -14, 1, -2, -1, 4,                    -2, 12, 2, -14, 4, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((3032470983293653 : Rat)/2251799813685248, (13314501900012699 : Rat)/4503599627370496),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (45348505920492289104355415344983343617195035709691 : Rat)/184298262093143466571145694567769518158338542534656,            reHi := (1495411044141490973893789775440315661756532557960853 : Rat)/368596524186286933142291389135539036316677085069312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -16, a6 := -20 }
def label : String := "462.a3"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 7, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -16, a6 := -20 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 1, -1, 1, 2, 1, -1, 2, -1, 2, 1, -6, -1, -4, -2, -1, -1, -4, 1, -1, -2, -1, 1,                    2, -2, -4, -1, -1, 6, -2, 1, -2, 4, -2, 2, -6, 1, 0, 1, -2, 4, -8, -1, 1, 1, 6, 2, -14, 1, -2, -1, 4,                    -2, 12, 2, -14, 4, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((3032470983293653 : Rat)/2251799813685248, (13314501900012699 : Rat)/4503599627370496),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (45348505920492289104355415344983343617195035709691 : Rat)/184298262093143466571145694567769518158338542534656,            reHi := (1495411044141490973893789775440315661756532557960853 : Rat)/368596524186286933142291389135539036316677085069312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 4, a6 := 0 }
def label : String := "462.a4"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 4, a6 := 0 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 1, -1, 1, 2, 1, -1, 2, -1, 2, 1, -6, -1, -4, -2, -1, -1, -4, 1, -1, -2, -1, 1,                    2, -2, -4, -1, -1, 6, -2, 1, -2, 4, -2, 2, -6, 1, 0, 1, -2, 4, -8, -1, 1, 1, 6, 2, -14, 1, -2, -1, 4,                    -2, 12, 2, -14, 4, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((3032470983293653 : Rat)/2251799813685248, (13314501900012699 : Rat)/4503599627370496),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (45348505920492289104355415344983343617195035709691 : Rat)/184298262093143466571145694567769518158338542534656,            reHi := (1495411044141490973893789775440315661756532557960853 : Rat)/368596524186286933142291389135539036316677085069312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -105, a6 := -441 }
def label : String := "462.b1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -105, a6 := -441 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 0, 1, -1, -1, 1, 0, -1, -1, -2, 1, 0, 1, -4, -1, 6, 0, 1, 1, -4, 1, -5, 2, -1, -1, -10,                    0, 6, -1, 1, 4, 0, 1, -6, -6, 2, 0, -12, -1, -8, -1, 0, 4, 2, -1, 1, 5, 4, -2, 6, 1, 0, 1, -6, 10,                    -8, 0, 6, -6, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((13343279362557505 : Rat)/9007199254740992, (27335496497679975 : Rat)/9007199254740992),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (280704214360530448004210554363167420571803909382735 : Rat)/737193048372573866284582778271078072633354170138624,            reHi := (3048644890988584728874369143095018001315599375058825 : Rat)/737193048372573866284582778271078072633354170138624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 5, a6 := -23 }
def label : String := "462.b2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 5, a6 := -23 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 0, 1, -1, -1, 1, 0, -1, -1, -2, 1, 0, 1, -4, -1, 6, 0, 1, 1, -4, 1, -5, 2, -1, -1, -10,                    0, 6, -1, 1, 4, 0, 1, -6, -6, 2, 0, -12, -1, -8, -1, 0, 4, 2, -1, 1, 5, 4, -2, 6, 1, 0, 1, -6, 10,                    -8, 0, 6, -6, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((13343279362557505 : Rat)/9007199254740992, (27335496497679975 : Rat)/9007199254740992),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (280704214360530448004210554363167420571803909382735 : Rat)/737193048372573866284582778271078072633354170138624,            reHi := (3048644890988584728874369143095018001315599375058825 : Rat)/737193048372573866284582778271078072633354170138624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -92004, a6 := 10703088 }
def label : String := "462.c1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -92004, a6 := 10703088 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 2, 1, -1, -1, 1, -2, 1, -1, 2, 1, -2, 1, 6, -1, -8, 2, 1, -1, 4, 1, -1, -2, -1, -1, 2,                    2, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (203084998602503900205639477506560896225831560988044613783391375285261168084573314679761501815650997924621536110098372542006787245221732724398351152326439599530776290123559765709583695550017440311410428789420852394375698362094806448115753829917802398935320771623039787131744239946225035989781662467612182924277752957629649055088264212017839697304495061732135833223081406859213422369574323178547321050195236389221849469011904337995264950431236886519792092091737039928556862952007216922068669112431996244058932484051661898528943036239 : Rat)/627885801827276988420291026784131944852270037161922986407347003612781597459700104171565868887986494671363145646581114458682284557324881513718611978747340194850831423327478653788841967239380737275095760951571411874827970562873769065167804737212081458751885166254574978800003772844739702372965939940980218706862680846289314758897050393457829279048973207328320986490267106645652722264351865591705894875203806887793797697140280681276755873050139029694080496239242432143478825492225110143207640713114238212212707244949899637797840486400,            reHi := (3349315549162295717532119748941524014320403692669819646324596247328904887024416712267157597694481377902990109076271764323914393422441886423977288456666102122330593427400582991991979923268968005568203781117970709729771159689054864990261643865308526834053970678468447202101336476847112055510321081502480954946190012889786647647726326615211568132352965418402556065060070009998924253524852457415310029445236560819762313846268026935008456251517921639144642121836885835255559461444473918203137878033864299232492021553103772544751050499 : Rat)/1993288259769133296572352465981371253499269959244199956848720646389782849078413029116082123453925379909089351258987664948197728753412322265773371361102667285240734677230090964409022118220256308809827812544671148808977684326583393857675570594324068123021857670649444377142869120142030801184018856955492757799564066178696237329831906010977235806504676848661336465048467005224294356394767827275256809127631132977123167292508827559608748803333774697441525384886483911566599446007063841724468700676553137181627642047459998850151874560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -5764, a6 := 164560 }
def label : String := "462.c2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -5764, a6 := 164560 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 2, 1, -1, -1, 1, -2, 1, -1, 2, 1, -2, 1, 6, -1, -8, 2, 1, -1, 4, 1, -1, -2, -1, -1, 2,                    2, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (203084998602503900205639477506560896225831560988044613783391375285261168084573314679761501815650997924621536110098372542006787245221732724398351152326439599530776290123559765709583695550017440311410428789420852394375698362094806448115753829917802398935320771623039787131744239946225035989781662467612182924277752957629649055088264212017839697304495061732135833223081406859213422369574323178547321050195236389221849469011904337995264950431236886519792092091737039928556862952007216922068669112431996244058932484051661898528943036239 : Rat)/627885801827276988420291026784131944852270037161922986407347003612781597459700104171565868887986494671363145646581114458682284557324881513718611978747340194850831423327478653788841967239380737275095760951571411874827970562873769065167804737212081458751885166254574978800003772844739702372965939940980218706862680846289314758897050393457829279048973207328320986490267106645652722264351865591705894875203806887793797697140280681276755873050139029694080496239242432143478825492225110143207640713114238212212707244949899637797840486400,            reHi := (3349315549162295717532119748941524014320403692669819646324596247328904887024416712267157597694481377902990109076271764323914393422441886423977288456666102122330593427400582991991979923268968005568203781117970709729771159689054864990261643865308526834053970678468447202101336476847112055510321081502480954946190012889786647647726326615211568132352965418402556065060070009998924253524852457415310029445236560819762313846268026935008456251517921639144642121836885835255559461444473918203137878033864299232492021553103772544751050499 : Rat)/1993288259769133296572352465981371253499269959244199956848720646389782849078413029116082123453925379909089351258987664948197728753412322265773371361102667285240734677230090964409022118220256308809827812544671148808977684326583393857675570594324068123021857670649444377142869120142030801184018856955492757799564066178696237329831906010977235806504676848661336465048467005224294356394767827275256809127631132977123167292508827559608748803333774697441525384886483911566599446007063841724468700676553137181627642047459998850151874560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1444, a6 := 410800 }
def label : String := "462.c3"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1444, a6 := 410800 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 2, 1, -1, -1, 1, -2, 1, -1, 2, 1, -2, 1, 6, -1, -8, 2, 1, -1, 4, 1, -1, -2, -1, -1, 2,                    2, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (203084998602503900205639477506560896225831560988044613783391375285261168084573314679761501815650997924621536110098372542006787245221732724398351152326439599530776290123559765709583695550017440311410428789420852394375698362094806448115753829917802398935320771623039787131744239946225035989781662467612182924277752957629649055088264212017839697304495061732135833223081406859213422369574323178547321050195236389221849469011904337995264950431236886519792092091737039928556862952007216922068669112431996244058932484051661898528943036239 : Rat)/627885801827276988420291026784131944852270037161922986407347003612781597459700104171565868887986494671363145646581114458682284557324881513718611978747340194850831423327478653788841967239380737275095760951571411874827970562873769065167804737212081458751885166254574978800003772844739702372965939940980218706862680846289314758897050393457829279048973207328320986490267106645652722264351865591705894875203806887793797697140280681276755873050139029694080496239242432143478825492225110143207640713114238212212707244949899637797840486400,            reHi := (3349315549162295717532119748941524014320403692669819646324596247328904887024416712267157597694481377902990109076271764323914393422441886423977288456666102122330593427400582991991979923268968005568203781117970709729771159689054864990261643865308526834053970678468447202101336476847112055510321081502480954946190012889786647647726326615211568132352965418402556065060070009998924253524852457415310029445236560819762313846268026935008456251517921639144642121836885835255559461444473918203137878033864299232492021553103772544751050499 : Rat)/1993288259769133296572352465981371253499269959244199956848720646389782849078413029116082123453925379909089351258987664948197728753412322265773371361102667285240734677230090964409022118220256308809827812544671148808977684326583393857675570594324068123021857670649444377142869120142030801184018856955492757799564066178696237329831906010977235806504676848661336465048467005224294356394767827275256809127631132977123167292508827559608748803333774697441525384886483911566599446007063841724468700676553137181627642047459998850151874560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -644, a6 := -2352 }
def label : String := "462.c4"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -644, a6 := -2352 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -1, 1, 2, 1, -1, -1, 1, -2, 1, -1, 2, 1, -2, 1, 6, -1, -8, 2, 1, -1, 4, 1, -1, -2, -1, -1, 2,                    2, 8, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (203084998602503900205639477506560896225831560988044613783391375285261168084573314679761501815650997924621536110098372542006787245221732724398351152326439599530776290123559765709583695550017440311410428789420852394375698362094806448115753829917802398935320771623039787131744239946225035989781662467612182924277752957629649055088264212017839697304495061732135833223081406859213422369574323178547321050195236389221849469011904337995264950431236886519792092091737039928556862952007216922068669112431996244058932484051661898528943036239 : Rat)/627885801827276988420291026784131944852270037161922986407347003612781597459700104171565868887986494671363145646581114458682284557324881513718611978747340194850831423327478653788841967239380737275095760951571411874827970562873769065167804737212081458751885166254574978800003772844739702372965939940980218706862680846289314758897050393457829279048973207328320986490267106645652722264351865591705894875203806887793797697140280681276755873050139029694080496239242432143478825492225110143207640713114238212212707244949899637797840486400,            reHi := (3349315549162295717532119748941524014320403692669819646324596247328904887024416712267157597694481377902990109076271764323914393422441886423977288456666102122330593427400582991991979923268968005568203781117970709729771159689054864990261643865308526834053970678468447202101336476847112055510321081502480954946190012889786647647726326615211568132352965418402556065060070009998924253524852457415310029445236560819762313846268026935008456251517921639144642121836885835255559461444473918203137878033864299232492021553103772544751050499 : Rat)/1993288259769133296572352465981371253499269959244199956848720646389782849078413029116082123453925379909089351258987664948197728753412322265773371361102667285240734677230090964409022118220256308809827812544671148808977684326583393857675570594324068123021857670649444377142869120142030801184018856955492757799564066178696237329831906010977235806504676848661336465048467005224294356394767827275256809127631132977123167292508827559608748803333774697441525384886483911566599446007063841724468700676553137181627642047459998850151874560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -452236, a6 := 115355594 }
def label : String := "462.d1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -452236, a6 := 115355594 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 0, -1, -1, -1, 1, 0, -1, 1, 6, 1, 0, 1, 4, -1, 6, 0, -1, 1, -4, -1, -5, -6, 1, -1, 6, 0,                    -2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (25672386822063107411497531198543659717127177957412022355496246935091173196260907686230922589159490219850584443038336159790915673808767269104593516767149529116135155080626170920583749289250285355573893676972668302294080517866813546591305430676768818505995100403718754550281260345796319771297381439117637292725921385886481276322629562288522793662151700893414613452855504903850188717291171183696465773384693163376007987150712830449446746871527372390753905774660013147146818881484158116267963880247025857625304033356629234217112990913 : Rat)/41859053455151799228019401785608796323484669144128199093823133574185439830646673611437724592532432978090876376438740963912152303821658767581240798583156012990055428221831910252589464482625382485006384063438094124988531370858251271011186982480805430583459011083638331920000251522982646824864395996065347913790845389752620983926470026230521951936598213821888065766017807109710181484290124372780392991680253792519586513142685378751783724870009268646272033082616162142898588366148340676213842714207615880814180482996659975853189365760,            reHi := (49481408068582631373390762474494609886747170736824429075503249145979873709212063983737398712529427994033926817993128148691771768175712355970924071792051365532252931971172487189445960635980194518697446936308528559268818120175355709259778417568958793232911200886162291656465629051078455172233193932528262585577374323736334258282345637276737496872560536911972327006882191503332801018589868142016324288719994175673050753657287785815532154033403721676898906434893209144754834647940980813552244492875056435832392302236044060312497823833 : Rat)/25115432073091079536811641071365277794090801486476919456293880144511263898388004166862634755519459786854525825863244578347291382292995260548744479149893607794033256933099146151553678689575229491003830438062856474993118822514950762606712189488483258350075406650182999152000150913789588094918637597639208748274507233851572590355882015738313171161958928293132839459610684265826108890574074623668235795008152275511751907885611227251070234922005561187763219849569697285739153019689004405728305628524569528488508289797995985511913619456,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1676, a6 := 5058506 }
def label : String := "462.d2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 7, 7, 7, 7,              11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1676, a6 := 5058506 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 0, -1, -1, -1, 1, 0, -1, 1, 6, 1, 0, 1, 4, -1, 6, 0, -1, 1, -4, -1, -5, -6, 1, -1, 6, 0,                    -2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (25672386822063107411497531198543659717127177957412022355496246935091173196260907686230922589159490219850584443038336159790915673808767269104593516767149529116135155080626170920583749289250285355573893676972668302294080517866813546591305430676768818505995100403718754550281260345796319771297381439117637292725921385886481276322629562288522793662151700893414613452855504903850188717291171183696465773384693163376007987150712830449446746871527372390753905774660013147146818881484158116267963880247025857625304033356629234217112990913 : Rat)/41859053455151799228019401785608796323484669144128199093823133574185439830646673611437724592532432978090876376438740963912152303821658767581240798583156012990055428221831910252589464482625382485006384063438094124988531370858251271011186982480805430583459011083638331920000251522982646824864395996065347913790845389752620983926470026230521951936598213821888065766017807109710181484290124372780392991680253792519586513142685378751783724870009268646272033082616162142898588366148340676213842714207615880814180482996659975853189365760,            reHi := (49481408068582631373390762474494609886747170736824429075503249145979873709212063983737398712529427994033926817993128148691771768175712355970924071792051365532252931971172487189445960635980194518697446936308528559268818120175355709259778417568958793232911200886162291656465629051078455172233193932528262585577374323736334258282345637276737496872560536911972327006882191503332801018589868142016324288719994175673050753657287785815532154033403721676898906434893209144754834647940980813552244492875056435832392302236044060312497823833 : Rat)/25115432073091079536811641071365277794090801486476919456293880144511263898388004166862634755519459786854525825863244578347291382292995260548744479149893607794033256933099146151553678689575229491003830438062856474993118822514950762606712189488483258350075406650182999152000150913789588094918637597639208748274507233851572590355882015738313171161958928293132839459610684265826108890574074623668235795008152275511751907885611227251070234922005561187763219849569697285739153019689004405728305628524569528488508289797995985511913619456,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -7445, a6 := 244091 }
def label : String := "462.e1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -7445, a6 := 244091 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, 1, 1, 1, -4, -1, -1, -6, 1, 4, 1, -4, 1, -2, -4, -1, -1, -8, -1, 11, -6, -1, 1,                    -6, 4, 6, 1, 1, -4, -4, 1, -6, -2, 6, -4, 12, -1, 4, -1, -4, -8, 6, -1, 1, 11, 4, -6, 2, -1, 4, 1, 2,                    -6, 0, 4, 10, 6, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((21813233904449863 : Rat)/9007199254740992, (43691597238313025 : Rat)/9007199254740992),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (973926539272260728227196407216656525370641311611561 : Rat)/737193048372573866284582778271078072633354170138624,            reHi := (4387307823101427799096297588071372902088483364612175 : Rat)/737193048372573866284582778271078072633354170138624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -405, a6 := 4731 }
def label : String := "462.e2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -405, a6 := 4731 },   conductor := 462,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, 1, 1, 1, -4, -1, -1, -6, 1, 4, 1, -4, 1, -2, -4, -1, -1, -8, -1, 11, -6, -1, 1,                    -6, 4, 6, 1, 1, -4, -4, 1, -6, -2, 6, -4, 12, -1, 4, -1, -4, -8, 6, -1, 1, 11, 4, -6, 2, -1, 4, 1, 2,                    -6, 0, 4, 10, 6, 1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   finite := ((21813233904449863 : Rat)/9007199254740992, (43691597238313025 : Rat)/9007199254740992),   tail := (773787255255420801734129375983142852783203125 : Rat)/703042076466153970989783075591161797173837824,   box := { reLo := (973926539272260728227196407216656525370641311611561 : Rat)/737193048372573866284582778271078072633354170138624,            reHi := (4387307823101427799096297588071372902088483364612175 : Rat)/737193048372573866284582778271078072633354170138624,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14133, a6 := -647829 }
def label : String := "462.f1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14133, a6 := -647829 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, -1, 0, 1, -5, 2, 1, 1, -6, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (16048394145177261245220357827935632783852332518431017248141376831225211189101478443918874524678957001929379139617331519146763505177802793098519727848128145866224421355816487041310193755328430479653189460671567010229600092735167577116494562416880674885360747895427332801843900699243486579516888676207054683830015633720740532306977149249705797481811747713470631700472490674012407753469760262290761877225090706158097565038192633107030778340148276957921889275566263768225122481228413472181124770310265731418276017982510037907638931 : Rat)/8235107899892150153063033992840605218076857986253826302148954077156293494126829354994633994202721420045421282006441267737979992882482543297509501983701753490075826917535296134682168892902888547119099756725967760178739203395288465672080854314539726654231558348148402895927651293130562035188746015358124712530168284429002751116755858003250433196261698568146383192212828469350812804306536370800785558072054651292462426351108671798501618113320729617602209931657714370037101783621550398625583850916312390480853921502392283268382720,            reHi := (212333423118430619545233057715778991972956645190586424923915578953006525770609102630536299340377094046201051776775632382767116746046503169270561404488069963908032027080344064935462022840269027994497719024787556407980847230547782854384603681026787989922745269484141305189671626920063196678549991765405863458257923223247637317987872498248498008366471000779410910944697586803393493895484462905728058331340103510021223772606526401406722144948926957314202976909830654872210378836611447482338112238198993008700501785204585361011951391 : Rat)/64233841619158771193891665144156720700999492292779845156761841801819089254189268968958145154781227076354285999650241888356243944483363837720574115472873677222591449956775309850520917364642530667528978102462548529394165786483250032242230663653409867903006155115557542588235680086418383874472218919793372757735312618546221458710695692425353378930841248831541788899260062060936339873590983692246127352962026280081206925538647640028312621283901691017297237466930172086289393912248093109279554037147236645750660587718659809493385216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -823, a6 := -11611 }
def label : String := "462.f2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 7, 7, 7, 11, 11, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -823, a6 := -11611 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, -1, 0, 1, -5, 2, 1, 1, -6, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (16048394145177261245220357827935632783852332518431017248141376831225211189101478443918874524678957001929379139617331519146763505177802793098519727848128145866224421355816487041310193755328430479653189460671567010229600092735167577116494562416880674885360747895427332801843900699243486579516888676207054683830015633720740532306977149249705797481811747713470631700472490674012407753469760262290761877225090706158097565038192633107030778340148276957921889275566263768225122481228413472181124770310265731418276017982510037907638931 : Rat)/8235107899892150153063033992840605218076857986253826302148954077156293494126829354994633994202721420045421282006441267737979992882482543297509501983701753490075826917535296134682168892902888547119099756725967760178739203395288465672080854314539726654231558348148402895927651293130562035188746015358124712530168284429002751116755858003250433196261698568146383192212828469350812804306536370800785558072054651292462426351108671798501618113320729617602209931657714370037101783621550398625583850916312390480853921502392283268382720,            reHi := (212333423118430619545233057715778991972956645190586424923915578953006525770609102630536299340377094046201051776775632382767116746046503169270561404488069963908032027080344064935462022840269027994497719024787556407980847230547782854384603681026787989922745269484141305189671626920063196678549991765405863458257923223247637317987872498248498008366471000779410910944697586803393493895484462905728058331340103510021223772606526401406722144948926957314202976909830654872210378836611447482338112238198993008700501785204585361011951391 : Rat)/64233841619158771193891665144156720700999492292779845156761841801819089254189268968958145154781227076354285999650241888356243944483363837720574115472873677222591449956775309850520917364642530667528978102462548529394165786483250032242230663653409867903006155115557542588235680086418383874472218919793372757735312618546221458710695692425353378930841248831541788899260062060936339873590983692246127352962026280081206925538647640028312621283901691017297237466930172086289393912248093109279554037147236645750660587718659809493385216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -363, a6 := 1305 }
def label : String := "462.f3"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -363, a6 := 1305 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, -1, 0, 1, -5, 2, 1, 1, -6, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (16048394145177261245220357827935632783852332518431017248141376831225211189101478443918874524678957001929379139617331519146763505177802793098519727848128145866224421355816487041310193755328430479653189460671567010229600092735167577116494562416880674885360747895427332801843900699243486579516888676207054683830015633720740532306977149249705797481811747713470631700472490674012407753469760262290761877225090706158097565038192633107030778340148276957921889275566263768225122481228413472181124770310265731418276017982510037907638931 : Rat)/8235107899892150153063033992840605218076857986253826302148954077156293494126829354994633994202721420045421282006441267737979992882482543297509501983701753490075826917535296134682168892902888547119099756725967760178739203395288465672080854314539726654231558348148402895927651293130562035188746015358124712530168284429002751116755858003250433196261698568146383192212828469350812804306536370800785558072054651292462426351108671798501618113320729617602209931657714370037101783621550398625583850916312390480853921502392283268382720,            reHi := (212333423118430619545233057715778991972956645190586424923915578953006525770609102630536299340377094046201051776775632382767116746046503169270561404488069963908032027080344064935462022840269027994497719024787556407980847230547782854384603681026787989922745269484141305189671626920063196678549991765405863458257923223247637317987872498248498008366471000779410910944697586803393493895484462905728058331340103510021223772606526401406722144948926957314202976909830654872210378836611447482338112238198993008700501785204585361011951391 : Rat)/64233841619158771193891665144156720700999492292779845156761841801819089254189268968958145154781227076354285999650241888356243944483363837720574115472873677222591449956775309850520917364642530667528978102462548529394165786483250032242230663653409867903006155115557542588235680086418383874472218919793372757735312618546221458710695692425353378930841248831541788899260062060936339873590983692246127352962026280081206925538647640028312621283901691017297237466930172086289393912248093109279554037147236645750660587718659809493385216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 77, a6 := 161 }
def label : String := "462.f4"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 77, a6 := 161 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, -1, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, -1, 0, 1, -5, 2, 1, 1, -6, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (16048394145177261245220357827935632783852332518431017248141376831225211189101478443918874524678957001929379139617331519146763505177802793098519727848128145866224421355816487041310193755328430479653189460671567010229600092735167577116494562416880674885360747895427332801843900699243486579516888676207054683830015633720740532306977149249705797481811747713470631700472490674012407753469760262290761877225090706158097565038192633107030778340148276957921889275566263768225122481228413472181124770310265731418276017982510037907638931 : Rat)/8235107899892150153063033992840605218076857986253826302148954077156293494126829354994633994202721420045421282006441267737979992882482543297509501983701753490075826917535296134682168892902888547119099756725967760178739203395288465672080854314539726654231558348148402895927651293130562035188746015358124712530168284429002751116755858003250433196261698568146383192212828469350812804306536370800785558072054651292462426351108671798501618113320729617602209931657714370037101783621550398625583850916312390480853921502392283268382720,            reHi := (212333423118430619545233057715778991972956645190586424923915578953006525770609102630536299340377094046201051776775632382767116746046503169270561404488069963908032027080344064935462022840269027994497719024787556407980847230547782854384603681026787989922745269484141305189671626920063196678549991765405863458257923223247637317987872498248498008366471000779410910944697586803393493895484462905728058331340103510021223772606526401406722144948926957314202976909830654872210378836611447482338112238198993008700501785204585361011951391 : Rat)/64233841619158771193891665144156720700999492292779845156761841801819089254189268968958145154781227076354285999650241888356243944483363837720574115472873677222591449956775309850520917364642530667528978102462548529394165786483250032242230663653409867903006155115557542588235680086418383874472218919793372757735312618546221458710695692425353378930841248831541788899260062060936339873590983692246127352962026280081206925538647640028312621283901691017297237466930172086289393912248093109279554037147236645750660587718659809493385216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_f4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -40247, a6 := 3104415 }
def label : String := "462.g1"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -40247, a6 := 3104415 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 2, 1, -1, 1, 1, 2, 1, 1, -2, -1, 2, 1, -2, 1, 0, 2, -1, 1, 0, 1, -1, -2, 1, -1, -2, 2, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (995920473754503545782751928154825081849611603776873258865181736691683121972908386068226509913328562547541907402005604212603015841594352960419499954445543686805810604506300054233975437924635837786069068647119303429861937306032027018348827700167796973631474615716045141984831563481311005267750605752249022930229664887182229195365851847674423773668842494954312775234006308740199078113598146987036708492155256272354311669359778584610393977684489616366451754327782625554822091222335924250667571534136449542304953053790389020151330769 : Rat)/478936538388464522059718555899414145577627793411077792835504960803037069000534023014161608610210903639483711400900926360550941691323326860197263141683707242449146775993500117306515611929352202345610801641168124999868779986936513398297333895661389365943466946037051852631581825205751107835977070893196200386622944962844633683369222268083775193782588258831671233020798708349086744671511720512361475877348441562008999006209214859860225685011547696181602209183251283099526182679042799499014218698027641656912820171586498579555942400,            reHi := (75958498168483480570144648411338335081843260380872434376770477534804534139181285784075464731737866206473479142796422679804300654486204695801604657760725626154819130007853377511148622641000572926017606358390684048627626217401629424324020685231219641003546672258899639211366412077930326735748413099505728380293190583094994352342361172097254846160985527005530720608705672319971986685198275194182016579364581349928641608742742779206062165183793887809362418111961011969162059079637385595160521912469889911326641214514300896735331661 : Rat)/22104763310236824095063933349203729795890513542049744284715613575524787800024647216038228089702041706437709756964658139717735770368768932009104452693094180420729851199700005414146874396739332415951267768053913461532405230166300618382953872107448739966621551355556239352226853471034666515506634041224440017844135921362060016155502566219251162789965611946077133831729171154573234369454387100570529655877620379785030723363502224301241185462071432131458563500765443835362746892878898438416040862985891153395976315611684549825658880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3507, a6 := 6507 }
def label : String := "462.g2"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3507, a6 := 6507 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 2, 1, -1, 1, 1, 2, 1, 1, -2, -1, 2, 1, -2, 1, 0, 2, -1, 1, 0, 1, -1, -2, 1, -1, -2, 2, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (995920473754503545782751928154825081849611603776873258865181736691683121972908386068226509913328562547541907402005604212603015841594352960419499954445543686805810604506300054233975437924635837786069068647119303429861937306032027018348827700167796973631474615716045141984831563481311005267750605752249022930229664887182229195365851847674423773668842494954312775234006308740199078113598146987036708492155256272354311669359778584610393977684489616366451754327782625554822091222335924250667571534136449542304953053790389020151330769 : Rat)/478936538388464522059718555899414145577627793411077792835504960803037069000534023014161608610210903639483711400900926360550941691323326860197263141683707242449146775993500117306515611929352202345610801641168124999868779986936513398297333895661389365943466946037051852631581825205751107835977070893196200386622944962844633683369222268083775193782588258831671233020798708349086744671511720512361475877348441562008999006209214859860225685011547696181602209183251283099526182679042799499014218698027641656912820171586498579555942400,            reHi := (75958498168483480570144648411338335081843260380872434376770477534804534139181285784075464731737866206473479142796422679804300654486204695801604657760725626154819130007853377511148622641000572926017606358390684048627626217401629424324020685231219641003546672258899639211366412077930326735748413099505728380293190583094994352342361172097254846160985527005530720608705672319971986685198275194182016579364581349928641608742742779206062165183793887809362418111961011969162059079637385595160521912469889911326641214514300896735331661 : Rat)/22104763310236824095063933349203729795890513542049744284715613575524787800024647216038228089702041706437709756964658139717735770368768932009104452693094180420729851199700005414146874396739332415951267768053913461532405230166300618382953872107448739966621551355556239352226853471034666515506634041224440017844135921362060016155502566219251162789965611946077133831729171154573234369454387100570529655877620379785030723363502224301241185462071432131458563500765443835362746892878898438416040862985891153395976315611684549825658880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2517, a6 := 48285 }
def label : String := "462.g3"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2517, a6 := 48285 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 2, 1, -1, 1, 1, 2, 1, 1, -2, -1, 2, 1, -2, 1, 0, 2, -1, 1, 0, 1, -1, -2, 1, -1, -2, 2, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (995920473754503545782751928154825081849611603776873258865181736691683121972908386068226509913328562547541907402005604212603015841594352960419499954445543686805810604506300054233975437924635837786069068647119303429861937306032027018348827700167796973631474615716045141984831563481311005267750605752249022930229664887182229195365851847674423773668842494954312775234006308740199078113598146987036708492155256272354311669359778584610393977684489616366451754327782625554822091222335924250667571534136449542304953053790389020151330769 : Rat)/478936538388464522059718555899414145577627793411077792835504960803037069000534023014161608610210903639483711400900926360550941691323326860197263141683707242449146775993500117306515611929352202345610801641168124999868779986936513398297333895661389365943466946037051852631581825205751107835977070893196200386622944962844633683369222268083775193782588258831671233020798708349086744671511720512361475877348441562008999006209214859860225685011547696181602209183251283099526182679042799499014218698027641656912820171586498579555942400,            reHi := (75958498168483480570144648411338335081843260380872434376770477534804534139181285784075464731737866206473479142796422679804300654486204695801604657760725626154819130007853377511148622641000572926017606358390684048627626217401629424324020685231219641003546672258899639211366412077930326735748413099505728380293190583094994352342361172097254846160985527005530720608705672319971986685198275194182016579364581349928641608742742779206062165183793887809362418111961011969162059079637385595160521912469889911326641214514300896735331661 : Rat)/22104763310236824095063933349203729795890513542049744284715613575524787800024647216038228089702041706437709756964658139717735770368768932009104452693094180420729851199700005414146874396739332415951267768053913461532405230166300618382953872107448739966621551355556239352226853471034666515506634041224440017844135921362060016155502566219251162789965611946077133831729171154573234369454387100570529655877620379785030723363502224301241185462071432131458563500765443835362746892878898438416040862985891153395976315611684549825658880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -97, a6 := 1337 }
def label : String := "462.g4"
def inputConductor : Nat := 462
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 7, 7, 7, 11, 11, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 462 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -97, a6 := 1337 },   conductor := 462,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 2, 1, -1, 1, 1, 2, 1, 1, -2, -1, 2, 1, -2, 1, 0, 2, -1, 1, 0, 1, -1, -2, 1, -1, -2, 2, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/18463364549348867702484130859375,   alphaHi := (2698607540904403791726115815424 : Rat)/9231682274674433803558349609375,   geometricUpper := (3362069672298951 : Rat)/4503599627370496,   tail := (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/139140244515156671012533761221414091031618179609096667278283585681706769605897464445058342999148888840657974899943107300356935972291306404980150210083839617077476901164079108255050760904737465518366647679399526222755783911446943540671222572468176654840856453131825128532857598087823496368398429169599170889271384961696430227095629625911112651961614329553387347970371347003549133127194505135674078479511122351881362258092541019831434150707282407278894474391015364447406340430939660788226065398037048168350459887582445568,   box := { reLo := (995920473754503545782751928154825081849611603776873258865181736691683121972908386068226509913328562547541907402005604212603015841594352960419499954445543686805810604506300054233975437924635837786069068647119303429861937306032027018348827700167796973631474615716045141984831563481311005267750605752249022930229664887182229195365851847674423773668842494954312775234006308740199078113598146987036708492155256272354311669359778584610393977684489616366451754327782625554822091222335924250667571534136449542304953053790389020151330769 : Rat)/478936538388464522059718555899414145577627793411077792835504960803037069000534023014161608610210903639483711400900926360550941691323326860197263141683707242449146775993500117306515611929352202345610801641168124999868779986936513398297333895661389365943466946037051852631581825205751107835977070893196200386622944962844633683369222268083775193782588258831671233020798708349086744671511720512361475877348441562008999006209214859860225685011547696181602209183251283099526182679042799499014218698027641656912820171586498579555942400,            reHi := (75958498168483480570144648411338335081843260380872434376770477534804534139181285784075464731737866206473479142796422679804300654486204695801604657760725626154819130007853377511148622641000572926017606358390684048627626217401629424324020685231219641003546672258899639211366412077930326735748413099505728380293190583094994352342361172097254846160985527005530720608705672319971986685198275194182016579364581349928641608742742779206062165183793887809362418111961011969162059079637385595160521912469889911326641214514300896735331661 : Rat)/22104763310236824095063933349203729795890513542049744284715613575524787800024647216038228089702041706437709756964658139717735770368768932009104452693094180420729851199700005414146874396739332415951267768053913461532405230166300618382953872107448739966621551355556239352226853471034666515506634041224440017844135921362060016155502566219251162789965611946077133831729171154573234369454387100570529655877620379785030723363502224301241185462071432131458563500765443835362746892878898438416040862985891153395976315611684549825658880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (94396502835229265674066314190477575114041416411661089415401561457778349402967880643005699067819347494336851111353746111498451345597550822598481830983848025220442561472577476499227079462879749832845984323211585231194986311801940258754819736964952957329297149220908244236960297898022120280727597274106369645020653977442546231067478567672533475660818881116646987423145155698715519145368651890693809320353156797165782957851235926992623626433998146142968639478693708661297417060429787557574436841981009395013518829441147757 : Rat)/278280489030313342025067522442828182063236359218193334556567171363413539211794928890116685998297777681315949799886214600713871944582612809960300420167679234154953802328158216510101521809474931036733295358799052445511567822893887081342445144936353309681712906263650257065715196175646992736796858339198341778542769923392860454191259251822225303923228659106774695940742694007098266254389010271348156959022244703762724516185082039662868301414564814557788948782030728894812680861879321576452130796074096336700919775164891136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N462.C462_g4
