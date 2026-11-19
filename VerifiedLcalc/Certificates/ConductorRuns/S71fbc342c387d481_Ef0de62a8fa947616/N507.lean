module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -11749, a6 := -495058 }
def label : String := "507.a1"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -11749, a6 := -495058 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, -2, 1, 4, 3, 1, 2, -4, 1, 0, -4, 2, -1, 2, -1, 0, 2, -4, 4, 0, -3, -1, 0, -1, -4, -10,                    -2, -4, -5, 4, -2, -8, -1, 2, 0, 0, -6, -6, 4, -12, 4, -2, 0, 0, 1, 9, 1, -2, 0, 6, 1, 8, 12, 0, 10,                    -12, -2, -2, 4, 4, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((6958175612104011 : Rat)/4503599627370496, (699897837328111 : Rat)/281474976710656),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (66206653484559808139744871937028347073181722348229 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (178079166535083783312427555117772550887199512668129 : Rat)/45197638904609621651666519051328301226803157008384,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3299, a6 := 64670 }
def label : String := "507.a2"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3299, a6 := 64670 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, -2, 1, 4, 3, 1, 2, -4, 1, 0, -4, 2, -1, 2, -1, 0, 2, -4, 4, 0, -3, -1, 0, -1, -4, -10,                    -2, -4, -5, 4, -2, -8, -1, 2, 0, 0, -6, -6, 4, -12, 4, -2, 0, 0, 1, 9, 1, -2, 0, 6, 1, 8, 12, 0, 10,                    -12, -2, -2, 4, 4, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((6958175612104011 : Rat)/4503599627370496, (699897837328111 : Rat)/281474976710656),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (66206653484559808139744871937028347073181722348229 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (178079166535083783312427555117772550887199512668129 : Rat)/45197638904609621651666519051328301226803157008384,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -764, a6 := -7324 }
def label : String := "507.a3"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -764, a6 := -7324 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, -2, 1, 4, 3, 1, 2, -4, 1, 0, -4, 2, -1, 2, -1, 0, 2, -4, 4, 0, -3, -1, 0, -1, -4, -10,                    -2, -4, -5, 4, -2, -8, -1, 2, 0, 0, -6, -6, 4, -12, 4, -2, 0, 0, 1, 9, 1, -2, 0, 6, 1, 8, 12, 0, 10,                    -12, -2, -2, 4, 4, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((6958175612104011 : Rat)/4503599627370496, (699897837328111 : Rat)/281474976710656),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (66206653484559808139744871937028347073181722348229 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (178079166535083783312427555117772550887199512668129 : Rat)/45197638904609621651666519051328301226803157008384,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 81, a6 := -564 }
def label : String := "507.a4"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 81, a6 := -564 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, -2, 1, 4, 3, 1, 2, -4, 1, 0, -4, 2, -1, 2, -1, 0, 2, -4, 4, 0, -3, -1, 0, -1, -4, -10,                    -2, -4, -5, 4, -2, -8, -1, 2, 0, 0, -6, -6, 4, -12, 4, -2, 0, 0, 1, 9, 1, -2, 0, 6, 1, 8, 12, 0, 10,                    -12, -2, -2, 4, 4, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((6958175612104011 : Rat)/4503599627370496, (699897837328111 : Rat)/281474976710656),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (66206653484559808139744871937028347073181722348229 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (178079166535083783312427555117772550887199512668129 : Rat)/45197638904609621651666519051328301226803157008384,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -75, a6 := -1422 }
def label : String := "507.b1"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -75, a6 := -1422 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 1, 1, -2, 3, 1, -1, 2, 1, 0, 2, -1, -1, -7, -1, 6, -1, 2, -2, -6, -3, -4, 0, -1, 2,                    -1, 1, -4, -5, -2, 7, -2, -1, -1, -6, 0, 3, -9, -2, 6, -2, 1, 6, -6, 1, -3, 4, 7, 0, -9, 1, 2, -6,                    -6, 1, 0, 1, 1, 4, -2, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((7661195325299271 : Rat)/4503599627370496, (11549476754093091 : Rat)/4503599627370496),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (179093530716580053296133756670495949671218411951369 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (2905646114370211967020141292018317445901355532426349 : Rat)/723162222473753946426664304821252819628850512134144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -10, a6 := 8 }
def label : String := "507.b2"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -10, a6 := 8 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, -1, 1, 1, -2, 3, 1, -1, 2, 1, 0, 2, -1, -1, -7, -1, 6, -1, 2, -2, -6, -3, -4, 0, -1, 2,                    -1, 1, -4, -5, -2, 7, -2, -1, -1, -6, 0, 3, -9, -2, 6, -2, 1, 6, -6, 1, -3, 4, 7, 0, -9, 1, 2, -6,                    -6, 1, 0, 1, 1, 4, -2, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((7661195325299271 : Rat)/4503599627370496, (11549476754093091 : Rat)/4503599627370496),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (179093530716580053296133756670495949671218411951369 : Rat)/723162222473753946426664304821252819628850512134144,            reHi := (2905646114370211967020141292018317445901355532426349 : Rat)/723162222473753946426664304821252819628850512134144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -12678, a6 := -3060351 }
def label : String := "507.c1"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -12678, a6 := -3060351 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -1, -1, 2, -3, 1, -1, -2, 1, 0, 2, 1, -1, -7, 1, -6, 1, -2, -2, -6, 3, -4, 0, -1, -2,                    -1, 1, 4, 5, 2, -7, -2, -1, 1, -6, 0, 3, 9, -2, 6, 2, -1, -6, 6, 1, -3, -4, 7, 0, -9, -1, 2, -6, 6,                    -1, 0, -1, 1, 4, 2, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((5844021114288419 : Rat)/2251799813685248, (22690687346978399 : Rat)/4503599627370496),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (412850766277663200793278850913834266917410104690541 : Rat)/361581111236876973213332152410626409814425256067072,            reHi := (4694637872081860547481135301786113233688105710523761 : Rat)/723162222473753946426664304821252819628850512134144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1693, a6 := 26434 }
def label : String := "507.c2"
def inputConductor : Nat := 507
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 507 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1693, a6 := 26434 },   conductor := 507,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -1, -1, 2, -3, 1, -1, -2, 1, 0, 2, 1, -1, -7, 1, -6, 1, -2, -2, -6, 3, -4, 0, -1, -2,                    -1, 1, 4, 5, 2, -7, -2, -1, 1, -6, 0, 3, 9, -2, 6, 2, -1, -6, 6, 1, -3, -4, 7, 0, -9, -1, 2, -6, 6,                    -1, 0, -1, 1, 4, 2, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1208854005696791553497314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/19341664091148664760589599609375,   finite := ((5844021114288419 : Rat)/2251799813685248, (22690687346978399 : Rat)/4503599627370496),   tail := (125300564272723318670745609126949310302734375 : Rat)/86207654771060221961339033224732019857031168,   box := { reLo := (412850766277663200793278850913834266917410104690541 : Rat)/361581111236876973213332152410626409814425256067072,            reHi := (4694637872081860547481135301786113233688105710523761 : Rat)/723162222473753946426664304821252819628850512134144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N507.C507_c2
