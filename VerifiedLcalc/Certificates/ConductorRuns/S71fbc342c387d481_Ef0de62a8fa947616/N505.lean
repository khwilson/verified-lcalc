module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -10, a6 := 15 }
def label : String := "505.a1"
def inputConductor : Nat := 505
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 101] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 505 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -10, a6 := 15 },   conductor := 505,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, -3, -1, -2, 0, 2, 0, 0, -1, -6, -3, 0, 1, 0, -2, -6, 0, 1, 2, 0, 0, -6, 0,                    8, 5, 0, -6, 0, 3, 2, 0, 0, 3, 2, 0, -6, 2, 3, -6, 6, 0, -7, 1, 0, -2, 6, 0, 2, 0, 0, -6, -6, 0, 2,                    8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/19303477155396976375579833984375,   alphaHi := (2698607540904403791726115815424 : Rat)/9651738577698488140106201171875,   finite := ((12427645172080491 : Rat)/4503599627370496, (24819366177014483 : Rat)/4503599627370496),   tail := (1983256507531376647922835020637989044189453125 : Rat)/1380552313292024650323267098225069358174961664,   box := { reLo := (957541752465740363410207431574328758898591053742397 : Rat)/723807011231249019868685060394225163658834300895232,            reHi := (5028702628148905680821404207161564669152528006963861 : Rat)/723807011231249019868685060394225163658834300895232,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := 26 }
def label : String := "505.a2"
def inputConductor : Nat := 505
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 101, 101] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 505 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := 26 },   conductor := 505,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, -3, -1, -2, 0, 2, 0, 0, -1, -6, -3, 0, 1, 0, -2, -6, 0, 1, 2, 0, 0, -6, 0,                    8, 5, 0, -6, 0, 3, 2, 0, 0, 3, 2, 0, -6, 2, 3, -6, 6, 0, -7, 1, 0, -2, 6, 0, 2, 0, 0, -6, -6, 0, 2,                    8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/19303477155396976375579833984375,   alphaHi := (2698607540904403791726115815424 : Rat)/9651738577698488140106201171875,   finite := ((12427645172080491 : Rat)/4503599627370496, (24819366177014483 : Rat)/4503599627370496),   tail := (1983256507531376647922835020637989044189453125 : Rat)/1380552313292024650323267098225069358174961664,   box := { reLo := (957541752465740363410207431574328758898591053742397 : Rat)/723807011231249019868685060394225163658834300895232,            reHi := (5028702628148905680821404207161564669152528006963861 : Rat)/723807011231249019868685060394225163658834300895232,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N505.C505_a2
