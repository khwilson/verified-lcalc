module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2, a6 := -12 }
def label : String := "402.a1"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2, a6 := -12 },   conductor := 402,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 1, 1, -3, -1, 1, -1, 0, -1, -4, 3, -1, 1, 2, -1, -2, 1, 3, 0, -3, 1, -4, 4, -1, -3, 0,                    1, -9, -1, 0, -2, -3, 1, -3, 2, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   finite := ((6606034955250307 : Rat)/9007199254740992, (7669675345678535 : Rat)/2251799813685248),   tail := (1030688931401312400379761383772945404052734375 : Rat)/1438432489618280277221414968049230779198210048,   box := { reLo := (25461745960450889485909499233123579598213692564633 : Rat)/1508305786233977859967722421537190213528542299291648,            reHi := (1554518861899296999075753338060522368502539498736165 : Rat)/377076446558494464991930605384297553382135574822912,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -10255, a6 := -438718 }
def label : String := "402.b1"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,              3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -10255, a6 := -438718 },   conductor := 402,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, -1, -1, 1, 3, 0, 1, -4, 1, -3, 1, -6, -1, 2, -3, -1, 0, -9, -1, 4, 4, 1, -1, 0,                    3, 5, -1, 0, 6, 3, 1, -7, -2, -4, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   finite := ((8492210186593723 : Rat)/9007199254740992, (34089751042529621 : Rat)/9007199254740992),   tail := (1030688931401312400379761383772945404052734375 : Rat)/1438432489618280277221414968049230779198210048,   box := { reLo := (341312315579973975554781600278032784768805109023937 : Rat)/1508305786233977859967722421537190213528542299291648,            reHi := (6789274750901495432041045315711855233567191120569199 : Rat)/1508305786233977859967722421537190213528542299291648,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -145, a6 := 692 }
def label : String := "402.b2"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -145, a6 := 692 },   conductor := 402,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, -1, -1, 1, 3, 0, 1, -4, 1, -3, 1, -6, -1, 2, -3, -1, 0, -9, -1, 4, 4, 1, -1, 0,                    3, 5, -1, 0, 6, 3, 1, -7, -2, -4, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   finite := ((8492210186593723 : Rat)/9007199254740992, (34089751042529621 : Rat)/9007199254740992),   tail := (1030688931401312400379761383772945404052734375 : Rat)/1438432489618280277221414968049230779198210048,   box := { reLo := (341312315579973975554781600278032784768805109023937 : Rat)/1508305786233977859967722421537190213528542299291648,            reHi := (6789274750901495432041045315711855233567191120569199 : Rat)/1508305786233977859967722421537190213528542299291648,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 800, a6 := 1070 }
def label : String := "402.b3"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 67, 67, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 800, a6 := 1070 },   conductor := 402,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, -1, -1, 1, 3, 0, 1, -4, 1, -3, 1, -6, -1, 2, -3, -1, 0, -9, -1, 4, 4, 1, -1, 0,                    3, 5, -1, 0, 6, 3, 1, -7, -2, -4, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   finite := ((8492210186593723 : Rat)/9007199254740992, (34089751042529621 : Rat)/9007199254740992),   tail := (1030688931401312400379761383772945404052734375 : Rat)/1438432489618280277221414968049230779198210048,   box := { reLo := (341312315579973975554781600278032784768805109023937 : Rat)/1508305786233977859967722421537190213528542299291648,            reHi := (6789274750901495432041045315711855233567191120569199 : Rat)/1508305786233977859967722421537190213528542299291648,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1430, a6 := 20684 }
def label : String := "402.c1"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1430, a6 := 20684 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, 0, -1, 1, -2, 4, 1, -2, 0, 2, 1, 2, -1, -4, 2, 0, -4, 4, -1, -1, 2, 1, 0, -2, -2,                    0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (405548064244724474579518929129607277237107293175545993326408670200112803409178372418351276355184193739680944540181096467170230873194477442991423400689581433895746893349489199750698834280457007061108963410316028046537410209528530744448764099996645943342808666602184567287078272630264712548898984780533848642914277169083678327403679780088561012465955691330333377338644167738191039823649296553879905078485199550033928129712547029323605903480569051642377323153607058323696202582747194417428045097307471270023831326741752745857598594363624703 : Rat)/357763830801008913899549566817813866759231683378733224658287948077178929230733380471083934897952070577268165509314694688195228506418280714692008877792530236077324734520607926266350095661686749542252351714741284198976558750871108433156009969079349454656712086270480971608587456127039051542313005169641402771274496923985042921948931740432699440950298190600065024816365100214253714053065549754797734113468766884223965830231240131530002650654682932274347589732124317174217897392779479434130554213281124370796385513091791980856185138760908800,            reHi := (145382536213257953571863467624219193474270856322236181823290071745146855424749892628989756202607668638093831101023941078339021289075490161943158881630636847483864838910697123505180842890570153546117437998324893584858276752282752465881143492950305545891977924452024195707009426770994546570758164029188231121821477699827000977028631673240370244808457725721785693039892779350331628550360580242023603350491798413426686338325220143177421661416156567680924834575432653520134676647737834156459240645936279485683986276458565158290512046744398159 : Rat)/82560884031002057053742207727187815405976542318169205690374141863964368284015395493327061899527400902446499732918775697275821963019603241852002048721353131402459554120140290676850022075773865278981311934171065584379205865585640407651386915941388335690010481447034070371212489875470550355918385808378785254909499290150394520449753478561392178680838043984630390342238100049443164781476665328030246333877407742513222883899516953430000611689542215140234059168951765501742591706026033715568589433834105624029935118405798149428350416637132800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -90, a6 := 316 }
def label : String := "402.c2"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 67, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -90, a6 := 316 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, 0, -1, 1, -2, 4, 1, -2, 0, 2, 1, 2, -1, -4, 2, 0, -4, 4, -1, -1, 2, 1, 0, -2, -2,                    0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (405548064244724474579518929129607277237107293175545993326408670200112803409178372418351276355184193739680944540181096467170230873194477442991423400689581433895746893349489199750698834280457007061108963410316028046537410209528530744448764099996645943342808666602184567287078272630264712548898984780533848642914277169083678327403679780088561012465955691330333377338644167738191039823649296553879905078485199550033928129712547029323605903480569051642377323153607058323696202582747194417428045097307471270023831326741752745857598594363624703 : Rat)/357763830801008913899549566817813866759231683378733224658287948077178929230733380471083934897952070577268165509314694688195228506418280714692008877792530236077324734520607926266350095661686749542252351714741284198976558750871108433156009969079349454656712086270480971608587456127039051542313005169641402771274496923985042921948931740432699440950298190600065024816365100214253714053065549754797734113468766884223965830231240131530002650654682932274347589732124317174217897392779479434130554213281124370796385513091791980856185138760908800,            reHi := (145382536213257953571863467624219193474270856322236181823290071745146855424749892628989756202607668638093831101023941078339021289075490161943158881630636847483864838910697123505180842890570153546117437998324893584858276752282752465881143492950305545891977924452024195707009426770994546570758164029188231121821477699827000977028631673240370244808457725721785693039892779350331628550360580242023603350491798413426686338325220143177421661416156567680924834575432653520134676647737834156459240645936279485683986276458565158290512046744398159 : Rat)/82560884031002057053742207727187815405976542318169205690374141863964368284015395493327061899527400902446499732918775697275821963019603241852002048721353131402459554120140290676850022075773865278981311934171065584379205865585640407651386915941388335690010481447034070371212489875470550355918385808378785254909499290150394520449753478561392178680838043984630390342238100049443164781476665328030246333877407742513222883899516953430000611689542215140234059168951765501742591706026033715568589433834105624029935118405798149428350416637132800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -30, a6 := 748 }
def label : String := "402.c3"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 67, 67, 67, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -30, a6 := 748 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, 0, -1, 1, -2, 4, 1, -2, 0, 2, 1, 2, -1, -4, 2, 0, -4, 4, -1, -1, 2, 1, 0, -2, -2,                    0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (405548064244724474579518929129607277237107293175545993326408670200112803409178372418351276355184193739680944540181096467170230873194477442991423400689581433895746893349489199750698834280457007061108963410316028046537410209528530744448764099996645943342808666602184567287078272630264712548898984780533848642914277169083678327403679780088561012465955691330333377338644167738191039823649296553879905078485199550033928129712547029323605903480569051642377323153607058323696202582747194417428045097307471270023831326741752745857598594363624703 : Rat)/357763830801008913899549566817813866759231683378733224658287948077178929230733380471083934897952070577268165509314694688195228506418280714692008877792530236077324734520607926266350095661686749542252351714741284198976558750871108433156009969079349454656712086270480971608587456127039051542313005169641402771274496923985042921948931740432699440950298190600065024816365100214253714053065549754797734113468766884223965830231240131530002650654682932274347589732124317174217897392779479434130554213281124370796385513091791980856185138760908800,            reHi := (145382536213257953571863467624219193474270856322236181823290071745146855424749892628989756202607668638093831101023941078339021289075490161943158881630636847483864838910697123505180842890570153546117437998324893584858276752282752465881143492950305545891977924452024195707009426770994546570758164029188231121821477699827000977028631673240370244808457725721785693039892779350331628550360580242023603350491798413426686338325220143177421661416156567680924834575432653520134676647737834156459240645936279485683986276458565158290512046744398159 : Rat)/82560884031002057053742207727187815405976542318169205690374141863964368284015395493327061899527400902446499732918775697275821963019603241852002048721353131402459554120140290676850022075773865278981311934171065584379205865585640407651386915941388335690010481447034070371212489875470550355918385808378785254909499290150394520449753478561392178680838043984630390342238100049443164781476665328030246333877407742513222883899516953430000611689542215140234059168951765501742591706026033715568589433834105624029935118405798149428350416637132800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -10, a6 := -4 }
def label : String := "402.c4"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -10, a6 := -4 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 2, -1, 0, -1, 1, -2, 4, 1, -2, 0, 2, 1, 2, -1, -4, 2, 0, -4, 4, -1, -1, 2, 1, 0, -2, -2,                    0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (405548064244724474579518929129607277237107293175545993326408670200112803409178372418351276355184193739680944540181096467170230873194477442991423400689581433895746893349489199750698834280457007061108963410316028046537410209528530744448764099996645943342808666602184567287078272630264712548898984780533848642914277169083678327403679780088561012465955691330333377338644167738191039823649296553879905078485199550033928129712547029323605903480569051642377323153607058323696202582747194417428045097307471270023831326741752745857598594363624703 : Rat)/357763830801008913899549566817813866759231683378733224658287948077178929230733380471083934897952070577268165509314694688195228506418280714692008877792530236077324734520607926266350095661686749542252351714741284198976558750871108433156009969079349454656712086270480971608587456127039051542313005169641402771274496923985042921948931740432699440950298190600065024816365100214253714053065549754797734113468766884223965830231240131530002650654682932274347589732124317174217897392779479434130554213281124370796385513091791980856185138760908800,            reHi := (145382536213257953571863467624219193474270856322236181823290071745146855424749892628989756202607668638093831101023941078339021289075490161943158881630636847483864838910697123505180842890570153546117437998324893584858276752282752465881143492950305545891977924452024195707009426770994546570758164029188231121821477699827000977028631673240370244808457725721785693039892779350331628550360580242023603350491798413426686338325220143177421661416156567680924834575432653520134676647737834156459240645936279485683986276458565158290512046744398159 : Rat)/82560884031002057053742207727187815405976542318169205690374141863964368284015395493327061899527400902446499732918775697275821963019603241852002048721353131402459554120140290676850022075773865278981311934171065584379205865585640407651386915941388335690010481447034070371212489875470550355918385808378785254909499290150394520449753478561392178680838043984630390342238100049443164781476665328030246333877407742513222883899516953430000611689542215140234059168951765501742591706026033715568589433834105624029935118405798149428350416637132800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -37, a6 := 71 }
def label : String := "402.d1"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -37, a6 := 71 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 2, -1, 2, 1, 1, 2, -4, -1, 0, 2, -2, 1, 6, 1, 4, 2, -2, -4, -6, -1, -1, 0, -1, 2, 8, -2,                    2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (31800809855158514233075377477451255168654114888662751516851983865091347857241000556969810849530428877390776114977839863928556409660667875586104436087338589537634224933355731504315679510090221421300473868166819654710335097497030619037804367089415154908744926854600514136358220485737242363354358827390785310378647761814803656991502855590058487741485607248595004720877759950645938245803694179266790252529906984807984372457505561941954217028128852918908212463456423851814160518492946826033151928499210516617522614516363604146575873147680013321 : Rat)/17915711834727446380662059076799755943096909683042717634811188784480267917631340822051972432197445995830890442043374326308853365975253903481884444572533629514333723244070443076876454790442928765538944689715121231810287672832083968460350960759281268844732274474006393270553110302977109427234289720418196400315361345962635610937596504847822102773741855544664794704265667710729166757580436376182563454451397480125369365806195178894310132736630660685430790839662533113878142400207649316278383907142000920414495920694058198425952040410257817600,            reHi := (14346740332085789452689059378137759001365556817347989104061037101202961974489331490189499585573466789280828416187907476647721662174114994265711056269369557447982605688517606080869832702505713815152735349246293543126093161057039935062608403630673308182698717019205348390239654422257293028320289917896967327255511156334927022054818652263154929561842935773370509676311493117270907096458749432674104942035655911403917875304131781104076738394925015712593472245111296007083233699400057724999610889743925662872589958478003723267019234908709776381 : Rat)/5971903944909148793554019692266585314365636561014239211603729594826755972543780274017324144065815331943630147347791442102951121991751301160628148190844543171444574414690147692292151596814309588512981563238373743936762557610694656153450320253093756281577424824668797756851036767659036475744763240139398800105120448654211870312532168282607367591247285181554931568088555903576388919193478792060854484817132493375123121935398392964770044245543553561810263613220844371292714133402549772092794635714000306804831973564686066141984013470085939200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -27, a6 := 123 }
def label : String := "402.d2"
def inputConductor : Nat := 402
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 67, 67] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 402 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -27, a6 := 123 },   conductor := 402,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 2, -1, 2, 1, 1, 2, -4, -1, 0, 2, -2, 1, 6, 1, 4, 2, -2, -4, -6, -1, -1, 0, -1, 2, 8, -2,                    2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17222765303668560123443603515625,   alphaHi := (674651885226100947931528953856 : Rat)/2152845662958570003509521484375,   geometricUpper := (6584032335231573 : Rat)/9007199254740992,   tail := (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/1290296529050452055358038961055292090108689632388815532040311611776504847054463128590301307730714198557076025156555407402403529182958372923679856427313020967116897412071090055823481793139985426478387786970433624610892568938747944845030449655264126633402979553583030706418884404554306490559929807876166136447514105944657131990807196373064557233858256848756570370758550737600570899800071276992929971732359540943060428441993109731371306742562393243448233339766801802553434351811585743475771096436241109892405567526237790343161446400,   box := { reLo := (31800809855158514233075377477451255168654114888662751516851983865091347857241000556969810849530428877390776114977839863928556409660667875586104436087338589537634224933355731504315679510090221421300473868166819654710335097497030619037804367089415154908744926854600514136358220485737242363354358827390785310378647761814803656991502855590058487741485607248595004720877759950645938245803694179266790252529906984807984372457505561941954217028128852918908212463456423851814160518492946826033151928499210516617522614516363604146575873147680013321 : Rat)/17915711834727446380662059076799755943096909683042717634811188784480267917631340822051972432197445995830890442043374326308853365975253903481884444572533629514333723244070443076876454790442928765538944689715121231810287672832083968460350960759281268844732274474006393270553110302977109427234289720418196400315361345962635610937596504847822102773741855544664794704265667710729166757580436376182563454451397480125369365806195178894310132736630660685430790839662533113878142400207649316278383907142000920414495920694058198425952040410257817600,            reHi := (14346740332085789452689059378137759001365556817347989104061037101202961974489331490189499585573466789280828416187907476647721662174114994265711056269369557447982605688517606080869832702505713815152735349246293543126093161057039935062608403630673308182698717019205348390239654422257293028320289917896967327255511156334927022054818652263154929561842935773370509676311493117270907096458749432674104942035655911403917875304131781104076738394925015712593472245111296007083233699400057724999610889743925662872589958478003723267019234908709776381 : Rat)/5971903944909148793554019692266585314365636561014239211603729594826755972543780274017324144065815331943630147347791442102951121991751301160628148190844543171444574414690147692292151596814309588512981563238373743936762557610694656153450320253093756281577424824668797756851036767659036475744763240139398800105120448654211870312532168282607367591247285181554931568088555903576388919193478792060854484817132493375123121935398392964770044245543553561810263613220844371292714133402549772092794635714000306804831973564686066141984013470085939200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (404733379218013493555567133999149641317214763098157058486687123906957516854869877295534864154325419889905117005942546825960329984289734314819313711635764706562766299360786592976520168821025074981905247534654296140170119088356076710924508570188059145222479351209073930781550317085216141620566635616173165028536669409331969130386605021527252700600249138628910412718409922017783371478801197303302671945199402683522607372565210732456272200224615559328236111396387301998704741186737286012013855695759206238451119900039146672824581831 : Rat)/2580593058100904110716077922110584180217379264777631064080623223553009694108926257180602615461428397114152050313110814804807058365916745847359712854626041934233794824142180111646963586279970852956775573940867249221785137877495889690060899310528253266805959107166061412837768809108612981119859615752332272895028211889314263981614392746129114467716513697513140741517101475201141799600142553985859943464719081886120856883986219462742613485124786486896466679533603605106868703623171486951542192872482219784811135052475580686322892800, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N402.C402_d2
