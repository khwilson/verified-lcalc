module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3, a6 := 2 }
def label : String := "591.a1"
def inputConductor : Nat := 591
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 197] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 591 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3, a6 := 2 },   conductor := 591,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, 1, 0, 1, 0, 2, 2, 0, 0, 0, 4, -4, 0, -7, 0, -1, 0, -5, 0, -5, 0, -1, -2, -3, 0,                    -4, 0, -2, 0, 0, -2, -1, 0, 0, 0, -1, 0, 1, -4, 0, 0, 11, -4, -6, 0, 4, 0, -6, 0, 0, 0, 7, 0, 8, 0,                    -7, 0, 1, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20882553241940837955474853515625,   alphaHi := (674651885226100947931528953856 : Rat)/2610319155242604732513427734375,   finite := ((22961146467926511 : Rat)/9007199254740992, (32975344769535687 : Rat)/9007199254740992),   tail := (601823523177009801905755417716388702392578125 : Rat)/264950016706000615475891503431908126919491584,   box := { reLo := (77161443282442086015385369543311553305633413602847 : Rat)/277820228717511301373248409102616496092732807184384,            reHi := (1648157199032158951718021825526679786242443772193399 : Rat)/277820228717511301373248409102616496092732807184384,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N591.C591_a1
