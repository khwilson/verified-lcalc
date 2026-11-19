module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := 25 }
def label : String := "492.a1"
def inputConductor : Nat := 492
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 492 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := 25 },   conductor := 492,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -2, 0, 1, 0, -1, 0, -2, 0, 0, 0, -1, 0, -4, 0, 2, 0, -6, 0, -5, 0, -1, 0, 5, 0,                    -3, 0, 1, 0, 0, 0, -3, 0, 2, 0, 1, 0, -7, 0, 0, 0, -3, 0, -3, 0, 1, 0, 10, 0, 0, 0, 4, 0, 0, 0, 1, 0,                    -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19053396636049016475677490234375,   alphaHi := (2698607540904403791726115815424 : Rat)/9526698318024508190155029296875,   finite := ((19062047156468099 : Rat)/9007199254740992, (17788135953645969 : Rat)/4503599627370496),   tail := (61531026189897940362830472055721282958984375 : Rat)/46281925632856192130321545840064433370431488,   box := { reLo := (38184928203066486345007059056316523908424815339911 : Rat)/48530116452397814519244045250791403285833567961088,            reHi := (128101125822207749937258523249703802336322364953341 : Rat)/24265058226198907259622022625395701642916783980544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 11, a6 := 695 }
def label : String := "492.b1"
def inputConductor : Nat := 492
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 492 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 11, a6 := 695 },   conductor := 492,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -2, 0, -4, 0, 1, 0, -5, 0, 4, 0, -2, 0, -5, 0, -6, 0, -4, 0, 4, 0, -1, 0, 1, 0, -3, 0, 1,                    0, -5, 0, 8, 0, 5, 0, 4, 0, -1, 0, 9, 0, -2, 0, -11, 0, 9, 0, -5, 0, 2, 0, 10, 0, -6, 0, -4, 0, 1, 0,                    -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19053396636049016475677490234375,   alphaHi := (2698607540904403791726115815424 : Rat)/9526698318024508190155029296875,   finite := ((21701168316200811 : Rat)/9007199254740992, (20961099561424237 : Rat)/4503599627370496),   tail := (61531026189897940362830472055721282958984375 : Rat)/46281925632856192130321545840064433370431488,   box := { reLo := (52404315783107161531280026121569660183623209312079 : Rat)/48530116452397814519244045250791403285833567961088,            reHi := (145196816616840622828933946742310040153099297140393 : Rat)/24265058226198907259622022625395701642916783980544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N492.C492_b1
