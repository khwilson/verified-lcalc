module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -221, a6 := -1191 }
def label : String := "564.a1"
def inputConductor : Nat := 564
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 564 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -221, a6 := -1191 },   conductor := 564,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 3, 0, -2, 0, 1, 0, -6, 0, -6, 0, 1, 0, 5, 0, -4, 0, -1, 0, -5, 0,                    -10, 0, -3, 0, 1, 0, -3, 0, 2, 0, -6, 0, 10, 0, -1, 0, 1, 0, -6, 0, 6, 0, 12, 0, -3, 0, 6, 0, 8, 0,                    -10, 0, -1, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2549995546267212009429931640625,   alphaHi := (5397215081808807583452231630848 : Rat)/20399964370137695980072021484375,   finite := ((2580021259522917 : Rat)/1125899906842624, (38775219605642171 : Rat)/9007199254740992),   tail := (55533938348762509279854740339374542236328125 : Rat)/27976452805993274678223290995273736751415296,   box := { reLo := (8991162285233363854786213366759449312460253591293 : Rat)/29335436977497203988992665578660153787852045418496,            reHi := (1476144743568337729135223897593490496313211813345059 : Rat)/234683495819977631911941324629281230302816363347968,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -517, a6 := -4681 }
def label : String := "564.b1"
def inputConductor : Nat := 564
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 47, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 564 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -517, a6 := -4681 },   conductor := 564,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -3, 0, -1, 0, 1, 0, -3, 0, -4, 0, -3, 0, 0, 0, 2, 0, -1, 0, -9, 0, 4, 0, 1, 0, -3, 0, -4,                    0, -3, 0, 3, 0, 5, 0, -4, 0, -6, 0, 8, 0, -3, 0, -1, 0, -6, 0, 0, 0, 6, 0, 9, 0, 2, 0, 6, 0, 2, 0,                    -1, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2549995546267212009429931640625,   alphaHi := (5397215081808807583452231630848 : Rat)/20399964370137695980072021484375,   finite := ((24412116013688427 : Rat)/9007199254740992, (46017810884017475 : Rat)/9007199254740992),   tail := (55533938348762509279854740339374542236328125 : Rat)/27976452805993274678223290995273736751415296,   box := { reLo := (170207734632846973058610998944109039759612884992083 : Rat)/234683495819977631911941324629281230302816363347968,            reHi := (1664851198475476739820774657939639980960611271879275 : Rat)/234683495819977631911941324629281230302816363347968,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -37, a6 := 71 }
def label : String := "564.b2"
def inputConductor : Nat := 564
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 564 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -37, a6 := 71 },   conductor := 564,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -3, 0, -1, 0, 1, 0, -3, 0, -4, 0, -3, 0, 0, 0, 2, 0, -1, 0, -9, 0, 4, 0, 1, 0, -3, 0, -4,                    0, -3, 0, 3, 0, 5, 0, -4, 0, -6, 0, 8, 0, -3, 0, -1, 0, -6, 0, 0, 0, 6, 0, 9, 0, 2, 0, 6, 0, 2, 0,                    -1, 0],   alphaLo := (674651885226100947929381470208 : Rat)/2549995546267212009429931640625,   alphaHi := (5397215081808807583452231630848 : Rat)/20399964370137695980072021484375,   finite := ((24412116013688427 : Rat)/9007199254740992, (46017810884017475 : Rat)/9007199254740992),   tail := (55533938348762509279854740339374542236328125 : Rat)/27976452805993274678223290995273736751415296,   box := { reLo := (170207734632846973058610998944109039759612884992083 : Rat)/234683495819977631911941324629281230302816363347968,            reHi := (1664851198475476739820774657939639980960611271879275 : Rat)/234683495819977631911941324629281230302816363347968,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N564.C564_b2
