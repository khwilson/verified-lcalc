module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -963, a6 := 11502 }
def label : String := "360.a1"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -963, a6 := 11502 },   conductor := 360,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 2, 0, -8,                    0, 0, 0, 4, 0, 6, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   finite := ((12700463769479109 : Rat)/9007199254740992, (4087257053764887 : Rat)/1125899906842624),   tail := (4475078954773299174405017977237701416015625 : Rat)/8892814825581175831179302189322173023256576,   box := { reLo := (16911640920359466192989025555834263839489616191479 : Rat)/18649584397097214056709335944941373800068574871552,            reHi := (9635861753945767161081180164809973892820030972797 : Rat)/2331198049637151757088666993117671725008571858944,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -63, a6 := 162 }
def label : String := "360.a2"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -63, a6 := 162 },   conductor := 360,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 2, 0, -8,                    0, 0, 0, 4, 0, 6, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   finite := ((12700463769479109 : Rat)/9007199254740992, (4087257053764887 : Rat)/1125899906842624),   tail := (4475078954773299174405017977237701416015625 : Rat)/8892814825581175831179302189322173023256576,   box := { reLo := (16911640920359466192989025555834263839489616191479 : Rat)/18649584397097214056709335944941373800068574871552,            reHi := (9635861753945767161081180164809973892820030972797 : Rat)/2331198049637151757088666993117671725008571858944,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -18, a6 := -27 }
def label : String := "360.a3"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -18, a6 := -27 },   conductor := 360,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 2, 0, -8,                    0, 0, 0, 4, 0, 6, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   finite := ((12700463769479109 : Rat)/9007199254740992, (4087257053764887 : Rat)/1125899906842624),   tail := (4475078954773299174405017977237701416015625 : Rat)/8892814825581175831179302189322173023256576,   box := { reLo := (16911640920359466192989025555834263839489616191479 : Rat)/18649584397097214056709335944941373800068574871552,            reHi := (9635861753945767161081180164809973892820030972797 : Rat)/2331198049637151757088666993117671725008571858944,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 117, a6 := 918 }
def label : String := "360.a4"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 117, a6 := 918 },   conductor := 360,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -2, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, 1, 0, 0, 0, 2, 0, -8,                    0, 0, 0, 4, 0, 6, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   finite := ((12700463769479109 : Rat)/9007199254740992, (4087257053764887 : Rat)/1125899906842624),   tail := (4475078954773299174405017977237701416015625 : Rat)/8892814825581175831179302189322173023256576,   box := { reLo := (16911640920359466192989025555834263839489616191479 : Rat)/18649584397097214056709335944941373800068574871552,            reHi := (9635861753945767161081180164809973892820030972797 : Rat)/2331198049637151757088666993117671725008571858944,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28803, a6 := 1881502 }
def label : String := "360.b1"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -28803, a6 := 1881502 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1803, a6 := 29302 }
def label : String := "360.b2"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1803, a6 := 29302 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -723, a6 := 64078 }
def label : String := "360.b3"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -723, a6 := 64078 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -183, a6 := -182 }
def label : String := "360.b4"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -183, a6 := -182 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -138, a6 := -623 }
def label : String := "360.b5"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -138, a6 := -623 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 717, a6 := -1442 }
def label : String := "360.b6"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0, 0, 0, 0, 0],                kodaira := -12 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 717, a6 := -1442 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/478127885985798789548209729869231814199122380910278871055065136275907714877481242111852556234221570950595654821348504098665436672120144198409411530548245387147281507922095472346920941798871199922585971587301442442808835000262881397745266662412945060127920076055961388153875915828827728365801139218118720381601779295671636297427323309696555661621431831792482817882933132244290395010742787770826586243877179805992647503546031038792764633188734833061541458666919377540674845386110907505751716535305909163217169000922349568,   box := { reLo := (609831330052902363189006707587217021264729406994596004017723620786511204716763332822766124774300958089060231176464986057490880342635481771813851198936513684594192231256198323244533921067675746748397944213120152941920866149968082064071030654217043974816525071293107018595622847808246141780833706267663522442947658901184492694449545243554950359839326365965344347277336573871248602502357024244907065703398374172156080203461934800752607294759208481724002939362172935971309802504941263907636619860216991407484655782933365071037415683 : Rat)/496343494607311405027689775810600587279322350575662970671775020448091584919647675040550439754807791660817984194709904604402970278731326225047968648921478066551606530672572183180912657782312690151216669350990845654170416364115021594088251339032554398116035046331524292528449945847993345674842548714794283313987958022877792770968542552001630357492861276897950674970003095056578615514523189082192289090614507729875899039790439431451707651811916785266182626312383471929359528993790748984951656637731773246687854981656464034313011200,            reHi := (26657365575567198793482175823278177032541967728044339480608841688839183437151695099147255125353092057627140683233641892911825611340170131793626340017453357666072688465034765095589947006967280035220642952063302234947382613923268912299725754997397529510348792845217966633873883314887790618810545163355437685764079952957574117115201474291537570976182162178343727252587288960107506392757338252965251867160509802865547403885306482813402585434705050102092153450157956048695579603517909157672165625966941246850080900584490669266650209 : Rat)/17115292917493496725092750890020709906183529330195274850750862774072123617918885346225877232924406608993723592921031193255274837197631938794757539617982002294882983816295592523479746820079747936248850667275546401867945391866035227382353494449398427521242587804535320432015515374068736057753191334992906321171998552513027336929949743172470012327340044030963816378275968795054435017742178933868699623814293369995720656544497911429369229372824716733316642286633912825150328585992784447756953677163164594713374309712291863252172800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (78620856132046943302695463487938171062956162579869179258653725589250992767897793402956446302160678570425541159736211296923297704045550348986095462294186948229908107486734162803636406031697040995397553521424924042686634767146976865091693359260390135776673422813395469164452312869138991344714540696164767544250739913191016116879113049232442776321918797295772847304359785810234216926970556562078133586996664609029525525734166723866275843225196289354597888059064762809463034683343540126186765217950707252323597753462819923 : Rat)/956255771971597579096419459738463628398244761820557742110130272551815429754962484223705112468443141901191309642697008197330873344240288396818823061096490774294563015844190944693841883597742399845171943174602884885617670000525762795490533324825890120255840152111922776307751831657655456731602278436237440763203558591343272594854646619393111323242863663584965635765866264488580790021485575541653172487754359611985295007092062077585529266377469666123082917333838755081349690772221815011503433070611818326434338001844699136, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_b6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -123, a6 := -522 }
def label : String := "360.c1"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -123, a6 := -522 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (107612514580184172744773184377889581722494281271984823923073196666513846405708297669824404291177964418379007879000544985214886708187545643175887555940797725190971699954721501768289652343830672328245872367980981643496473837116726677198914968611471562788336334134440897806371182974241774892413056193540518306162264541925737269837919128967576187309636589094852174101821137739023430239585260652272969387 : Rat)/8090683951679179319287083337897830485498466251478054823931956945186038624780286411207817711100599358847671523268322767698812445735980493902808293382161295460380072525911476629177771156948286364048214244693098372294432088843464055786708471706276758398020737563208406228348792410165556450565345462099235120584371879906115147703105659050984692251893269887293774574882747046115776331469244874389570191360,            reHi := (161696048501628220560929754872790817886536681495251014553767120907275012542827728134432475447244044534261079408240637093871415393859585236886768984223952586168108964168464647677707528396704903146547062255002926999004981787820709220448537794018848157982314030961132233342701716250152011278292571240215851212334928501970815723058650103841267427536235536689474492028705956298373291670483033735253673324883 : Rat)/56634787661754255235009583365284813398489263760346383767523698616302270373462004878454723977704195511933700662878259373891687120151863457319658053675129068222660507681380336404244398098638004548337499712851688606061024621904248390506959301943937308786145162942458843598441546871158895153957418234694645844090603159342806033921739613356892845763252889211056422024179229322810434320284714120726991339520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := -18 }
def label : String := "360.c2"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := -18 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -1, 0, 2, 0, 0, 0, 2, 0, 4, 0, 0, 0, -2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (107612514580184172744773184377889581722494281271984823923073196666513846405708297669824404291177964418379007879000544985214886708187545643175887555940797725190971699954721501768289652343830672328245872367980981643496473837116726677198914968611471562788336334134440897806371182974241774892413056193540518306162264541925737269837919128967576187309636589094852174101821137739023430239585260652272969387 : Rat)/8090683951679179319287083337897830485498466251478054823931956945186038624780286411207817711100599358847671523268322767698812445735980493902808293382161295460380072525911476629177771156948286364048214244693098372294432088843464055786708471706276758398020737563208406228348792410165556450565345462099235120584371879906115147703105659050984692251893269887293774574882747046115776331469244874389570191360,            reHi := (161696048501628220560929754872790817886536681495251014553767120907275012542827728134432475447244044534261079408240637093871415393859585236886768984223952586168108964168464647677707528396704903146547062255002926999004981787820709220448537794018848157982314030961132233342701716250152011278292571240215851212334928501970815723058650103841267427536235536689474492028705956298373291670483033735253673324883 : Rat)/56634787661754255235009583365284813398489263760346383767523698616302270373462004878454723977704195511933700662878259373891687120151863457319658053675129068222660507681380336404244398098638004548337499712851688606061024621904248390506959301943937308786145162942458843598441546871158895153957418234694645844090603159342806033921739613356892845763252889211056422024179229322810434320284714120726991339520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1107, a6 := 14094 }
def label : String := "360.d1"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1107, a6 := 14094 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 2, 0, 0, 0, -2, 0, 4, 0, 0, 0, 2, 0, 4, 0, 0, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (1197588317103920084034158978857023711157788473367582854678895549912028013233906580907388138300469598665929352623845673670982686979851621326619962613948569404289444076065570334467929755701375499708696778653653474306778350524479906160479833371663774893286474862900702702485771335573083138153259476935669664284806288018573687163700889925200101170302014498712050230711706553053492864147783880489171576491 : Rat)/8090683951679179319287083337897830485498466251478054823931956945186038624780286411207817711100599358847671523268322767698812445735980493902808293382161295460380072525911476629177771156948286364048214244693098372294432088843464055786708471706276758398020737563208406228348792410165556450565345462099235120584371879906115147703105659050984692251893269887293774574882747046115776331469244874389570191360,            reHi := (169325879119294371939955455434144756792583740839920200769057877379993611710625116117095421585309085973993931821454552994671789995761233766670877509630006987921798270801240589506605009120207716938210218599002634447647954924632251476831504222840214281295801000662496065975457517318343900821118496185410755234185436666307351372315690899414895102417182182056794878424975154205574577707840424074111963574611 : Rat)/56634787661754255235009583365284813398489263760346383767523698616302270373462004878454723977704195511933700662878259373891687120151863457319658053675129068222660507681380336404244398098638004548337499712851688606061024621904248390506959301943937308786145162942458843598441546871158895153957418234694645844090603159342806033921739613356892845763252889211056422024179229322810434320284714120726991339520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := 486 }
def label : String := "360.d2"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := 486 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 2, 0, 0, 0, -2, 0, 4, 0, 0, 0, 2, 0, 4, 0, 0, 0, -8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (1197588317103920084034158978857023711157788473367582854678895549912028013233906580907388138300469598665929352623845673670982686979851621326619962613948569404289444076065570334467929755701375499708696778653653474306778350524479906160479833371663774893286474862900702702485771335573083138153259476935669664284806288018573687163700889925200101170302014498712050230711706553053492864147783880489171576491 : Rat)/8090683951679179319287083337897830485498466251478054823931956945186038624780286411207817711100599358847671523268322767698812445735980493902808293382161295460380072525911476629177771156948286364048214244693098372294432088843464055786708471706276758398020737563208406228348792410165556450565345462099235120584371879906115147703105659050984692251893269887293774574882747046115776331469244874389570191360,            reHi := (169325879119294371939955455434144756792583740839920200769057877379993611710625116117095421585309085973993931821454552994671789995761233766670877509630006987921798270801240589506605009120207716938210218599002634447647954924632251476831504222840214281295801000662496065975457517318343900821118496185410755234185436666307351372315690899414895102417182182056794878424975154205574577707840424074111963574611 : Rat)/56634787661754255235009583365284813398489263760346383767523698616302270373462004878454723977704195511933700662878259373891687120151863457319658053675129068222660507681380336404244398098638004548337499712851688606061024621904248390506959301943937308786145162942458843598441546871158895153957418234694645844090603159342806033921739613356892845763252889211056422024179229322810434320284714120726991339520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1947, a6 := 33046 }
def label : String := "360.e1"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 2, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1947, a6 := 33046 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (142484454781571573088077054865432707454989386843924027306225266943799675416229421669303183350246594982282097533496865076593369054324284982766966067312669472626706137643190308429277445590166175994456895224406530893502862775888522963773244681496208496748923083878261074370633855625613018332607261045778352361449437796398209295326191348334949306392482213110300122366041335291934380100071344433139300321 : Rat)/735516722879925392662462121627075498681678750134368620357450631380548965889116946473437973736418123531606502115302069790801131430543681263891663034741935950943642956901043329925251923358935124004383113153918033844948371713042186889700770155116068945274612505746218748031708400924141495505940496554475920053124716355101377063918696277362244750172115444299434052262067913283252393769931352217233653760,            reHi := (15628551265249813247338446038992289438459816831033105255735779495965870839573750443363712082575936829502868086766051744014967402352491754737991923605766101841613190864618843941601548552177376977804740669733567209496484529886359080541525686425393169012005982107981996583995337465347580053554303038078555943365809353329773916282893803451256718140335109207511413003546025003222886107987673137062020020441 : Rat)/5148617060159477748637234851389528490771751250940580342502154419663842761223818625314065816154926864721245514807114488535607920013805768847241641243193551656605500698307303309476763463512545868030681792077426236914638601991295308227905391085812482616922287540223531236221958806468990468541583475881331440371873014485709639447430873941535713251204808110096038365834475392982766756389519465520635576320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1227, a6 := -16346 }
def label : String := "360.e2"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1227, a6 := -16346 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (142484454781571573088077054865432707454989386843924027306225266943799675416229421669303183350246594982282097533496865076593369054324284982766966067312669472626706137643190308429277445590166175994456895224406530893502862775888522963773244681496208496748923083878261074370633855625613018332607261045778352361449437796398209295326191348334949306392482213110300122366041335291934380100071344433139300321 : Rat)/735516722879925392662462121627075498681678750134368620357450631380548965889116946473437973736418123531606502115302069790801131430543681263891663034741935950943642956901043329925251923358935124004383113153918033844948371713042186889700770155116068945274612505746218748031708400924141495505940496554475920053124716355101377063918696277362244750172115444299434052262067913283252393769931352217233653760,            reHi := (15628551265249813247338446038992289438459816831033105255735779495965870839573750443363712082575936829502868086766051744014967402352491754737991923605766101841613190864618843941601548552177376977804740669733567209496484529886359080541525686425393169012005982107981996583995337465347580053554303038078555943365809353329773916282893803451256718140335109207511413003546025003222886107987673137062020020441 : Rat)/5148617060159477748637234851389528490771751250940580342502154419663842761223818625314065816154926864721245514807114488535607920013805768847241641243193551656605500698307303309476763463512545868030681792077426236914638601991295308227905391085812482616922287540223531236221958806468990468541583475881331440371873014485709639447430873941535713251204808110096038365834475392982766756389519465520635576320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -147, a6 := 286 }
def label : String := "360.e3"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -147, a6 := 286 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (142484454781571573088077054865432707454989386843924027306225266943799675416229421669303183350246594982282097533496865076593369054324284982766966067312669472626706137643190308429277445590166175994456895224406530893502862775888522963773244681496208496748923083878261074370633855625613018332607261045778352361449437796398209295326191348334949306392482213110300122366041335291934380100071344433139300321 : Rat)/735516722879925392662462121627075498681678750134368620357450631380548965889116946473437973736418123531606502115302069790801131430543681263891663034741935950943642956901043329925251923358935124004383113153918033844948371713042186889700770155116068945274612505746218748031708400924141495505940496554475920053124716355101377063918696277362244750172115444299434052262067913283252393769931352217233653760,            reHi := (15628551265249813247338446038992289438459816831033105255735779495965870839573750443363712082575936829502868086766051744014967402352491754737991923605766101841613190864618843941601548552177376977804740669733567209496484529886359080541525686425393169012005982107981996583995337465347580053554303038078555943365809353329773916282893803451256718140335109207511413003546025003222886107987673137062020020441 : Rat)/5148617060159477748637234851389528490771751250940580342502154419663842761223818625314065816154926864721245514807114488535607920013805768847241641243193551656605500698307303309476763463512545868030681792077426236914638601991295308227905391085812482616922287540223531236221958806468990468541583475881331440371873014485709639447430873941535713251204808110096038365834475392982766756389519465520635576320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 33, a6 := 34 }
def label : String := "360.e4"
def inputConductor : Nat := 360
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 360 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 33, a6 := 34 },   conductor := 360,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -6, 0, 0, 0, 2, 0, 4, 0, 0, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8149127478776754665374755859375,   alphaHi := (5397215081808807583452231630848 : Rat)/16298254957553509235382080078125,   geometricUpper := (3234013876665683 : Rat)/4503599627370496,   tail := (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/1523171609969092832998461583248755912239309049016574588892698326476384575808146756419101802160800446341481930719119603613285008709203394729369649160238847657193002385456254242573805198668285666368562107238613818704139436331719119230667281350872503691923775859151182472082811437348730019582178979579974362535851634147056498056304702522054412023923119260899456500537535672641006437909505062731776,   box := { reLo := (142484454781571573088077054865432707454989386843924027306225266943799675416229421669303183350246594982282097533496865076593369054324284982766966067312669472626706137643190308429277445590166175994456895224406530893502862775888522963773244681496208496748923083878261074370633855625613018332607261045778352361449437796398209295326191348334949306392482213110300122366041335291934380100071344433139300321 : Rat)/735516722879925392662462121627075498681678750134368620357450631380548965889116946473437973736418123531606502115302069790801131430543681263891663034741935950943642956901043329925251923358935124004383113153918033844948371713042186889700770155116068945274612505746218748031708400924141495505940496554475920053124716355101377063918696277362244750172115444299434052262067913283252393769931352217233653760,            reHi := (15628551265249813247338446038992289438459816831033105255735779495965870839573750443363712082575936829502868086766051744014967402352491754737991923605766101841613190864618843941601548552177376977804740669733567209496484529886359080541525686425393169012005982107981996583995337465347580053554303038078555943365809353329773916282893803451256718140335109207511413003546025003222886107987673137062020020441 : Rat)/5148617060159477748637234851389528490771751250940580342502154419663842761223818625314065816154926864721245514807114488535607920013805768847241641243193551656605500698307303309476763463512545868030681792077426236914638601991295308227905391085812482616922287540223531236221958806468990468541583475881331440371873014485709639447430873941535713251204808110096038365834475392982766756389519465520635576320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2164247932704889645438435962010444251352360641522238208886796257092609004110763628598371376173435771847695394441915159838181557803578146094468851721449753169278506842666582534964237675071069738630456922015993243679246897277905383219911952361677332009241363346756445684238398352951728550499872753743421272307888715172362931000198482825337353475033021325903117402878343405789055702502051344921875 : Rat)/3046343219938185665996923166497511824478618098033149177785396652952769151616293512838203604321600892682963861438239207226570017418406789458739298320477695314386004770912508485147610397336571332737124214477227637408278872663438238461334562701745007383847551718302364944165622874697460039164357959159948725071703268294112996112609405044108824047846238521798913001075071345282012875819010125463552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N360.C360_e4
