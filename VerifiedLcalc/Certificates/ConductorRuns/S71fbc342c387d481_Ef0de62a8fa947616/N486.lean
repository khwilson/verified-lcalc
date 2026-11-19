module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -96, a6 := 386 }
def label : String := "486.a1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -96, a6 := 386 },   conductor := 486,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 2, -1, 0, 3, 0, 0, -4, -2, 0, 1, 6, 0, -7, -3, 0, 0, -9, 0, 4, 4, 0, 2, -9, 0, 2,                    -1, 0, -6, -6, 0, -4, 7, 0, 3, 6, 0, -4, 0, 0, 9, -3, 0, -3, -4, 0, -4, 3, 0, 0, -2, 0, 9, 0, 0, -10,                    -2, 0, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   finite := ((14701308217925035 : Rat)/9007199254740992, (29626056660458585 : Rat)/9007199254740992),   tail := (446044293205009815932416552813625335693359375 : Rat)/348013356669480855331051507516935714459615232,   box := { reLo := (255797476278403366671321607025478171628582233908845 : Rat)/729836906966115114719225331092156767450411003019264,            reHi := (3335967950668199768762796935524017217738552975851695 : Rat)/729836906966115114719225331092156767450411003019264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := -4 }
def label : String := "486.a2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := -4 },   conductor := 486,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 2, -1, 0, 3, 0, 0, -4, -2, 0, 1, 6, 0, -7, -3, 0, 0, -9, 0, 4, 4, 0, 2, -9, 0, 2,                    -1, 0, -6, -6, 0, -4, 7, 0, 3, 6, 0, -4, 0, 0, 9, -3, 0, -3, -4, 0, -4, 3, 0, 0, -2, 0, 9, 0, 0, -10,                    -2, 0, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   finite := ((14701308217925035 : Rat)/9007199254740992, (29626056660458585 : Rat)/9007199254740992),   tail := (446044293205009815932416552813625335693359375 : Rat)/348013356669480855331051507516935714459615232,   box := { reLo := (255797476278403366671321607025478171628582233908845 : Rat)/729836906966115114719225331092156767450411003019264,            reHi := (3335967950668199768762796935524017217738552975851695 : Rat)/729836906966115114719225331092156767450411003019264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -177, a6 := 953 }
def label : String := "486.b1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -177, a6 := 953 },   conductor := 486,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, 0, 0, -6, 0, -1, 1, 0, 1, -6, 0, 5, 0, 0, 6, 6, 0, -5, 1, 0, -1, -6, 0,                    -7, -1, 0, 6, 0, 0, -7, -5, 0, 0, 0, 0, 5, -6, 0, -6, 6, 0, -6, 5, 0, -1, 6, 0, 0, 1, 0, 6, -12, 0,                    -10, 7, 0, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   finite := ((15892385333565677 : Rat)/9007199254740992, (31543479776477015 : Rat)/9007199254740992),   tail := (446044293205009815932416552813625335693359375 : Rat)/348013356669480855331051507516935714459615232,   box := { reLo := (352308279853635814392127431203439061111845722889659 : Rat)/729836906966115114719225331092156767450411003019264,            reHi := (3491333244225310302322172500385913567711220804873505 : Rat)/729836906966115114719225331092156767450411003019264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := 5 }
def label : String := "486.b2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := 5 },   conductor := 486,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, 0, 0, -6, 0, -1, 1, 0, 1, -6, 0, 5, 0, 0, 6, 6, 0, -5, 1, 0, -1, -6, 0,                    -7, -1, 0, 6, 0, 0, -7, -5, 0, 0, 0, 0, 5, -6, 0, -6, 6, 0, -6, 5, 0, -1, 6, 0, 0, 1, 0, 6, -12, 0,                    -10, 7, 0, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   finite := ((15892385333565677 : Rat)/9007199254740992, (31543479776477015 : Rat)/9007199254740992),   tail := (446044293205009815932416552813625335693359375 : Rat)/348013356669480855331051507516935714459615232,   box := { reLo := (352308279853635814392127431203439061111845722889659 : Rat)/729836906966115114719225331092156767450411003019264,            reHi := (3491333244225310302322172500385913567711220804873505 : Rat)/729836906966115114719225331092156767450411003019264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -258, a6 := -748 }
def label : String := "486.c1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1.nonsingular
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -123, a6 := 557 }
def label : String := "486.c2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -123, a6 := 557 },   conductor := 486,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 3, 0, -4, -1, 0, -3, 6, 0, 2, 4, 0, 1, 0, 0, -1, 3, 0, -6, 3, 0, 4, -2, 0, -4, -3, 0, 2,                    -1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   geometricUpper := (6773467225540815 : Rat)/9007199254740992,   tail := (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/43026913343511076289245992633812344992414713404777140425097205944441434644355388210543815155728965636367692603565104046443392492240732333946876656888122091655464236956391361923045536036106476026197740876204948288603806725182354607249353439567546496515904598753273281340298878807674277148607551753210380117086598206802444528618108033103998308391760624049581084995072886691752005588892643773068250264304326994572523425625093886486737774468519926359656341486538416086339421209892256519967408802666124341963548230561065830233145344,   box := { reLo := (158898125813465990877833373678404964791513702157210336639287173484892229280755788670588952543477605743093974657977242269607584597651533419662569149108551914047969244176059892430393865556748814652776230660824938039872918039792288484443380152735956425529783721252690422801798873692163810922801417675295666293093745035081851880445301048328210802719217018699621832540500259850049243677094186177411410193969611368532523712262035158704113996148616676457872703137562854749693988423420245829315250536999235879451994841681317138591963961839733 : Rat)/454365895250501174978149045448483262890595504132473219133828909306392224329325356322165245122950423615121405481571210216672620708481471475249279695464375606963874521211658925853722123044485805305349172849687247693481822738904153959341314260718416871106029973372374015261037386236422096750183727524863347301367648323049081461099416540965236936550536151988092491090594489899735497847497310454606093329456933589817777009449855284274062877371567399926506524025546930738090537025152617475219121390071520648877075025548198637705345420492800,            reHi := (6763327432255007537376674489602823310824504813425457867097797179990407966140225752409660451634728446525234371923069836584793174409703020636501167089665596969455232345545468237085248055251273979654105689750347181494891563897706216668833839936699984207853838305831073536550253650904553759286899767636080495455152649546757785483183382391855656096579027620889349812963981195314130363237440381509685867050555540599238148541204867962130977973405844417589240929578004112865798262190644546047888628146705928972933243725715060338343356928412877 : Rat)/3180561266753508224847043318139382840234168528927312533936802365144745570305277494255156715860652965305849838370998471516708344959370300326744957868250629248747121648481612480976054861311400637137444209947810733854372759172329077715389199825028918097742209813606618106827261703654954677251286092674043431109573538261343570227695915786756658555853753063916647437634161429298148484932481173182242653306198535128724439066148986989918440141600971799485545668178828515166633759176068322326533849730500644542139525178837390463937417943449600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/86053826687022152578491985267624689984829426809554280850194411888882869288710776421087630311457931272735385207130208092886784984481464667893753313776244183310928473912782723846091072072212952052395481752409896577207613450364709214498706879135092993031809197506546562680597757615348554297215103506420760234173196413604889057236216066207996616783521248099162169990145773383504011177785287546136500528608653989145046851250187772973475548937039852719312682973076832172678842419784513039934817605332248683927096461122131660466290688, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1109, a6 := -13931 }
def label : String := "486.d1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1.nonsingular
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := 37 }
def label : String := "486.d2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := 37 },   conductor := 486,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, 1, -3, 0, -4, 1, 0, -3, -6, 0, 2, -4, 0, 1, 0, 0, -1, -3, 0, -6, -3, 0, 4, 2, 0, -4, 3, 0,                    2, 1, 0, 0, 12, 0, 8, -1, 0, -3, -12, 0, -4, -6, 0, -3, 3, 0, 9, 4, 0, 2, -9, 0, 18, -4, 0, 3, 6, 0,                    8, 2, 0, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   finite := ((24495199435503741 : Rat)/9007199254740992, (50041313636033123 : Rat)/9007199254740992),   tail := (446044293205009815932416552813625335693359375 : Rat)/348013356669480855331051507516935714459615232,   box := { reLo := (1049378596362749251888791159256950545174855989157547 : Rat)/729836906966115114719225331092156767450411003019264,            reHi := (4990178941740605061261765806503652832238476151149941 : Rat)/729836906966115114719225331092156767450411003019264,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -20, a6 := -29 }
def label : String := "486.e1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -20, a6 := -29 },   conductor := 486,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -1, 1, 0, 0, 6, 0, -1, -1, 0, 1, 6, 0, 5, 0, 0, 6, -6, 0, -5, -1, 0, -1, 6, 0, -7,                    1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   geometricUpper := (6773467225540815 : Rat)/9007199254740992,   tail := (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/43026913343511076289245992633812344992414713404777140425097205944441434644355388210543815155728965636367692603565104046443392492240732333946876656888122091655464236956391361923045536036106476026197740876204948288603806725182354607249353439567546496515904598753273281340298878807674277148607551753210380117086598206802444528618108033103998308391760624049581084995072886691752005588892643773068250264304326994572523425625093886486737774468519926359656341486538416086339421209892256519967408802666124341963548230561065830233145344,   box := { reLo := (14900853562151634092602491654209219413350018782358620138652203007244125961254345601300720271867060345645005999812003455676885466152864089933431911502832266028081991066514255868618369699114162927569020623163447453900103128976998641018127989759434292147825949021901345636881206136886057672230144878251985992076200197115266001975562495443940588498355682133501961377303453274769273445287366223884178107889828983726619731549258863566604104530395964533127263412990899737227104733562377919375455453947951271896806543217657526364409059214549319 : Rat)/10813908306961927964479947281673901656796172998352862615385128041492134939037943480467532833926220082039889450461394803156808372861859021110932856752052139445740213604837482435318586528458762166267310313822556495104867381185918864232323279405098321532323513366262501563212689792426845902654372715091747665772550030088568138774166113674972639089902760417316601287956148859613704848770435988819625021241075019437663092824906555765722696481443304118250855271808016951566554781198632295910215089083702191443274385608047127577387221007728640,            reHi := (2006728908085774525619598915671526764301332139255478619916094269685371827078651611385076037179364122377190270640356568191555616506984729123426295860282267266797657846830162364510542582254382615203930655348718748691145103139173840211573544923045297758547731606380731399611155901695857015972018297494393211095918343118902713597217966996259847690103970665608938310445206273933183210517741048613134554756548071686371109884333902309929034073107788001379842082595183363522828940272801432853223664332087788515763823351292994487595947006581801 : Rat)/636112253350701644969408663627876568046833705785462506787360473028949114061055498851031343172130593061169967674199694303341668991874060065348991573650125849749424329696322496195210972262280127427488841989562146770874551834465815543077839965005783619548441962721323621365452340730990935450257218534808686221914707652268714045539183157351331711170750612783329487526832285859629696986496234636448530661239707025744887813229797397983688028320194359897109133635765703033326751835213664465306769946100128908427905035767478092787483588689920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/86053826687022152578491985267624689984829426809554280850194411888882869288710776421087630311457931272735385207130208092886784984481464667893753313776244183310928473912782723846091072072212952052395481752409896577207613450364709214498706879135092993031809197506546562680597757615348554297215103506420760234173196413604889057236216066207996616783521248099162169990145773383504011177785287546136500528608653989145046851250187772973475548937039852719312682973076832172678842419784513039934817605332248683927096461122131660466290688, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 25, a6 := -161 }
def label : String := "486.e2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 25, a6 := -161 },   conductor := 486,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, -1, 1, 0, 0, 6, 0, -1, -1, 0, 1, 6, 0, 5, 0, 0, 6, -6, 0, -5, -1, 0, -1, 6, 0, -7,                    1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   geometricUpper := (6773467225540815 : Rat)/9007199254740992,   tail := (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/43026913343511076289245992633812344992414713404777140425097205944441434644355388210543815155728965636367692603565104046443392492240732333946876656888122091655464236956391361923045536036106476026197740876204948288603806725182354607249353439567546496515904598753273281340298878807674277148607551753210380117086598206802444528618108033103998308391760624049581084995072886691752005588892643773068250264304326994572523425625093886486737774468519926359656341486538416086339421209892256519967408802666124341963548230561065830233145344,   box := { reLo := (14900853562151634092602491654209219413350018782358620138652203007244125961254345601300720271867060345645005999812003455676885466152864089933431911502832266028081991066514255868618369699114162927569020623163447453900103128976998641018127989759434292147825949021901345636881206136886057672230144878251985992076200197115266001975562495443940588498355682133501961377303453274769273445287366223884178107889828983726619731549258863566604104530395964533127263412990899737227104733562377919375455453947951271896806543217657526364409059214549319 : Rat)/10813908306961927964479947281673901656796172998352862615385128041492134939037943480467532833926220082039889450461394803156808372861859021110932856752052139445740213604837482435318586528458762166267310313822556495104867381185918864232323279405098321532323513366262501563212689792426845902654372715091747665772550030088568138774166113674972639089902760417316601287956148859613704848770435988819625021241075019437663092824906555765722696481443304118250855271808016951566554781198632295910215089083702191443274385608047127577387221007728640,            reHi := (2006728908085774525619598915671526764301332139255478619916094269685371827078651611385076037179364122377190270640356568191555616506984729123426295860282267266797657846830162364510542582254382615203930655348718748691145103139173840211573544923045297758547731606380731399611155901695857015972018297494393211095918343118902713597217966996259847690103970665608938310445206273933183210517741048613134554756548071686371109884333902309929034073107788001379842082595183363522828940272801432853223664332087788515763823351292994487595947006581801 : Rat)/636112253350701644969408663627876568046833705785462506787360473028949114061055498851031343172130593061169967674199694303341668991874060065348991573650125849749424329696322496195210972262280127427488841989562146770874551834465815543077839965005783619548441962721323621365452340730990935450257218534808686221914707652268714045539183157351331711170750612783329487526832285859629696986496234636448530661239707025744887813229797397983688028320194359897109133635765703033326751835213664465306769946100128908427905035767478092787483588689920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/86053826687022152578491985267624689984829426809554280850194411888882869288710776421087630311457931272735385207130208092886784984481464667893753313776244183310928473912782723846091072072212952052395481752409896577207613450364709214498706879135092993031809197506546562680597757615348554297215103506420760234173196413604889057236216066207996616783521248099162169990145773383504011177785287546136500528608653989145046851250187772973475548937039852719312682973076832172678842419784513039934817605332248683927096461122131660466290688, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -56, a6 := 163 }
def label : String := "486.f1"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -56, a6 := 163 },   conductor := 486,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 3, 0, 2, 1, 0, 3, 0, 0, -4, 2, 0, 1, -6, 0, -7, 3, 0, 0, 9, 0, 4, -4, 0, 2, 9, 0, 2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   geometricUpper := (6773467225540815 : Rat)/9007199254740992,   tail := (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/43026913343511076289245992633812344992414713404777140425097205944441434644355388210543815155728965636367692603565104046443392492240732333946876656888122091655464236956391361923045536036106476026197740876204948288603806725182354607249353439567546496515904598753273281340298878807674277148607551753210380117086598206802444528618108033103998308391760624049581084995072886691752005588892643773068250264304326994572523425625093886486737774468519926359656341486538416086339421209892256519967408802666124341963548230561065830233145344,   box := { reLo := (72396404955327362737922565825123912774047268007552232335856452825928781234344466384969660252759849468278579956820233334226456392559311265583500911988705833083018378011318327072733925549883878628623962780558143621509531869174916621937406900561581666202779303488313613397195763728240308718427622836679113271509315881458497641571128416532201390017197223893929017195690135323260254522111282804582710985467228672129667688229255597747168544938309328401869129167160823533627168800697496996008853981378646933030177735337913947958609757716863 : Rat)/41305990477318288634377185949862114808235954921133929012166264482399293120847759665651385920268220328647400498324655474242965518952861043204479972314943236996715865564696265986702011185862345936849924804517022517589256612627650359940119478247128806464184543033852183205548853294220190613653066138623940663760695302095371041918128776451385176050048741089826590099144953627248681622499755495873281211768812144528888819040895934934005716124687945447864229456867902794371867002286601588656283762733774604443370456868018057973213220044800,            reHi := (17348598496641472148561748328711326455896986507526900725323526829805640063252554410759927678857043328349778878493593694057933729966207509263504526252458506389065630564008711111486422995704074410099983466943739269343019586361023603161553457457728635877726930366616562631986625207550197901467056486335058640137941321679957976526502647913046386683204340195399629077763898833346214207021997483051277177343154398601858427175822740324729912487717704799025342536027758921180001869374868439342579426358266469761638287562052530894556439407431159 : Rat)/4915412866800876347490885128033591662180078635614937552447785473405515881380883400212514924511918219109040659300634001434912896755390464141333116705478245202609188002198855652417539331117619166485141051737525679593121536902690392832874217911408327969237960621028409801460313542012202683024714870496248938987522740949349153988257324397714835949955800189689364221798249481642593113077470904008920464200488645198937769465866616257146680218837865508295843305367280432530252173272105589050097767765319177928761084367294148898812373185331200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/86053826687022152578491985267624689984829426809554280850194411888882869288710776421087630311457931272735385207130208092886784984481464667893753313776244183310928473912782723846091072072212952052395481752409896577207613450364709214498706879135092993031809197506546562680597757615348554297215103506420760234173196413604889057236216066207996616783521248099162169990145773383504011177785287546136500528608653989145046851250187772973475548937039852719312682973076832172678842419784513039934817605332248683927096461122131660466290688, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11, a6 := -11 }
def label : String := "486.f2"
def inputConductor : Nat := 486
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 486 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11, a6 := -11 },   conductor := 486,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 3, 0, 2, 1, 0, 3, 0, 0, -4, 2, 0, 1, -6, 0, -7, 3, 0, 0, 9, 0, 4, -4, 0, 2, 9, 0, 2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9468430503427081775665283203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18936861006854163455963134765625,   geometricUpper := (6773467225540815 : Rat)/9007199254740992,   tail := (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/43026913343511076289245992633812344992414713404777140425097205944441434644355388210543815155728965636367692603565104046443392492240732333946876656888122091655464236956391361923045536036106476026197740876204948288603806725182354607249353439567546496515904598753273281340298878807674277148607551753210380117086598206802444528618108033103998308391760624049581084995072886691752005588892643773068250264304326994572523425625093886486737774468519926359656341486538416086339421209892256519967408802666124341963548230561065830233145344,   box := { reLo := (72396404955327362737922565825123912774047268007552232335856452825928781234344466384969660252759849468278579956820233334226456392559311265583500911988705833083018378011318327072733925549883878628623962780558143621509531869174916621937406900561581666202779303488313613397195763728240308718427622836679113271509315881458497641571128416532201390017197223893929017195690135323260254522111282804582710985467228672129667688229255597747168544938309328401869129167160823533627168800697496996008853981378646933030177735337913947958609757716863 : Rat)/41305990477318288634377185949862114808235954921133929012166264482399293120847759665651385920268220328647400498324655474242965518952861043204479972314943236996715865564696265986702011185862345936849924804517022517589256612627650359940119478247128806464184543033852183205548853294220190613653066138623940663760695302095371041918128776451385176050048741089826590099144953627248681622499755495873281211768812144528888819040895934934005716124687945447864229456867902794371867002286601588656283762733774604443370456868018057973213220044800,            reHi := (17348598496641472148561748328711326455896986507526900725323526829805640063252554410759927678857043328349778878493593694057933729966207509263504526252458506389065630564008711111486422995704074410099983466943739269343019586361023603161553457457728635877726930366616562631986625207550197901467056486335058640137941321679957976526502647913046386683204340195399629077763898833346214207021997483051277177343154398601858427175822740324729912487717704799025342536027758921180001869374868439342579426358266469761638287562052530894556439407431159 : Rat)/4915412866800876347490885128033591662180078635614937552447785473405515881380883400212514924511918219109040659300634001434912896755390464141333116705478245202609188002198855652417539331117619166485141051737525679593121536902690392832874217911408327969237960621028409801460313542012202683024714870496248938987522740949349153988257324397714835949955800189689364221798249481642593113077470904008920464200488645198937769465866616257146680218837865508295843305367280432530252173272105589050097767765319177928761084367294148898812373185331200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (38223887502858592958138307506951193658073715932513107950859560815960758430174312638854777582779176733075911717845009921589037414122642406024149560868224108120521027925182144107981245014384657257926692488774139260475378657993443503736134816282040985465831845308669311086040655962317254571456541627790327071412234070513718422073070290890149031164562388321056856802041858046765087413554970400501161741696485929380947071587606128326107798506101384090380527971229051414518906373670561653439670317887151630306965671479701995849609375 : Rat)/86053826687022152578491985267624689984829426809554280850194411888882869288710776421087630311457931272735385207130208092886784984481464667893753313776244183310928473912782723846091072072212952052395481752409896577207613450364709214498706879135092993031809197506546562680597757615348554297215103506420760234173196413604889057236216066207996616783521248099162169990145773383504011177785287546136500528608653989145046851250187772973475548937039852719312682973076832172678842419784513039934817605332248683927096461122131660466290688, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N486.C486_f2
