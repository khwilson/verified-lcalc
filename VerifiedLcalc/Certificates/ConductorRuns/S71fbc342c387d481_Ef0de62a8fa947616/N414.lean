module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2223, a6 := -39785 }
def label : String := "414.a1"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 2, 1, 2, 1, 1, 0],                kodaira := -12 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2223, a6 := -39785 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 0, -1, 0, 2, 0, 0, -2, 0, 0, 1, -2, 0, -8, -2, 0, 0, 1, 0, -1, 2, 0, 0, 2, 0, -8,                    -1, 0, 2, 0, 0, 2, 8, 0, 2, -10, 0, 8, 0, 0, -1, -8, 0, -7, 1, 0, -2, -2, 0, 0, 0, 0, -2, 4, 0, 2, 8,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((3372815239864619 : Rat)/2251799813685248, (1667778654772275 : Rat)/562949953421312),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (13368635959087462668214888045392436569491072393579 : Rat)/18773440773300942498916901238277743445389835501568,            reHi := (17592108922532543058798822579924524349466212508275 : Rat)/4693360193325235624729225309569435861347458875392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -963, a6 := 11371 }
def label : String := "414.a2"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 23, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -963, a6 := 11371 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 0, -1, 0, 2, 0, 0, -2, 0, 0, 1, -2, 0, -8, -2, 0, 0, 1, 0, -1, 2, 0, 0, 2, 0, -8,                    -1, 0, 2, 0, 0, 2, 8, 0, 2, -10, 0, 8, 0, 0, -1, -8, 0, -7, 1, 0, -2, -2, 0, 0, 0, 0, -2, 4, 0, 2, 8,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((3372815239864619 : Rat)/2251799813685248, (1667778654772275 : Rat)/562949953421312),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (13368635959087462668214888045392436569491072393579 : Rat)/18773440773300942498916901238277743445389835501568,            reHi := (17592108922532543058798822579924524349466212508275 : Rat)/4693360193325235624729225309569435861347458875392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -153, a6 := -455 }
def label : String := "414.a3"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 1, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -153, a6 := -455 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 0, -1, 0, 2, 0, 0, -2, 0, 0, 1, -2, 0, -8, -2, 0, 0, 1, 0, -1, 2, 0, 0, 2, 0, -8,                    -1, 0, 2, 0, 0, 2, 8, 0, 2, -10, 0, 8, 0, 0, -1, -8, 0, -7, 1, 0, -2, -2, 0, 0, 0, 0, -2, 4, 0, 2, 8,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((3372815239864619 : Rat)/2251799813685248, (1667778654772275 : Rat)/562949953421312),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (13368635959087462668214888045392436569491072393579 : Rat)/18773440773300942498916901238277743445389835501568,            reHi := (17592108922532543058798822579924524349466212508275 : Rat)/4693360193325235624729225309569435861347458875392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 27, a6 := -59 }
def label : String := "414.a4"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 27, a6 := -59 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 0, -1, 0, 2, 0, 0, -2, 0, 0, 1, -2, 0, -8, -2, 0, 0, 1, 0, -1, 2, 0, 0, 2, 0, -8,                    -1, 0, 2, 0, 0, 2, 8, 0, 2, -10, 0, 8, 0, 0, -1, -8, 0, -7, 1, 0, -2, -2, 0, 0, 0, 0, -2, 4, 0, 2, 8,                    0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((3372815239864619 : Rat)/2251799813685248, (1667778654772275 : Rat)/562949953421312),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (13368635959087462668214888045392436569491072393579 : Rat)/18773440773300942498916901238277743445389835501568,            reHi := (17592108922532543058798822579924524349466212508275 : Rat)/4693360193325235624729225309569435861347458875392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1532, a6 := 23455 }
def label : String := "414.b1"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1532, a6 := 23455 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, 1, -4, 0, -4, 1, 0, -4, -2, 0, -2, -4, 0, 1, 2, 0, -2, -4, 0, -2, -1, 0, 11, -2, 0, -4, -2,                    0, 0, 1, 0, 2, 16, 0, -4, -2, 0, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((14111258226468871 : Rat)/9007199254740992, (50202935139032863 : Rat)/9007199254740992),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (58643512188283040752339134183619647551181984861511 : Rat)/75093763093203769995667604953110973781559342006272,            reHi := (477549222481975242858999861900066180368458089010783 : Rat)/75093763093203769995667604953110973781559342006272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -92, a6 := 415 }
def label : String := "414.b2"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -92, a6 := 415 },   conductor := 414,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, 1, -4, 0, -4, 1, 0, -4, -2, 0, -2, -4, 0, 1, 2, 0, -2, -4, 0, -2, -1, 0, 11, -2, 0, -4, -2,                    0, 0, 1, 0, 2, 16, 0, -4, -2, 0, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   finite := ((14111258226468871 : Rat)/9007199254740992, (50202935139032863 : Rat)/9007199254740992),   tail := (56269847422433625861850458326740264892578125 : Rat)/71614993184283990855853657677756284505423872,   box := { reLo := (58643512188283040752339134183619647551181984861511 : Rat)/75093763093203769995667604953110973781559342006272,            reHi := (477549222481975242858999861900066180368458089010783 : Rat)/75093763093203769995667604953110973781559342006272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6935, a6 := -36241 }
def label : String := "414.c1"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 23, 23, 23, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6935, a6 := -36241 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, -5, 2, 0, 2, 6, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (6126422272738560116604948317957045014210198564654513105123145261035026603996563850765327554222864992053683098564186476685601010990282857651961525925712989949086301112163285597581587754736086287248225101882634121657843519643499587807358001843476117426301820419017611755432934354845567959275862620252035957884351430815100107492549663677336374347283415851013018023313152025784667270999398204904078976847482999528118072848380968276569280631556138227498842992119212973617740362307595806799543612451563191230888675542533123363806991603477647 : Rat)/3258102057972274563263852326989679658390333386650599093339905165737293465774651881266673831604186627759159091554747158161141919820251504502038263077286188765473193861149940148332889813393829050980803904399326629350795796050738928801157976700670386093974944655854665468713342050794453992618947796694677234850721732234765463159359810561627586298293884287761521254647937316412367869466725044548643018588734090066583360209312033730519700129722653299546922992357275836298961505062345072054591359662753763513984278921663085163923137856798720,            reHi := (162295293233895897854739021481723873049839467154305799881190529785385524545510891031453097535870862675785772522198860847919364383290954468061070985888179581654740054399787936563512436172242895826800095461482485244867063937814359065546123723407041024147620618629190016615657461796193144807512760101929877423325676480205617260698628287632809600507208575724288470542160309340935382080763367576971992140753636264743117710289881827654052688541532722000586622536847852518342418203026288828088546448193471988824484237355896435894364271449780579 : Rat)/61903939101473216702013194212803913509416334346361382773458198149008575849718385744066802800479545927424022739540196005061696476584778585538726998468437586543990683361848862818324906454482751968635274183587205957665120124964039647222001557312737335785523948461238643905553498965094625859760008137198867462163712912460543800027836400670924139667583801467468903838310809011834989519867775846424217353185947711265083843976928640879874302464730412691391536854788240889680268596184556369037235833592321506765701299511598618114539619279175680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5180, a6 := -142189 }
def label : String := "414.c2"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5180, a6 := -142189 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, -5, 2, 0, 2, 6, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (6126422272738560116604948317957045014210198564654513105123145261035026603996563850765327554222864992053683098564186476685601010990282857651961525925712989949086301112163285597581587754736086287248225101882634121657843519643499587807358001843476117426301820419017611755432934354845567959275862620252035957884351430815100107492549663677336374347283415851013018023313152025784667270999398204904078976847482999528118072848380968276569280631556138227498842992119212973617740362307595806799543612451563191230888675542533123363806991603477647 : Rat)/3258102057972274563263852326989679658390333386650599093339905165737293465774651881266673831604186627759159091554747158161141919820251504502038263077286188765473193861149940148332889813393829050980803904399326629350795796050738928801157976700670386093974944655854665468713342050794453992618947796694677234850721732234765463159359810561627586298293884287761521254647937316412367869466725044548643018588734090066583360209312033730519700129722653299546922992357275836298961505062345072054591359662753763513984278921663085163923137856798720,            reHi := (162295293233895897854739021481723873049839467154305799881190529785385524545510891031453097535870862675785772522198860847919364383290954468061070985888179581654740054399787936563512436172242895826800095461482485244867063937814359065546123723407041024147620618629190016615657461796193144807512760101929877423325676480205617260698628287632809600507208575724288470542160309340935382080763367576971992140753636264743117710289881827654052688541532722000586622536847852518342418203026288828088546448193471988824484237355896435894364271449780579 : Rat)/61903939101473216702013194212803913509416334346361382773458198149008575849718385744066802800479545927424022739540196005061696476584778585538726998468437586543990683361848862818324906454482751968635274183587205957665120124964039647222001557312737335785523948461238643905553498965094625859760008137198867462163712912460543800027836400670924139667583801467468903838310809011834989519867775846424217353185947711265083843976928640879874302464730412691391536854788240889680268596184556369037235833592321506765701299511598618114539619279175680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -320, a6 := -2221 }
def label : String := "414.c3"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1, 0, 2],                kodaira := -10 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -320, a6 := -2221 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, -5, 2, 0, 2, 6, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (6126422272738560116604948317957045014210198564654513105123145261035026603996563850765327554222864992053683098564186476685601010990282857651961525925712989949086301112163285597581587754736086287248225101882634121657843519643499587807358001843476117426301820419017611755432934354845567959275862620252035957884351430815100107492549663677336374347283415851013018023313152025784667270999398204904078976847482999528118072848380968276569280631556138227498842992119212973617740362307595806799543612451563191230888675542533123363806991603477647 : Rat)/3258102057972274563263852326989679658390333386650599093339905165737293465774651881266673831604186627759159091554747158161141919820251504502038263077286188765473193861149940148332889813393829050980803904399326629350795796050738928801157976700670386093974944655854665468713342050794453992618947796694677234850721732234765463159359810561627586298293884287761521254647937316412367869466725044548643018588734090066583360209312033730519700129722653299546922992357275836298961505062345072054591359662753763513984278921663085163923137856798720,            reHi := (162295293233895897854739021481723873049839467154305799881190529785385524545510891031453097535870862675785772522198860847919364383290954468061070985888179581654740054399787936563512436172242895826800095461482485244867063937814359065546123723407041024147620618629190016615657461796193144807512760101929877423325676480205617260698628287632809600507208575724288470542160309340935382080763367576971992140753636264743117710289881827654052688541532722000586622536847852518342418203026288828088546448193471988824484237355896435894364271449780579 : Rat)/61903939101473216702013194212803913509416334346361382773458198149008575849718385744066802800479545927424022739540196005061696476584778585538726998468437586543990683361848862818324906454482751968635274183587205957665120124964039647222001557312737335785523948461238643905553498965094625859760008137198867462163712912460543800027836400670924139667583801467468903838310809011834989519867775846424217353185947711265083843976928640879874302464730412691391536854788240889680268596184556369037235833592321506765701299511598618114539619279175680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1705, a6 := -5137 }
def label : String := "414.c4"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1705, a6 := -5137 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, -5, 2, 0, 2, 6, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (6126422272738560116604948317957045014210198564654513105123145261035026603996563850765327554222864992053683098564186476685601010990282857651961525925712989949086301112163285597581587754736086287248225101882634121657843519643499587807358001843476117426301820419017611755432934354845567959275862620252035957884351430815100107492549663677336374347283415851013018023313152025784667270999398204904078976847482999528118072848380968276569280631556138227498842992119212973617740362307595806799543612451563191230888675542533123363806991603477647 : Rat)/3258102057972274563263852326989679658390333386650599093339905165737293465774651881266673831604186627759159091554747158161141919820251504502038263077286188765473193861149940148332889813393829050980803904399326629350795796050738928801157976700670386093974944655854665468713342050794453992618947796694677234850721732234765463159359810561627586298293884287761521254647937316412367869466725044548643018588734090066583360209312033730519700129722653299546922992357275836298961505062345072054591359662753763513984278921663085163923137856798720,            reHi := (162295293233895897854739021481723873049839467154305799881190529785385524545510891031453097535870862675785772522198860847919364383290954468061070985888179581654740054399787936563512436172242895826800095461482485244867063937814359065546123723407041024147620618629190016615657461796193144807512760101929877423325676480205617260698628287632809600507208575724288470542160309340935382080763367576971992140753636264743117710289881827654052688541532722000586622536847852518342418203026288828088546448193471988824484237355896435894364271449780579 : Rat)/61903939101473216702013194212803913509416334346361382773458198149008575849718385744066802800479545927424022739540196005061696476584778585538726998468437586543990683361848862818324906454482751968635274183587205957665120124964039647222001557312737335785523948461238643905553498965094625859760008137198867462163712912460543800027836400670924139667583801467468903838310809011834989519867775846424217353185947711265083843976928640879874302464730412691391536854788240889680268596184556369037235833592321506765701299511598618114539619279175680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -284, a6 := -1767 }
def label : String := "414.d1"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -284, a6 := -1767 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 2, 0, -2, 1, 0, 2, 6, 0, -2, -2, 0, 1, 0, 0, 0, 2, 0, 6, 1, 0, -1, -2, 0, -2, -6, 0, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (350513956434232314224162363378344789798060257745060181475632639119197143450299545231239598941252580767498151245367037176891179934689161399804751138299867292543770607031183280601390613383155556625837139155878526608751827748091989590436801026420486975777690335874797568495944681028300962282275488583448747939601241316805305323121282815096697876243090140656637170433689618974508357336454738700491314343847382923745510261980183562430961571089711627608767565290996755801879909332629529544674609379183457481174387528207437686471543986787553977 : Rat)/179195613188475100979511877984432381211468336265782950133694784115551140617605853469667060738230264526753750035511093698862805590113832747612104469250740382101025662363246708158308939736660597803944214741962964614293768782790641084063688718536871235168621956072006600779233812793694969594042128818207247916789695272912100473764789580889517246406163635826883669005636552402680232820669877450175366022380374953662084811512161855178583507134745931475080764579650170996442882778428978963002524781451456993269135340691469684015772582123929600,            reHi := (483362896058047072503716183258378177425307518039840337590774680064942490625865568401671152616065860821452801164416587435620206474017357696432339435809859276197136307314159972648666534170167245154104075629867813957438803482086555293726655783440902061402120423765165534282117032088885734942291859724616140100626773350390473054894462928858504952690528723676573687745096988680143358142527664878907123484663974596248818624550905223111524665305487138110062658119786480359737222498347248087594991647682784446073083641959803900572684146573733191 : Rat)/179195613188475100979511877984432381211468336265782950133694784115551140617605853469667060738230264526753750035511093698862805590113832747612104469250740382101025662363246708158308939736660597803944214741962964614293768782790641084063688718536871235168621956072006600779233812793694969594042128818207247916789695272912100473764789580889517246406163635826883669005636552402680232820669877450175366022380374953662084811512161855178583507134745931475080764579650170996442882778428978963002524781451456993269135340691469684015772582123929600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := -39 }
def label : String := "414.d2"
def inputConductor : Nat := 414
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 414 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := -39 },   conductor := 414,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, 1, 2, 0, -2, 1, 0, 2, 6, 0, -2, -2, 0, 1, 0, 0, 0, 2, 0, 6, 1, 0, -1, -2, 0, -2, -6, 0, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/17477931280921955204010009765625,   alphaHi := (674651885226100947931528953856 : Rat)/2184741410115244388580322265625,   geometricUpper := (6614223883381609 : Rat)/9007199254740992,   tail := (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/346310580049104256442907825809500034639574936386886219422005250377713674085465443237261960824357756721691521295865412720205858058590503171176368187117308637294949887107131313641253440638117210552554694407421595407627182089643472712543902812932816054997132201979974082655234812667518136637347522271619656479883602923965042982871535933021888874594310532195248131479946377369170912891663885662483506767219094111212741046277148600161425858824149070400665281576575324847214270042824571980715564904122249068374456400477154386003361792,   box := { reLo := (350513956434232314224162363378344789798060257745060181475632639119197143450299545231239598941252580767498151245367037176891179934689161399804751138299867292543770607031183280601390613383155556625837139155878526608751827748091989590436801026420486975777690335874797568495944681028300962282275488583448747939601241316805305323121282815096697876243090140656637170433689618974508357336454738700491314343847382923745510261980183562430961571089711627608767565290996755801879909332629529544674609379183457481174387528207437686471543986787553977 : Rat)/179195613188475100979511877984432381211468336265782950133694784115551140617605853469667060738230264526753750035511093698862805590113832747612104469250740382101025662363246708158308939736660597803944214741962964614293768782790641084063688718536871235168621956072006600779233812793694969594042128818207247916789695272912100473764789580889517246406163635826883669005636552402680232820669877450175366022380374953662084811512161855178583507134745931475080764579650170996442882778428978963002524781451456993269135340691469684015772582123929600,            reHi := (483362896058047072503716183258378177425307518039840337590774680064942490625865568401671152616065860821452801164416587435620206474017357696432339435809859276197136307314159972648666534170167245154104075629867813957438803482086555293726655783440902061402120423765165534282117032088885734942291859724616140100626773350390473054894462928858504952690528723676573687745096988680143358142527664878907123484663974596248818624550905223111524665305487138110062658119786480359737222498347248087594991647682784446073083641959803900572684146573733191 : Rat)/179195613188475100979511877984432381211468336265782950133694784115551140617605853469667060738230264526753750035511093698862805590113832747612104469250740382101025662363246708158308939736660597803944214741962964614293768782790641084063688718536871235168621956072006600779233812793694969594042128818207247916789695272912100473764789580889517246406163635826883669005636552402680232820669877450175366022380374953662084811512161855178583507134745931475080764579650170996442882778428978963002524781451456993269135340691469684015772582123929600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (128370869468892081983596827456466327386675341973635542154940259833928465515592807159294555541169913846959263318600292663484144311928467062663707970966368671608777131270748104203519069997699540194277865491444918160110943689018177883145371891231341055974242225688450906815427228970175517663955445389227342356319016373541078562874748013920644250252401749923828326976279925770698307902574893402426070449124802742684079172597263583595793564006248620097468794961581483613500631388602827064744729847466062794483544929542273712608169819 : Rat)/692621160098208512885815651619000069279149872773772438844010500755427348170930886474523921648715513443383042591730825440411716117181006342352736374234617274589899774214262627282506881276234421105109388814843190815254364179286945425087805625865632109994264403959948165310469625335036273274695044543239312959767205847930085965743071866043777749188621064390496262959892754738341825783327771324967013534438188222425482092554297200322851717648298140801330563153150649694428540085649143961431129808244498136748912800954308772006723584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N414.C414_d2
