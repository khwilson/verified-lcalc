module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -110, a6 := -134 }
def label : String := "549.a1"
def inputConductor : Nat := 549
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 549 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -110, a6 := -134 },   conductor := 549,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, -2, 3, 0, 0, 4, 0, -2, 2, 0, -1, -2, 0, -4, 0, 0, -4, 0, 0, -5, 2, 0, 2, -6, 0,                    -6, -5, 0, 2, 0, 0, 2, 4, 0, 0, -4, 0, -2, -4, 0, 0, 4, 0, -3, 5, 0, 2, 6, 0, 0, -6, 0, 6, -12, 0,                    -1, 6, 0, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5031715039742051982879638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/20126860158968207836151123046875,   finite := ((18440485497192757 : Rat)/9007199254740992, (13223682198254473 : Rat)/4503599627370496),   tail := (620784073541531580313649875148105621337890625 : Rat)/338177911899958336396491621265137408218759168,   box := { reLo := (300183443028363937767043915791241248648986747598187 : Rat)/1418420968593642850181150393038850891841574453379072,            reHi := (3384295923501965016100098017893392250678161071246743 : Rat)/709210484296821425090575196519425445920787226689536,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 25, a6 := -26 }
def label : String := "549.a2"
def inputConductor : Nat := 549
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 549 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 25, a6 := -26 },   conductor := 549,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, -2, 3, 0, 0, 4, 0, -2, 2, 0, -1, -2, 0, -4, 0, 0, -4, 0, 0, -5, 2, 0, 2, -6, 0,                    -6, -5, 0, 2, 0, 0, 2, 4, 0, 0, -4, 0, -2, -4, 0, 0, 4, 0, -3, 5, 0, 2, 6, 0, 0, -6, 0, 6, -12, 0,                    -1, 6, 0, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5031715039742051982879638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/20126860158968207836151123046875,   finite := ((18440485497192757 : Rat)/9007199254740992, (13223682198254473 : Rat)/4503599627370496),   tail := (620784073541531580313649875148105621337890625 : Rat)/338177911899958336396491621265137408218759168,   box := { reLo := (300183443028363937767043915791241248648986747598187 : Rat)/1418420968593642850181150393038850891841574453379072,            reHi := (3384295923501965016100098017893392250678161071246743 : Rat)/709210484296821425090575196519425445920787226689536,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12, a6 := 9 }
def label : String := "549.b1"
def inputConductor : Nat := 549
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 61, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 549 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12, a6 := 9 },   conductor := 549,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 0, 0, -2, -3, 0, 0, -4, 0, -2, -2, 0, -1, 2, 0, -4, 0, 0, -4, 0, 0, -5, -2, 0, 2, 6, 0,                    -6, 5, 0, 2, 0, 0, 2, -4, 0, 0, 4, 0, -2, 4, 0, 0, -4, 0, -3, -5, 0, 2, -6, 0, 0, 6, 0, 6, 12, 0, -1,                    -6, 0, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5031715039742051982879638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/20126860158968207836151123046875,   finite := ((27106153365295911 : Rat)/9007199254740992, (53489745214263659 : Rat)/9007199254740992),   tail := (620784073541531580313649875148105621337890625 : Rat)/338177911899958336396491621265137408218759168,   box := { reLo := (1664821291415691071712205696395016278514119588495801 : Rat)/1418420968593642850181150393038850891841574453379072,            reHi := (11027127592442014320556775494564757231160291626798069 : Rat)/1418420968593642850181150393038850891841574453379072,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := 0 }
def label : String := "549.b2"
def inputConductor : Nat := 549
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 549 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := 0 },   conductor := 549,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 0, 0, -2, -3, 0, 0, -4, 0, -2, -2, 0, -1, 2, 0, -4, 0, 0, -4, 0, 0, -5, -2, 0, 2, 6, 0,                    -6, 5, 0, 2, 0, 0, 2, -4, 0, 0, 4, 0, -2, 4, 0, 0, -4, 0, -3, -5, 0, 2, -6, 0, 0, 6, 0, 6, 12, 0, -1,                    -6, 0, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/5031715039742051982879638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/20126860158968207836151123046875,   finite := ((27106153365295911 : Rat)/9007199254740992, (53489745214263659 : Rat)/9007199254740992),   tail := (620784073541531580313649875148105621337890625 : Rat)/338177911899958336396491621265137408218759168,   box := { reLo := (1664821291415691071712205696395016278514119588495801 : Rat)/1418420968593642850181150393038850891841574453379072,            reHi := (11027127592442014320556775494564757231160291626798069 : Rat)/1418420968593642850181150393038850891841574453379072,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := -27 }
def label : String := "549.c1"
def inputConductor : Nat := 549
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 549 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := -27 },   conductor := 549,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 0, -1, 3, 0, 1, -3, 0, 3, 5, 0, 1, 1, 0, -1, -4, 0, -4, -3, 0, 5, 9, 0, 4, 1, 0, -1, 6, 0, 0,                    5],   alphaLo := (1349303770452201895858762940416 : Rat)/5031715039742051982879638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/20126860158968207836151123046875,   geometricUpper := (6888575815294617 : Rat)/9007199254740992,   tail := (599908279189831949596061939942963239257213388436130445614790198071819870697937229340919794842814717036181847571928653123330404819559630872957651299270254870865613814084121477137851496444559674206968403249012417007862299864451379146004771047619745661973937927071720432746541683584580783660752675471386311388098675265420962164531011326392114346408061762275560972800726386424992165807505187283313610667386742569870943839408657627772163514855790294042985799646151183787882445632754747731723156634526648588246063557736029439962033553 : Rat)/361200737350594870512854120840728674457785769666353207795873355049918066173636294271572980831993059716815553661020925356219732852051353115226204972272232015287359561998730508027093363146338975410689882281912166042139094052909477700021596563540806249133863105891802114167285449399635301321893215582113455520798373405971384170188166939389487240057662118743600635711987628982013168966960431065066645744497218251071692268105067053796989214290947363453699175852262447466572700972715749761299159986200591487450473378910943005923868672,   box := { reLo := (50015903808705406125334657567072005256339088281637754544539307442891181322771018581098441485390196318210493644616220361590877374082525612106666366107375113500665414694074929886455515221611490336523895957743007725140558908560297009905270961853224386910269351687979759290301525063812795790599598014193439051482551390320829423522871943491370370413045447347908076266674578476349678623989536219962839540322300611122737736865080504064089761684422065661353829333111013600022741481711516549072229033438242252338757753921677046660058096254424823 : Rat)/77895265503605059007657964452695473780213683826691490242191502236794707492608891251036116517988842195228910155980293188849004800844174362063946274256733239543129555427965067879244886270860025616655893367626136403248773050414723655955523138031040633958768249997832175017592458648610935781042086254484331075827178687320836857986518382462599531005748047308764304622984753102289413034546333151318112249066065422426365590386756574888214230469372046920758232548932061218590535159533116698168376378913628672278465252661178424611383434754916352,            reHi := (7719101816043314216457603399045076083777736163840692664506003534646349057209279758361271080307120516443721149930765134659085032436430786969222520580827904491424863517608592856661914462688083219320259508361184509857142295300456192626680527864047537973043326057526169932955159565636451124236093983223850822977978258221050492522867522667845115625098608490310343481344022797107080518258141221423369856833389422698130597875465167622504997228420485341183222223418944649217232117108353688595177685695734698507955162931565720968300630930205458913 : Rat)/1947381637590126475191449111317386844505342095667287256054787555919867687315222281275902912949721054880722753899507329721225120021104359051598656856418330988578238885699126696981122156771500640416397334190653410081219326260368091398888078450776015848969206249945804375439811466215273394526052156362108276895679467183020921449662959561564988275143701182719107615574618827557235325863658328782952806226651635560659139759668914372205355761734301173018955813723301530464763378988327917454209409472840716806961631316529460615284585868872908800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (599908279189831949596061939942963239257213388436130445614790198071819870697937229340919794842814717036181847571928653123330404819559630872957651299270254870865613814084121477137851496444559674206968403249012417007862299864451379146004771047619745661973937927071720432746541683584580783660752675471386311388098675265420962164531011326392114346408061762275560972800726386424992165807505187283313610667386742569870943839408657627772163514855790294042985799646151183787882445632754747731723156634526648588246063557736029439962033553 : Rat)/722401474701189741025708241681457348915571539332706415591746710099836132347272588543145961663986119433631107322041850712439465704102706230452409944544464030574719123997461016054186726292677950821379764563824332084278188105818955400043193127081612498267726211783604228334570898799270602643786431164226911041596746811942768340376333878778974480115324237487201271423975257964026337933920862130133291488994436502143384536210134107593978428581894726907398351704524894933145401945431499522598319972401182974900946757821886011847737344, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N549.C549_c1
