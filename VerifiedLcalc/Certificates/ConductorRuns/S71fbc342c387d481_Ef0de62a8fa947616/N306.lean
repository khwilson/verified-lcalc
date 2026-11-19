module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1017, a6 := 8883 }
def label : String := "306.a1"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1017, a6 := 8883 },   conductor := 306,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, 0, 0, -6, 0, 2, 4, 0, 1, 1, 0, -4, 0, 0, 6, 0, 0, -5, -2, 0, -4, 0, 0, -4,                    -1, 0, -1, 0, 0, -4, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   finite := ((291973515875979 : Rat)/281474976710656, (11544991477827427 : Rat)/4503599627370496),   tail := (432077635811842309374264842275524139404296875 : Rat)/1480381951980999472263263903211659488491732992,   box := { reLo := (36160145057586896249769223411474977879677852288029 : Rat)/48509155802513390707122631580439658118897106681856,            reHi := (2216187037898635965893180597159304813919629756499077 : Rat)/776146492840214251313962105287034529902353706909696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -927, a6 := 11097 }
def label : String := "306.a2"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -927, a6 := 11097 },   conductor := 306,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, 0, 0, -6, 0, 2, 4, 0, 1, 1, 0, -4, 0, 0, 6, 0, 0, -5, -2, 0, -4, 0, 0, -4,                    -1, 0, -1, 0, 0, -4, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   finite := ((291973515875979 : Rat)/281474976710656, (11544991477827427 : Rat)/4503599627370496),   tail := (432077635811842309374264842275524139404296875 : Rat)/1480381951980999472263263903211659488491732992,   box := { reLo := (36160145057586896249769223411474977879677852288029 : Rat)/48509155802513390707122631580439658118897106681856,            reHi := (2216187037898635965893180597159304813919629756499077 : Rat)/776146492840214251313962105287034529902353706909696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -387, a6 := -2835 }
def label : String := "306.a3"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -387, a6 := -2835 },   conductor := 306,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, 0, 0, -6, 0, 2, 4, 0, 1, 1, 0, -4, 0, 0, 6, 0, 0, -5, -2, 0, -4, 0, 0, -4,                    -1, 0, -1, 0, 0, -4, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   finite := ((291973515875979 : Rat)/281474976710656, (11544991477827427 : Rat)/4503599627370496),   tail := (432077635811842309374264842275524139404296875 : Rat)/1480381951980999472263263903211659488491732992,   box := { reLo := (36160145057586896249769223411474977879677852288029 : Rat)/48509155802513390707122631580439658118897106681856,            reHi := (2216187037898635965893180597159304813919629756499077 : Rat)/776146492840214251313962105287034529902353706909696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := -27 }
def label : String := "306.a4"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -27, a6 := -27 },   conductor := 306,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, 0, 0, -6, 0, 2, 4, 0, 1, 1, 0, -4, 0, 0, 6, 0, 0, -5, -2, 0, -4, 0, 0, -4,                    -1, 0, -1, 0, 0, -4, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   finite := ((291973515875979 : Rat)/281474976710656, (11544991477827427 : Rat)/4503599627370496),   tail := (432077635811842309374264842275524139404296875 : Rat)/1480381951980999472263263903211659488491732992,   box := { reLo := (36160145057586896249769223411474977879677852288029 : Rat)/48509155802513390707122631580439658118897106681856,            reHi := (2216187037898635965893180597159304813919629756499077 : Rat)/776146492840214251313962105287034529902353706909696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -249696, a6 := 48087270 }
def label : String := "306.b1"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -249696, a6 := 48087270 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15606, a6 := 754272 }
def label : String := "306.b2"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 2, 2],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15606, a6 := 754272 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -14796, a6 := 835434 }
def label : String := "306.b3"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -14796, a6 := 835434 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1026, a6 := 10692 }
def label : String := "306.b4"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 2, 2, 1, 0, 2, 0],                kodaira := -12 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1026, a6 := 10692 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -306, a6 := -1836 }
def label : String := "306.b5"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0, 1],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -306, a6 := -1836 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 2034, a6 := 60264 }
def label : String := "306.b6"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2, 2, 1, 2, 1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0],                kodaira := -20 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 2034, a6 := 60264 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 0, 1, 2, 0, 0, -1, 0, -2, 4, 0, -2, 0, 0, 1, -1, 0, 4, 2, 0, -4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (2286201119581983956242500748241788316168476974508291781058747348890457559731500424535886540214310946271272511587416244722261616611454533596095511516700466510373453908771261146659106275027543027384006149778674534491886854794301169348202193725439676223580618305953552666506218137387128555876456016530750788596048444222123200761017248958794038317070720501562822914389083035426268850313187389306951763 : Rat)/4536360154715940762980487784097413544806276868583525027535238157458356390064467431088388697084662341943292806547308941605174044919912324098805241102956166544412519812804853362667405749864362567482691230072840778319824750780524038350392700221647373481571579262735279712133001008949155489628211736651063447001762594699578088451314215698143753099671670207693135672453109372761044485087072308518977536,            reHi := (690328286441576626820387411279216788695323447220470086178992197614720732612686760560244359692565838950055584376082979417871406873179203005263007022497195616954254179702510235816475171725640658836168364009182836093254893477318570948392452993713911030392078017179839042820218201620552735532673936908774175424698844538417766911423313823814366504011938503853777645239421148383350458639889102132560211057 : Rat)/385590613150854964853341461648280151308533533829599627340495243383960293155479731642513039252196299065179888556521260036439793818192547548398445493751274156275064184088412535826729488738470818236028754556191466157185103816344543259783379518840026745933584237332498775531305085760678216618397997615340392995149820549464137518361708334342219013472091967653916532158514296684688781232401146224113090560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_b6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6755, a6 := 163235 }
def label : String := "306.c1"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6755, a6 := 163235 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 1, 0, -4, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1608635337391673578063040649715531488911070513844214969674910859830915294739936597167069529112021032519094257808595115362715985663817408450344948654921735136468305941890655617236233633967144401821183468632173593544390976207219086552652959974363527130501441937923056512115304407649601411579148606701098044872626183006799377158598195755972520633366571545832065708654842178163890851407055989646638435593 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (180033299841878530059866379527548557476078406490796790428379706381984766132545931568067833526994340562208737971015509173064133797502696225456162081693663999268653825734819410990205809653116135744516132498271099937192645511412902194058335576043296718996903876569703866269351301126403104391186188393225217932788486885573856577872531078688096024606216561181627061293249860049189361660866526910283221639 : Rat)/66395816809933314803623503021789416428528234167449775403015758486435943527307205127748234566420967004806376532192430872584820112009625834537058528870540255786401426351052853762677484157105670305883026185611578664499253170514942743128474975971384284593911296481852730332128469312801275802740189963711019542480343431512006567332871702491013113549739900312599531205904600819502560190819876515595943936,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2300, a6 := -41857 }
def label : String := "306.c2"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 2, 0, 0, 1],                kodaira := -10 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2300, a6 := -41857 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 1, 0, -4, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1608635337391673578063040649715531488911070513844214969674910859830915294739936597167069529112021032519094257808595115362715985663817408450344948654921735136468305941890655617236233633967144401821183468632173593544390976207219086552652959974363527130501441937923056512115304407649601411579148606701098044872626183006799377158598195755972520633366571545832065708654842178163890851407055989646638435593 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (180033299841878530059866379527548557476078406490796790428379706381984766132545931568067833526994340562208737971015509173064133797502696225456162081693663999268653825734819410990205809653116135744516132498271099937192645511412902194058335576043296718996903876569703866269351301126403104391186188393225217932788486885573856577872531078688096024606216561181627061293249860049189361660866526910283221639 : Rat)/66395816809933314803623503021789416428528234167449775403015758486435943527307205127748234566420967004806376532192430872584820112009625834537058528870540255786401426351052853762677484157105670305883026185611578664499253170514942743128474975971384284593911296481852730332128469312801275802740189963711019542480343431512006567332871702491013113549739900312599531205904600819502560190819876515595943936,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1940, a6 := -55681 }
def label : String := "306.c3"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1, 2, 1, 2, 1, 0, 2, 2, 1],                kodaira := -16 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1940, a6 := -55681 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 1, 0, -4, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1608635337391673578063040649715531488911070513844214969674910859830915294739936597167069529112021032519094257808595115362715985663817408450344948654921735136468305941890655617236233633967144401821183468632173593544390976207219086552652959974363527130501441937923056512115304407649601411579148606701098044872626183006799377158598195755972520633366571545832065708654842178163890851407055989646638435593 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (180033299841878530059866379527548557476078406490796790428379706381984766132545931568067833526994340562208737971015509173064133797502696225456162081693663999268653825734819410990205809653116135744516132498271099937192645511412902194058335576043296718996903876569703866269351301126403104391186188393225217932788486885573856577872531078688096024606216561181627061293249860049189361660866526910283221639 : Rat)/66395816809933314803623503021789416428528234167449775403015758486435943527307205127748234566420967004806376532192430872584820112009625834537058528870540255786401426351052853762677484157105670305883026185611578664499253170514942743128474975971384284593911296481852730332128469312801275802740189963711019542480343431512006567332871702491013113549739900312599531205904600819502560190819876515595943936,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 16285, a6 := 1020323 }
def label : String := "306.c4"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 16285, a6 := 1020323 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 1, 0, -4, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1608635337391673578063040649715531488911070513844214969674910859830915294739936597167069529112021032519094257808595115362715985663817408450344948654921735136468305941890655617236233633967144401821183468632173593544390976207219086552652959974363527130501441937923056512115304407649601411579148606701098044872626183006799377158598195755972520633366571545832065708654842178163890851407055989646638435593 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (180033299841878530059866379527548557476078406490796790428379706381984766132545931568067833526994340562208737971015509173064133797502696225456162081693663999268653825734819410990205809653116135744516132498271099937192645511412902194058335576043296718996903876569703866269351301126403104391186188393225217932788486885573856577872531078688096024606216561181627061293249860049189361660866526910283221639 : Rat)/66395816809933314803623503021789416428528234167449775403015758486435943527307205127748234566420967004806376532192430872584820112009625834537058528870540255786401426351052853762677484157105670305883026185611578664499253170514942743128474975971384284593911296481852730332128469312801275802740189963711019542480343431512006567332871702491013113549739900312599531205904600819502560190819876515595943936,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -23, a6 := -21 }
def label : String := "306.d1"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -23, a6 := -21 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 4, 0, -2, 1, 0, 4, 0, 0, -6, -2, 0, 1, 1, 0, 4, 4, 0, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1812688073151887312085263996292850911788090864265485427608233985268818727334527687182548996468226217779566143085527889805963582078928958753670677717096153302631394307468598823400398076112570442984683110081962709346559995940089743791044026681014030191521192645026773652743425095010664019623519297758475245194299198147446131737460008764145657970697924366101811055753959130976467676572567708244641303817 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (960182009727102697951685847491154250195044465315998476473859733664398108143994017739995306934037253368815389550991255546388988911013555672714281363690890947542022771292760876256651343145160018014657668193056319845011302675030372770060743341645285690905314877164726527654099444239508739790621313194837771395367931675423675918799521508372925946631345476822960891978250887082776913434491383717714310307 : Rat)/331979084049666574018117515108947082142641170837248877015078792432179717636536025638741172832104835024031882660962154362924100560048129172685292644352701278932007131755264268813387420785528351529415130928057893322496265852574713715642374879856921422969556482409263651660642346564006379013700949818555097712401717157560032836664358512455065567748699501562997656029523004097512800954099382577979719680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 67, a6 := -201 }
def label : String := "306.d2"
def inputConductor : Nat := 306
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 306 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 67, a6 := -201 },   conductor := 306,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 4, 0, -2, 1, 0, 4, 0, 0, -6, -2, 0, 1, 1, 0, 4, 4, 0, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15026248615745877933502197265625,   alphaHi := (674651885226100947931528953856 : Rat)/1878281076968234729766845703125,   geometricUpper := (3144614155016689 : Rat)/4503599627370496,   tail := (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/1669620962354045183283212287117193060289391560023380576936046432630974011801423419612951305515149923424104823904051873980557248774351241847186323556480002408690658745971605948718220739736607496313099458988899807994046651004977562881999521612678459139334405323053102580836584839510178685913953528395680326463659401803304412385467138644881764114711693120240388543412995720559824985309927239057408,   box := { reLo := (1812688073151887312085263996292850911788090864265485427608233985268818727334527687182548996468226217779566143085527889805963582078928958753670677717096153302631394307468598823400398076112570442984683110081962709346559995940089743791044026681014030191521192645026773652743425095010664019623519297758475245194299198147446131737460008764145657970697924366101811055753959130976467676572567708244641303817 : Rat)/1128728885768866351661599551370420079284979980846646181851267894269411039964222487171719987629156439081708401047271324833941941904163639187129994990799184348368824247967898513965517230670796395200011445155396837296487303898754026633184074591513532838096492040191496415646183978317621688646583229383087332222165838335704111644658818942347222930345578305314192030500378213931543523243937900765131046912,            reHi := (960182009727102697951685847491154250195044465315998476473859733664398108143994017739995306934037253368815389550991255546388988911013555672714281363690890947542022771292760876256651343145160018014657668193056319845011302675030372770060743341645285690905314877164726527654099444239508739790621313194837771395367931675423675918799521508372925946631345476822960891978250887082776913434491383717714310307 : Rat)/331979084049666574018117515108947082142641170837248877015078792432179717636536025638741172832104835024031882660962154362924100560048129172685292644352701278932007131755264268813387420785528351529415130928057893322496265852574713715642374879856921422969556482409263651660642346564006379013700949818555097712401717157560032836664358512455065567748699501562997656029523004097512800954099382577979719680,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1073851331003285576142254851692478671519550738300115331592906949999804010249634575633152302481290391495483877305191993920336057166289098881162642219684302265616754835072095064760831303460553995542071093251408636975746252322665053483962131617859227843783815642910389959956685431616859559495008654938009827766365590459026432117902932300965471796344786296685702949961474761312780258886635644140625 : Rat)/3339241924708090366566424574234386120578783120046761153872092865261948023602846839225902611030299846848209647808103747961114497548702483694372647112960004817381317491943211897436441479473214992626198917977799615988093302009955125763999043225356918278668810646106205161673169679020357371827907056791360652927318803606608824770934277289763528229423386240480777086825991441119649970619854478114816, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N306.C306_d2
