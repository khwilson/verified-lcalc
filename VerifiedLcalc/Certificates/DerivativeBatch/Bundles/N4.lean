module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C128_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 7 },   conductor := 128,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -2, 0, -4, 0, 1, 0, 2, 0, -2, 0, 4, 0, -2, 0, -2, 0, 8, 0, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/4859200799961679553985595703125,   alphaHi := (5397215081808807583452231630848 : Rat)/9718401599923359012603759765625,   finite := ((3384848310856777 : Rat)/9007199254740992, (1486064855635603 : Rat)/1125899906842624),   tail := (514795891812430791746478377138805389404296875 : Rat)/1376232371681568624024026159846399463309443072,   box := { reLo := (2499279281604416328201018577409335481491170622907 : Rat)/1443084235368372501504617254587098163639162578665472,            reHi := (305564516151626033146418314194316937696733090211673 : Rat)/180385529421046562688077156823387270454895322333184,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C128_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C128_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C128_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 1 },   conductor := 128,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -2, 0, -4, 0, 1, 0, 2, 0, -2, 0, 4, 0, -2, 0, -2, 0, 8, 0, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/4859200799961679553985595703125,   alphaHi := (5397215081808807583452231630848 : Rat)/9718401599923359012603759765625,   finite := ((3384848310856777 : Rat)/9007199254740992, (1486064855635603 : Rat)/1125899906842624),   tail := (514795891812430791746478377138805389404296875 : Rat)/1376232371681568624024026159846399463309443072,   box := { reLo := (2499279281604416328201018577409335481491170622907 : Rat)/1443084235368372501504617254587098163639162578665472,            reHi := (305564516151626033146418314194316937696733090211673 : Rat)/180385529421046562688077156823387270454895322333184,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C128_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C128_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C128_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C129_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -19, a6 := 39 },   conductor := 129,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -1, -2, -2, 0, -2, 0, 1, 0, -5, 2, 3, 0, 2, 4, -3, 0, 2, 4, 2, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9756290248877453708648681640625,   alphaHi := (42165742826631309245720559616 : Rat)/76221017569355106353759765625,   finite := ((1756070474791159 : Rat)/4503599627370496, (12207119353345333 : Rat)/9007199254740992),   tail := (1051594356032638556982268341555500030517578125 : Rat)/2747489076733091924630232438739776349075931136,   box := { reLo := (5170266230631160459378176833008419097534064700911 : Rat)/720237776531119649490267652420999931252160891715584,            reHi := (2503560796708359994761695701881484414793353401049757 : Rat)/1440475553062239298980535304841999862504321783431168,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 43] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C129_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C129_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C130_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -208, a6 := -1122 },   conductor := 130,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -2, 1, 1, 2, -4, -1, 1, -1, -6, -2, 1, 4, -2, 1, -6, -1, 2, 1, 8, 6, 6, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/9794032325007390308380126953125,   finite := ((249672690922753 : Rat)/562949953421312, (3819046453622279 : Rat)/4503599627370496),   tail := (67113789992662492119772598906421661376953125 : Rat)/171405364950912970459821899133020529382916096,   box := { reLo := (583652145647666026147384185243675185617617597139 : Rat)/11233221997423032432054887981581633413638789267456,            reHi := (111393012426559950810296644186675759308622786452677 : Rat)/89865775979384259456439103852653067309110314139648,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 13, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C130_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C130_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C130_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -33, a6 := 68 },   conductor := 130,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -2, 1, 1, 2, -4, -1, 1, -1, -6, -2, 1, 4, -2, 1, -6, -1, 2, 1, 8, 6, 6, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/9794032325007390308380126953125,   finite := ((249672690922753 : Rat)/562949953421312, (3819046453622279 : Rat)/4503599627370496),   tail := (67113789992662492119772598906421661376953125 : Rat)/171405364950912970459821899133020529382916096,   box := { reLo := (583652145647666026147384185243675185617617597139 : Rat)/11233221997423032432054887981581633413638789267456,            reHi := (111393012426559950810296644186675759308622786452677 : Rat)/89865775979384259456439103852653067309110314139648,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C130_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C130_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C130_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C130_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -13, a6 := 156 },   conductor := 130,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -2, 1, 1, 2, -4, -1, 1, -1, -6, -2, 1, 4, -2, 1, -6, -1, 2, 1, 8, 6, 6, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/9794032325007390308380126953125,   finite := ((249672690922753 : Rat)/562949953421312, (3819046453622279 : Rat)/4503599627370496),   tail := (67113789992662492119772598906421661376953125 : Rat)/171405364950912970459821899133020529382916096,   box := { reLo := (583652145647666026147384185243675185617617597139 : Rat)/11233221997423032432054887981581633413638789267456,            reHi := (111393012426559950810296644186675759308622786452677 : Rat)/89865775979384259456439103852653067309110314139648,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 5, 5, 5, 5, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C130_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C130_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C130_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C130_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 112, a6 := -4194 },   conductor := 130,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -2, 1, 1, 2, -4, -1, 1, -1, -6, -2, 1, 4, -2, 1, -6, -1, 2, 1, 8, 6, 6, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/4897016162503695201873779296875,   alphaHi := (5397215081808807583452231630848 : Rat)/9794032325007390308380126953125,   finite := ((249672690922753 : Rat)/562949953421312, (3819046453622279 : Rat)/4503599627370496),   tail := (67113789992662492119772598906421661376953125 : Rat)/171405364950912970459821899133020529382916096,   box := { reLo := (583652145647666026147384185243675185617617597139 : Rat)/11233221997423032432054887981581633413638789267456,            reHi := (111393012426559950810296644186675759308622786452677 : Rat)/89865775979384259456439103852653067309110314139648,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 5, 13, 13, 13, 13, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C130_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C130_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C130_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C131_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 1, a6 := 0 },   conductor := 131,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -1, -2, -2, 0, -1, 0, -2, 0, 0, 2, -3, 0, 2, 4, 4, 0, -2, 4, 1, 0, -2, 0, -1, 0, 5, 2, 0, 0,                    -2, 0, 0, 0, 2, 4, -8, 0, 3, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2457907379080806255340576171875,   alphaHi := (5397215081808807583452231630848 : Rat)/9831629516323224925994873046875,   finite := ((1932708470949367 : Rat)/4503599627370496, (1507509658493425 : Rat)/1125899906842624),   tail := (274067435058218426176676926241397857666015625 : Rat)/684363855467062187556122810889130774976528384,   box := { reLo := (20578927889042357086787617214537441295613971398993 : Rat)/717607514110230200378849032550881191501788226781184,            reHi := (312053044708687721977378811717640400868167778205575 : Rat)/179401878527557550094712258137720297875447056695296,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [131] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C131_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C131_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C135_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 4 },   conductor := 135,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, -1, 0, -3, 0, 0, 2, -2, 0, -5, 6, 0, -4, -8, 0, 1, -2, 0, 4, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9980602085948100757598876953125,   alphaHi := (1349303770452201895863057907712 : Rat)/2495150521487025165557861328125,   finite := ((1193120884383025 : Rat)/4503599627370496, (10542179491052809 : Rat)/9007199254740992),   tail := (15706820259044158125934261243915557861328125 : Rat)/1517057543232069378345130828463855427550969856,   box := { reLo := (202480681214386035146396018380700433962347374156325 : Rat)/795375065226055190233811951793657834399842883862528,            reHi := (1878310853934345673963202030408640082687188232591837 : Rat)/1590750130452110380467623903587315668799685767725056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C135_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C135_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C136_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 0 },   conductor := 136,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -2, 0, -2, 0, -2, 0, 1, 0, -6, 0, 2, 0, 4, 0, 1, 0, 0, 0, 4, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/10017499077163918590545654296875,   finite := ((5179071432341373 : Rat)/9007199254740992, (4696475801775889 : Rat)/4503599627370496),   tail := (151478215419012051886726234538555145263671875 : Rat)/338988629737449005890735749252773598195613696,   box := { reLo := (91095422192045621456107357822950286666959692304573 : Rat)/710910682831150657601768258016952657003127653793792,            reHi := (529514889036050575566746684135307580728405677233489 : Rat)/355455341415575328800884129008476328501563826896896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 17] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C136_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C136_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C136_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 16 },   conductor := 136,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -2, 0, -2, 0, -2, 0, 1, 0, -6, 0, 2, 0, 4, 0, 1, 0, 0, 0, 4, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/10017499077163918590545654296875,   finite := ((5179071432341373 : Rat)/9007199254740992, (4696475801775889 : Rat)/4503599627370496),   tail := (151478215419012051886726234538555145263671875 : Rat)/338988629737449005890735749252773598195613696,   box := { reLo := (91095422192045621456107357822950286666959692304573 : Rat)/710910682831150657601768258016952657003127653793792,            reHi := (529514889036050575566746684135307580728405677233489 : Rat)/355455341415575328800884129008476328501563826896896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C136_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C136_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C136_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C138_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -31, a6 := 55 },   conductor := 138,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -1, 1, -2, 1, -2, -1, 1, 2, -6, -1, -2, 2, 2, 1, 0, -1, 0, -2, 2, 6, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/10090888329918071460723876953125,   alphaHi := (1349303770452201895863057907712 : Rat)/2522722082479517841339111328125,   finite := ((4497851339447107 : Rat)/9007199254740992, (4129645677668513 : Rat)/4503599627370496),   tail := (18523174027828813771825296759319305419921875 : Rat)/39728139037095146988473507718179149907492864,   box := { reLo := (689722602421063708516723509967124150498445940497 : Rat)/20828986559480540424292798414548710146699618680832,            reHi := (14405470417451718182884745285715382115648591062523 : Rat)/10414493279740270212146399207274355073349809340416,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 23, 23] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C138_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C138_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C138_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1, a6 := 1 },   conductor := 138,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -1, 1, -2, 1, -2, -1, 1, 2, -6, -1, -2, 2, 2, 1, 0, -1, 0, -2, 2, 6, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/10090888329918071460723876953125,   alphaHi := (1349303770452201895863057907712 : Rat)/2522722082479517841339111328125,   finite := ((4497851339447107 : Rat)/9007199254740992, (4129645677668513 : Rat)/4503599627370496),   tail := (18523174027828813771825296759319305419921875 : Rat)/39728139037095146988473507718179149907492864,   box := { reLo := (689722602421063708516723509967124150498445940497 : Rat)/20828986559480540424292798414548710146699618680832,            reHi := (14405470417451718182884745285715382115648591062523 : Rat)/10414493279740270212146399207274355073349809340416,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 23] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C138_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C138_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C138_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C141_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -12, a6 := 2 },   conductor := 141,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 1, 2, -3, -2, -3, 0, 1, 6, -5, 2, 2, 6, -3, -4, -6, -2, -6, -6, -3, 10, 9, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2549995546267212009429931640625,   alphaHi := (5397215081808807583452231630848 : Rat)/10199982185068847942352294921875,   finite := ((2564994491503975 : Rat)/9007199254740992, (2909330936783417 : Rat)/2251799813685248),   tail := (2416908786803428486959130865192413330078125 : Rat)/189577903109790173983893991865006226327732224,   box := { reLo := (216298130417341968028919974554523108783317184074175 : Rat)/795147357325005365901342505655363075111312578052096,            reHi := (259367401340817990157641733341873532424493048721121 : Rat)/198786839331251341475335626413840768777828144513024,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 47] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C141_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C141_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C141_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := 0 },   conductor := 141,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, -2, -1, 0, -3, 0, 1, 0, -3, 2, -4, 0, 1, 4, 8, 0, -6, 2, 3, 0, 3, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2549995546267212009429931640625,   alphaHi := (5397215081808807583452231630848 : Rat)/10199982185068847942352294921875,   finite := ((2742747342345687 : Rat)/4503599627370496, (4966734530906425 : Rat)/4503599627370496),   tail := (55533938348762509279854740339374542236328125 : Rat)/111905811223973098712893163981094947005661184,   box := { reLo := (13231006980335207798534998057676502415198097078623 : Rat)/117341747909988815955970662314640615151408181673984,            reHi := (187640330025252400160281875075639418877824557803825 : Rat)/117341747909988815955970662314640615151408181673984,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 47] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C141_d1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C141_d1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C142_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1, a6 := -1 },   conductor := 142,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -1, 1, -2, 1, -1, -1, -2, 2, -2, -1, -3, 1, 2, 1, -6, 2, 5, -2, 1, 2, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/10236088429603871631622314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/2559022107400967884063720703125,   finite := ((4593799448964225 : Rat)/9007199254740992, (8459638413117621 : Rat)/9007199254740992),   tail := (38790111860382583501254536601467132568359375 : Rat)/76583849087857302202261948772010919014170624,   box := { reLo := (140896131005168392527740820173174830346947133975 : Rat)/40151993070574529257019512597780060708101488115712,            reHi := (58048284741130089114950313379341157606387429313731 : Rat)/40151993070574529257019512597780060708101488115712,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 71] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C142_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C142_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C142_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -12, a6 := 15 },   conductor := 142,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 1, -3, 1, -4, -3, -3, 1, 6, -4, 0, -3, 1, -3, 12, 1, 0, 6, -5, -4, 9, 0, -7, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/10236088429603871631622314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/2559022107400967884063720703125,   finite := ((6141724858456149 : Rat)/9007199254740992, (5693603055880199 : Rat)/4503599627370496),   tail := (38790111860382583501254536601467132568359375 : Rat)/76583849087857302202261948772010919014170624,   box := { reLo := (7041186505171339041279058070401053891198277960739 : Rat)/40151993070574529257019512597780060708101488115712,            reHi := (35549349298105294992187430599413908710699452320289 : Rat)/20075996535287264628509756298890030354050744057856,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 71] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C142_d1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C142_d1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C143_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := -2 },   conductor := 143,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, -2, -1, 0, -2, 0, -2, 0, -1, 2, -1, 0, 1, 4, -4, 0, 2, 2, 2, 0, 7, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5136033880866116237640380859375,   alphaHi := (5397215081808807583452231630848 : Rat)/10272067761732232379913330078125,   finite := ((5551077930801339 : Rat)/9007199254740992, (10056588920741871 : Rat)/9007199254740992),   tail := (230450829760541831302025229492473602294921875 : Rat)/445851193862485084837715276185197658268237824,   box := { reLo := (46477441279901512485238482269963473913477164585683 : Rat)/467508861455549160318792133441169819716275744538624,            reHi := (763621497732889743250736736856211979857959745067687 : Rat)/467508861455549160318792133441169819716275744538624,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [11, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C143_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C143_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C145_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3, a6 := 2 },   conductor := 145,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, 0, -1, -1, 0, -2, 3, -3, 1, -6, 0, 2, 2, 0, -1, -2, 3, -2, 1, 0, 6, 2, 0, 1, -2, 0, 2, -1, 0,                    2, -5, 0, 2, 2, 3, 10, 2, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/5171825490760380458831787109375,   alphaHi := (5397215081808807583452231630848 : Rat)/10343650981520760822296142578125,   finite := ((4998041740346633 : Rat)/9007199254740992, (4324990104371073 : Rat)/4503599627370496),   tail := (716719149891558030807005489719295501708984375 : Rat)/1332192497087250683713785706639566989523156992,   box := { reLo := (23599890276888663483419212059865694699771046506733 : Rat)/1396905079825760972925866561125290595606233866043392,            reHi := (1046519664046432370581957702434056414078337805199173 : Rat)/698452539912880486462933280562645297803116933021696,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 29] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C145_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C145_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C145_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 2, a6 := 6 },   conductor := 145,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, 0, -1, -1, 0, -2, 3, -3, 1, -6, 0, 2, 2, 0, -1, -2, 3, -2, 1, 0, 6, 2, 0, 1, -2, 0, 2, -1, 0,                    2, -5, 0, 2, 2, 3, 10, 2, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/5171825490760380458831787109375,   alphaHi := (5397215081808807583452231630848 : Rat)/10343650981520760822296142578125,   finite := ((4998041740346633 : Rat)/9007199254740992, (4324990104371073 : Rat)/4503599627370496),   tail := (716719149891558030807005489719295501708984375 : Rat)/1332192497087250683713785706639566989523156992,   box := { reLo := (23599890276888663483419212059865694699771046506733 : Rat)/1396905079825760972925866561125290595606233866043392,            reHi := (1046519664046432370581957702434056414078337805199173 : Rat)/698452539912880486462933280562645297803116933021696,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 29, 29] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C145_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C145_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C145_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C148_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 1 },   conductor := 148,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, 0, -4, 0, -3, 0, -2, 0, 5, 0, 0, 0, 4, 0, -6, 0, 2, 0, 3, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10450106454786025142669677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/5225053227393012523651123046875,   finite := ((90508491133107 : Rat)/140737488355328, (10535240677867491 : Rat)/9007199254740992),   tail := (755550960712462001394709047292613983154296875 : Rat)/1324069530165773016611212675526082479276425216,   box := { reLo := (786105566396087780245160452648541694675704856843 : Rat)/10846777591118012552079054237909667670232475369472,            reHi := (1208087733526218048267211998295505510199791826236859 : Rat)/694193765831552803333059471226218730894878423646208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C148_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C148_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C152_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 3 },   conductor := 152,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -2, 0, -1, 0, -3, 0, 1, 0, -3, 0, -4, 0, 2, 0, 5, 0, -1, 0, 6, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/10590382616702480220794677734375,   finite := ((2836583284652813 : Rat)/4503599627370496, (5186563170542687 : Rat)/4503599627370496),   tail := (202191486630892536251637781391143798828125 : Rat)/328273457237915750689976781390482564448256,   box := { reLo := (9585869381151888462061084747403574472871025511 : Rat)/688439337393409492390986187046613290997788966912,            reHi := (1216866321407848851639017229449497178111659712989 : Rat)/688439337393409492390986187046613290997788966912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C152_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C152_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C153_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 2 },   conductor := 153,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, -1, 0, -2, 0, 0, 2, -3, 0, -5, 4, 0, -4, -1, 0, -1, -2, 0, 6, -7, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1328145286498610401153564453125,   alphaHi := (5397215081808807583452231630848 : Rat)/10625162291988883113861083984375,   finite := ((2247876345188213 : Rat)/9007199254740992, (3008981849122545 : Rat)/2251799813685248),   tail := (3532889522042044131354036734104156494140625 : Rat)/189448977249726516025039765358759710344347648,   box := { reLo := (366975026866179699187883135814811434279735315366301 : Rat)/1589213206148873850139776776006614576272277434793984,            reHi := (538308074555138025137354669520248101003960539849465 : Rat)/397303301537218462534944194001653644068069358698496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 17] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C153_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C153_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C153_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -534, a6 := 4752 },   conductor := 153,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, 0, -2, -3, 0, -4, 0, 0, 0, 3, 0, -1, 0, 0, 4, 1, 0, -1, 6, 0, 0, -9, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1328145286498610401153564453125,   alphaHi := (5397215081808807583452231630848 : Rat)/10625162291988883113861083984375,   finite := ((6105026339867423 : Rat)/9007199254740992, (11132606367096029 : Rat)/9007199254740992),   tail := (102790436535887518507593898477077484130859375 : Rat)/163790629779451054044591498242803458667184128,   box := { reLo := (34501853243668988942919778222518951799592115418153 : Rat)/686987693646470673783446299445783517901605056806912,            reHi := (1280228864082103852409814782595454827908740160365819 : Rat)/686987693646470673783446299445783517901605056806912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C153_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C153_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C153_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 27 },   conductor := 153,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, 0, -2, -3, 0, -4, 0, 0, 0, 3, 0, -1, 0, 0, 4, 1, 0, -1, 6, 0, 0, -9, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1328145286498610401153564453125,   alphaHi := (5397215081808807583452231630848 : Rat)/10625162291988883113861083984375,   finite := ((6105026339867423 : Rat)/9007199254740992, (11132606367096029 : Rat)/9007199254740992),   tail := (102790436535887518507593898477077484130859375 : Rat)/163790629779451054044591498242803458667184128,   box := { reLo := (34501853243668988942919778222518951799592115418153 : Rat)/686987693646470673783446299445783517901605056806912,            reHi := (1280228864082103852409814782595454827908740160365819 : Rat)/686987693646470673783446299445783517901605056806912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0],                kodaira := -7 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C153_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C153_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C153_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C154_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -469, a6 := 4029 },   conductor := 154,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -4, 0, -1, -1, -3, 4, -1, 0, 2, 1, 0, 1, -4, 3, -6, -4, 0, 1, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10659828492712762165069580078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2664957123178190517425537109375,   finite := ((3578127687806123 : Rat)/9007199254740992, (6918079984813663 : Rat)/4503599627370496),   tail := (1164590992786222002915545473392486572265625 : Rat)/60619827542549197790074893577646902547054592,   box := { reLo := (24029959486532649211041005590995439790953452461123 : Rat)/63564496285256067621925571608074678485180315860992,            reHi := (49432002376545766567818393308620321721608506368663 : Rat)/31782248142628033810962785804037339242590157930496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 7, 7, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C154_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C154_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C154_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -29, a6 := 69 },   conductor := 154,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -4, 0, -1, -1, -3, 4, -1, 0, 2, 1, 0, 1, -4, 3, -6, -4, 0, 1, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10659828492712762165069580078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2664957123178190517425537109375,   finite := ((3578127687806123 : Rat)/9007199254740992, (6918079984813663 : Rat)/4503599627370496),   tail := (1164590992786222002915545473392486572265625 : Rat)/60619827542549197790074893577646902547054592,   box := { reLo := (24029959486532649211041005590995439790953452461123 : Rat)/63564496285256067621925571608074678485180315860992,            reHi := (49432002376545766567818393308620321721608506368663 : Rat)/31782248142628033810962785804037339242590157930496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C154_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C154_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C154_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C155_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -840, a6 := -9114 },   conductor := 155,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 2, -2, -6, 4, -1, -4, -7, 4, -5, 2, 2, -4, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10694382322369030666351318359375,   alphaHi := (2698607540904403791726115815424 : Rat)/5347191161184515285491943359375,   finite := ((1526949000301413 : Rat)/9007199254740992, (1482531237121117 : Rat)/1125899906842624),   tail := (14991890819739624800423235102367401123046875 : Rat)/757698976900476447685161413964591466666786816,   box := { reLo := (118968629684400379762752013893276575236615360440549 : Rat)/794504962402393991607915814809335461751592652374016,            reHi := (132735791856773155086984300784962454532401770098141 : Rat)/99313120300299248950989476851166932718949081546752,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 31, 31, 31, 31, 31] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C155_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C155_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C155_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 10, a6 := 6 },   conductor := 155,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 2, -2, -6, 4, -1, -4, -7, 4, -5, 2, 2, -4, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10694382322369030666351318359375,   alphaHi := (2698607540904403791726115815424 : Rat)/5347191161184515285491943359375,   finite := ((1526949000301413 : Rat)/9007199254740992, (1482531237121117 : Rat)/1125899906842624),   tail := (14991890819739624800423235102367401123046875 : Rat)/757698976900476447685161413964591466666786816,   box := { reLo := (118968629684400379762752013893276575236615360440549 : Rat)/794504962402393991607915814809335461751592652374016,            reHi := (132735791856773155086984300784962454532401770098141 : Rat)/99313120300299248950989476851166932718949081546752,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 31] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C155_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C155_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C155_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C155_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := 1 },   conductor := 155,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, -2, -1, 0, 0, 0, -2, 0, -4, 2, -6, 0, 1, 4, 5, 0, -1, 2, 0, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10694382322369030666351318359375,   alphaHi := (2698607540904403791726115815424 : Rat)/5347191161184515285491943359375,   finite := ((2947323574168869 : Rat)/4503599627370496, (1349950604695581 : Rat)/1125899906842624),   tail := (67979181727454317924804889395191192626953125 : Rat)/104380694402426598373994476662458239632277504,   box := { reLo := (86884468542058189420596344399164706030467019739 : Rat)/27362772753429718204152408090203452770163754008576,            reHi := (12657054228549768305879549857472757141814050218211 : Rat)/6840693188357429551038102022550863192540938502144,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 31] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C155_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C155_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C156_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -24 },   conductor := 156,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, 0, -4, 0, -2, 0, 1, 0, -4, 0, 1, 0, 4, 0, 2, 0, -2, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10728824866682632350921630859375,   alphaHi := (2698607540904403791726115815424 : Rat)/5364412433341316127777099609375,   finite := ((6029657669187101 : Rat)/9007199254740992, (10788731637457 : Rat)/8796093022208),   tail := (863597541934329806988924811442089080810546875 : Rat)/1301961408752116276953153772992228093610426368,   box := { reLo := (4178521756594528360037997386503989072375471978077 : Rat)/682602743071829538611215085334549282742823219625984,            reHi := (1259776563031865575926558241552957365319159158289 : Rat)/666604241281083533800014731772020783928538300416,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C156_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C156_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C156_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 6 },   conductor := 156,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 0, -1, 0, -4, 0, -2, 0, 1, 0, -4, 0, 1, 0, 4, 0, 2, 0, -2, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10728824866682632350921630859375,   alphaHi := (2698607540904403791726115815424 : Rat)/5364412433341316127777099609375,   finite := ((6029657669187101 : Rat)/9007199254740992, (10788731637457 : Rat)/8796093022208),   tail := (863597541934329806988924811442089080810546875 : Rat)/1301961408752116276953153772992228093610426368,   box := { reLo := (4178521756594528360037997386503989072375471978077 : Rat)/682602743071829538611215085334549282742823219625984,            reHi := (1259776563031865575926558241552957365319159158289 : Rat)/666604241281083533800014731772020783928538300416,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C156_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C156_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C156_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C158_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3, a6 := 1 },   conductor := 158,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -3, -1, -2, 1, 4, -1, -7, 3, 1, 1, -4, 2, -6, -1, 3, -4, 6, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/2699345088927177715301513671875,   alphaHi := (5397215081808807583452231630848 : Rat)/10797380355708710765838623046875,   finite := ((1677868913674957 : Rat)/4503599627370496, (6917280881231883 : Rat)/4503599627370496),   tail := (107554364288778927327826160717010498046875 : Rat)/4983865264242080147096216968617574522683392,   box := { reLo := (3668428772074727422219541817812679978440743417153 : Rat)/10451923006635806864643125608170283645394520899584,            reHi := (16279135691891630620414935525870163989478944489207 : Rat)/10451923006635806864643125608170283645394520899584,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 79] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C158_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C158_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C158_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -9, a6 := 9 },   conductor := 158,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, 1, -3, 1, -3, -3, -3, 1, 6, -3, -2, -3, -5, -3, 9, 1, 6, 6, 0, -3, 9, -2, -2, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/2699345088927177715301513671875,   alphaHi := (5397215081808807583452231630848 : Rat)/10797380355708710765838623046875,   finite := ((6720371204884963 : Rat)/9007199254740992, (12584531737842303 : Rat)/9007199254740992),   tail := (12513823683396941170884712669525146484375 : Rat)/18194237322558960719066394911418020265984,   box := { reLo := (2225284753906406022883565857206819412177549627 : Rat)/38156081189479169589911528221270124036848877568,            reHi := (79553681515769872777492996485092354543222338487 : Rat)/38156081189479169589911528221270124036848877568,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 79] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C158_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C158_c1
