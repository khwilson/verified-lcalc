module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C192_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -129, a6 := 609 },   conductor := 192,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -4, 0, 1, 0, -4, 0, 2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/11902562517629947566986083984375,   finite := ((2856733868917681 : Rat)/9007199254740992, (21597691084158141 : Rat)/9007199254740992),   tail := (2366944324156003498842591602802276611328125 : Rat)/47206083288558485411771997073995347330596864,   box := { reLo := (105738339756450236020497272809630305506848337479941 : Rat)/395993327923068019193073868830893962580223498125312,            reHi := (969378224864488088070181611534401901558780845472001 : Rat)/395993327923068019193073868830893962580223498125312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C192_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C192_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C192_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 9 },   conductor := 192,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -4, 0, 1, 0, -4, 0, 2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/11902562517629947566986083984375,   finite := ((2856733868917681 : Rat)/9007199254740992, (21597691084158141 : Rat)/9007199254740992),   tail := (2366944324156003498842591602802276611328125 : Rat)/47206083288558485411771997073995347330596864,   box := { reLo := (105738339756450236020497272809630305506848337479941 : Rat)/395993327923068019193073868830893962580223498125312,            reHi := (969378224864488088070181611534401901558780845472001 : Rat)/395993327923068019193073868830893962580223498125312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C192_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C192_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C192_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C192_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := -2 },   conductor := 192,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -4, 0, 1, 0, -4, 0, 2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/11902562517629947566986083984375,   finite := ((2856733868917681 : Rat)/9007199254740992, (21597691084158141 : Rat)/9007199254740992),   tail := (2366944324156003498842591602802276611328125 : Rat)/47206083288558485411771997073995347330596864,   box := { reLo := (105738339756450236020497272809630305506848337479941 : Rat)/395993327923068019193073868830893962580223498125312,            reHi := (969378224864488088070181611534401901558780845472001 : Rat)/395993327923068019193073868830893962580223498125312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C192_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C192_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C192_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C192_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 31, a6 := 33 },   conductor := 192,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -4, 0, 1, 0, -4, 0, 2, 0, 2, 0, -6, 0, 4, 0, 4, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/11902562517629947566986083984375,   finite := ((2856733868917681 : Rat)/9007199254740992, (21597691084158141 : Rat)/9007199254740992),   tail := (2366944324156003498842591602802276611328125 : Rat)/47206083288558485411771997073995347330596864,   box := { reLo := (105738339756450236020497272809630305506848337479941 : Rat)/395993327923068019193073868830893962580223498125312,            reHi := (969378224864488088070181611534401901558780845472001 : Rat)/395993327923068019193073868830893962580223498125312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C192_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C192_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C192_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C196_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -142, a6 := 701 },   conductor := 196,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, 0, 0, -2, 0, -3, 0, -2, 0, 3, 0, -3, 0, 1, 0, 0, 0, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12025908428800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/700000000000000000000,   finite := ((2459782944042211 : Rat)/9007199254740992, (5591007683957325 : Rat)/2251799813685248),   tail := (16487816121475719248943733456058502197265625 : Rat)/301986269248015390849747266637505806794227712,   box := { reLo := (69186979596217220536345382968152104692160664270671 : Rat)/316655554263006986475664589861689288865064117338112,            reHi := (200878690588948705799582204028446392412943647281825 : Rat)/79163888565751746618916147465422322216266029334528,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C196_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C196_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C196_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 1 },   conductor := 196,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, 0, 0, -2, 0, -3, 0, -2, 0, 3, 0, -3, 0, 1, 0, 0, 0, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12025908428800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/700000000000000000000,   finite := ((2459782944042211 : Rat)/9007199254740992, (5591007683957325 : Rat)/2251799813685248),   tail := (16487816121475719248943733456058502197265625 : Rat)/301986269248015390849747266637505806794227712,   box := { reLo := (69186979596217220536345382968152104692160664270671 : Rat)/316655554263006986475664589861689288865064117338112,            reHi := (200878690588948705799582204028446392412943647281825 : Rat)/79163888565751746618916147465422322216266029334528,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C196_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C196_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C196_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C197_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -5, a6 := 4 },   conductor := 197,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, 0, 0, -3, 0, -3, 0, 4, 0, -2, 6, 0, -4, -8, 6, -3, 0, 0, -8, -3, 0, -5, 4, 0, -6, 7, 0,                    -10, 8, 0, 16, 0, -6, 7, 6, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6028273867800617504119873046875,   alphaHi := (5397215081808807583452231630848 : Rat)/12056547735601234912872314453125,   finite := ((2064116936893287 : Rat)/4503599627370496, (6751828033649017 : Rat)/4503599627370496),   tail := (42085593436732755415895651508808135986328125 : Rat)/754880502186183969840142132483044376158666752,   box := { reLo := (318657831981237155175650185722727489430466649967469 : Rat)/791549577460380042359096876710540739774950148145152,            reHi := (1230826601301101227562156125277680444129004851900979 : Rat)/791549577460380042359096876710540739774950148145152,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [197] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C197_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C197_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C198_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3168, a6 := 69430 },   conductor := 198,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -4, -1, 0, 2, 1, 0, -6, 4, 0, 1, -2, 0, 4, -2, 0, -1, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3021777343962693119049072265625,   alphaHi := (5397215081808807583452231630848 : Rat)/12087109375850772380828857421875,   finite := ((1254806441575541 : Rat)/9007199254740992, (10321637154511435 : Rat)/4503599627370496),   tail := (10740835478648842207289253542423248291015625 : Rat)/188698606666375420900512232169194615207886848,   box := { reLo := (65209056177509829136061810185806498695287578227441 : Rat)/791459320735205093384702057436181651344900638113792,            reHi := (929483665261180339190065919866079574919264005577935 : Rat)/395729660367602546692351028718090825672450319056896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C198_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C198_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C198_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -198, a6 := 1120 },   conductor := 198,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -4, -1, 0, 2, 1, 0, -6, 4, 0, 1, -2, 0, 4, -2, 0, -1, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3021777343962693119049072265625,   alphaHi := (5397215081808807583452231630848 : Rat)/12087109375850772380828857421875,   finite := ((1254806441575541 : Rat)/9007199254740992, (10321637154511435 : Rat)/4503599627370496),   tail := (10740835478648842207289253542423248291015625 : Rat)/188698606666375420900512232169194615207886848,   box := { reLo := (65209056177509829136061810185806498695287578227441 : Rat)/791459320735205093384702057436181651344900638113792,            reHi := (929483665261180339190065919866079574919264005577935 : Rat)/395729660367602546692351028718090825672450319056896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C198_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C198_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C198_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C198_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -108, a6 := 2074 },   conductor := 198,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -4, -1, 0, 2, 1, 0, -6, 4, 0, 1, -2, 0, 4, -2, 0, -1, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3021777343962693119049072265625,   alphaHi := (5397215081808807583452231630848 : Rat)/12087109375850772380828857421875,   finite := ((1254806441575541 : Rat)/9007199254740992, (10321637154511435 : Rat)/4503599627370496),   tail := (10740835478648842207289253542423248291015625 : Rat)/188698606666375420900512232169194615207886848,   box := { reLo := (65209056177509829136061810185806498695287578227441 : Rat)/791459320735205093384702057436181651344900638113792,            reHi := (929483665261180339190065919866079574919264005577935 : Rat)/395729660367602546692351028718090825672450319056896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C198_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C198_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C198_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C198_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := 4 },   conductor := 198,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -4, -1, 0, 2, 1, 0, -6, 4, 0, 1, -2, 0, 4, -2, 0, -1, -4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3021777343962693119049072265625,   alphaHi := (5397215081808807583452231630848 : Rat)/12087109375850772380828857421875,   finite := ((1254806441575541 : Rat)/9007199254740992, (10321637154511435 : Rat)/4503599627370496),   tail := (10740835478648842207289253542423248291015625 : Rat)/188698606666375420900512232169194615207886848,   box := { reLo := (65209056177509829136061810185806498695287578227441 : Rat)/791459320735205093384702057436181651344900638113792,            reHi := (929483665261180339190065919866079574919264005577935 : Rat)/395729660367602546692351028718090825672450319056896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C198_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C198_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C198_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C200_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := 48 },   conductor := 200,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -2, 0, 1, 0, -4, 0, -4, 0, 0, 0, 0, 0, -4, 0, 4, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/12148001999904198741912841796875,   finite := ((1729007042117957 : Rat)/9007199254740992, (2816625610422669 : Rat)/1125899906842624),   tail := (2237707737411530100584855653591156005859375 : Rat)/37730977898185119590612360079727846190219264,   box := { reLo := (20992777788647347319391858066722039834999682630001 : Rat)/158255191522269439839383784331842824187021419872256,            reHi := (50660908961395060515577349793270553253465797528217 : Rat)/19781898940283679979922973041480353023377677484032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C200_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C200_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C200_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -2 },   conductor := 200,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -2, 0, 1, 0, -4, 0, -4, 0, 0, 0, 0, 0, -4, 0, 4, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/12148001999904198741912841796875,   finite := ((1729007042117957 : Rat)/9007199254740992, (2816625610422669 : Rat)/1125899906842624),   tail := (2237707737411530100584855653591156005859375 : Rat)/37730977898185119590612360079727846190219264,   box := { reLo := (20992777788647347319391858066722039834999682630001 : Rat)/158255191522269439839383784331842824187021419872256,            reHi := (50660908961395060515577349793270553253465797528217 : Rat)/19781898940283679979922973041480353023377677484032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C200_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C200_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C200_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C201_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 2, a6 := 0 },   conductor := 201,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, 0, 2, 0, 0, 1, 0, -6, -2, 4, 0, 0, -4, -7, -2, -5, 0, 0, 12, -1, 0, -5, -8, -1, 0, 1,                    0, -4, 8, 6, 14, 0, 2, 3, 10, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12178334137008427333831787109375,   alphaHi := (2698607540904403791726115815424 : Rat)/6089167068504213619232177734375,   finite := ((3316854701307867 : Rat)/9007199254740992, (12817563194817521 : Rat)/9007199254740992),   tail := (11416833151672141677294013290882110595703125 : Rat)/188632690740671740935844501386005349775966208,   box := { reLo := (60865834360977920124090692474952389261192656452933 : Rat)/197795712326090611423544083885331945646683542519808,            reHi := (293441713465409522971745707030896745581308972672879 : Rat)/197795712326090611423544083885331945646683542519808,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 67] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C201_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C201_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C201_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 2 },   conductor := 201,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, -1, -1, -5, 3, 1, 1, -4, -1, -4, 5, -1, -1, 6, -1, -2, 1, -5, 4, -3, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/12178334137008427333831787109375,   alphaHi := (2698607540904403791726115815424 : Rat)/6089167068504213619232177734375,   finite := ((449669127755295 : Rat)/4503599627370496, (21957726153344831 : Rat)/9007199254740992),   tail := (11416833151672141677294013290882110595703125 : Rat)/188632690740671740935844501386005349775966208,   box := { reLo := (3888906443476489581360089137115696188694713752705 : Rat)/98897856163045305711772041942665972823341771259904,            reHi := (494157273544405911992636843256352409870257078089569 : Rat)/197795712326090611423544083885331945646683542519808,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 67] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C201_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C201_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C201_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -794, a6 := 8289 },   conductor := 201,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -3, -1, -3, -3, 1, -3, 0, 1, 4, -3, 3, -1, 2, 1, -2, 3, 3, 0, -7, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/12178334137008427333831787109375,   alphaHi := (2698607540904403791726115815424 : Rat)/6089167068504213619232177734375,   finite := ((1461538188572013 : Rat)/4503599627370496, (27732484314992625 : Rat)/9007199254740992),   tail := (11416833151672141677294013290882110595703125 : Rat)/188632690740671740935844501386005349775966208,   box := { reLo := (26109283278110009010335089047949357157711048579187 : Rat)/98897856163045305711772041942665972823341771259904,            reHi := (620969434771195192282538324447235575298120947307375 : Rat)/197795712326090611423544083885331945646683542519808,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 67] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C201_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C201_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C203_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := -2 },   conductor := 203,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, -1, 1, 1, 1, 3, -2, -1, -5, 1, -5, -1, -1, -1, -4, 2, -4, -1, -1, 5, 6, -3, -4, 5, 5, -1,                    1, 1, 7, -5, 5, 4, 1, 2, -10, 4, 5, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/12238772891042694759368896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/6119386445521347332000732421875,   finite := ((327784702754443 : Rat)/562949953421312, (15049723887130155 : Rat)/9007199254740992),   tail := (95059021448058658311472521430110931396484375 : Rat)/1508700894987774333932272505741090168059723776,   box := { reLo := (51340973320471776291552099695150559230033746662079 : Rat)/98874221853918778748585410936248085253962057383936,            reHi := (2742948411611783417482551421770396771452529465909215 : Rat)/1581987549662700459977366574979969364063392918142976,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 7, 29] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C203_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C203_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C205_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -232, a6 := -1286 },   conductor := 205,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -4, 3, -3, -1, 0, 0, -2, 4, 0, -1, -6, 3, 0, -1, 0, 0, -8, 0, 1, 2, 0, 4, 6, 0,                    0, -5, 0, 6, -4, 3, 6, 0, 0, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/6149457321675188350677490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/12298914643350376605987548828125,   finite := ((6325007381877269 : Rat)/9007199254740992, (3947059549620471 : Rat)/2251799813685248),   tail := (9887963633946499292292310212078094482421875 : Rat)/150833298619549030925799339288952881257906176,   box := { reLo := (201388930093254234896334617920926462010404451981589 : Rat)/316320353866584489304101935988506112835780452810752,            reHi := (143799401443846161263009027249611482609332908623351 : Rat)/79080088466646122326025483997126528208945113202688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C205_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C205_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C205_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -27, a6 := 26 },   conductor := 205,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -4, 3, -3, -1, 0, 0, -2, 4, 0, -1, -6, 3, 0, -1, 0, 0, -8, 0, 1, 2, 0, 4, 6, 0,                    0, -5, 0, 6, -4, 3, 6, 0, 0, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/6149457321675188350677490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/12298914643350376605987548828125,   finite := ((6325007381877269 : Rat)/9007199254740992, (3947059549620471 : Rat)/2251799813685248),   tail := (9887963633946499292292310212078094482421875 : Rat)/150833298619549030925799339288952881257906176,   box := { reLo := (201388930093254234896334617920926462010404451981589 : Rat)/316320353866584489304101935988506112835780452810752,            reHi := (143799401443846161263009027249611482609332908623351 : Rat)/79080088466646122326025483997126528208945113202688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 41, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C205_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C205_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C205_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C205_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -22, a6 := 44 },   conductor := 205,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -4, 3, -3, -1, 0, 0, -2, 4, 0, -1, -6, 3, 0, -1, 0, 0, -8, 0, 1, 2, 0, 4, 6, 0,                    0, -5, 0, 6, -4, 3, 6, 0, 0, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/6149457321675188350677490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/12298914643350376605987548828125,   finite := ((6325007381877269 : Rat)/9007199254740992, (3947059549620471 : Rat)/2251799813685248),   tail := (9887963633946499292292310212078094482421875 : Rat)/150833298619549030925799339288952881257906176,   box := { reLo := (201388930093254234896334617920926462010404451981589 : Rat)/316320353866584489304101935988506112835780452810752,            reHi := (143799401443846161263009027249611482609332908623351 : Rat)/79080088466646122326025483997126528208945113202688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C205_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C205_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C205_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C205_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 98, a6 := 126 },   conductor := 205,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 1, 0, -4, 3, -3, -1, 0, 0, -2, 4, 0, -1, -6, 3, 0, -1, 0, 0, -8, 0, 1, 2, 0, 4, 6, 0,                    0, -5, 0, 6, -4, 3, 6, 0, 0, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/6149457321675188350677490234375,   alphaHi := (5397215081808807583452231630848 : Rat)/12298914643350376605987548828125,   finite := ((6325007381877269 : Rat)/9007199254740992, (3947059549620471 : Rat)/2251799813685248),   tail := (9887963633946499292292310212078094482421875 : Rat)/150833298619549030925799339288952881257906176,   box := { reLo := (201388930093254234896334617920926462010404451981589 : Rat)/316320353866584489304101935988506112835780452810752,            reHi := (143799401443846161263009027249611482609332908623351 : Rat)/79080088466646122326025483997126528208945113202688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 41, 41, 41, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C205_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C205_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C205_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C207_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -140, a6 := 668 },   conductor := 207,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, -2, 3, 0, 0, -4, 0, -6, 2, 0, -1, -4, 0, 2, 0, 0, 4, 1, 0, -5, 6, 0, 2, -2, 0, 4,                    -5, 0, 4, 0, 0, 2, -2, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3089690932463098812103271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12358763729852395153045654296875,   finite := ((6317851800959745 : Rat)/9007199254740992, (15770298962063255 : Rat)/9007199254740992),   tail := (1427741290848374684626856948375701904296875 : Rat)/20943858180340223653905286069393136814129152,   box := { reLo := (55628009993962732810735184022068195240321496728505 : Rat)/87844908141233721432469556981999911312049158750208,            reHi := (159792068979661848398996345243312784949366196798495 : Rat)/87844908141233721432469556981999911312049158750208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 23, 23] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C207_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C207_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C207_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 20 },   conductor := 207,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, -2, 3, 0, 0, -4, 0, -6, 2, 0, -1, -4, 0, 2, 0, 0, 4, 1, 0, -5, 6, 0, 2, -2, 0, 4,                    -5, 0, 4, 0, 0, 2, -2, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3089690932463098812103271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12358763729852395153045654296875,   finite := ((6317851800959745 : Rat)/9007199254740992, (15770298962063255 : Rat)/9007199254740992),   tail := (1427741290848374684626856948375701904296875 : Rat)/20943858180340223653905286069393136814129152,   box := { reLo := (55628009993962732810735184022068195240321496728505 : Rat)/87844908141233721432469556981999911312049158750208,            reHi := (159792068979661848398996345243312784949366196798495 : Rat)/87844908141233721432469556981999911312049158750208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 23] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C207_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C207_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C207_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C208_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 32 },   conductor := 208,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -5, 0, -2, 0, 2, 0, -1, 0, 1, 0, -3, 0, 2, 0, 5, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12388579849735137081146240234375,   alphaHi := (2698607540904403791726115815424 : Rat)/6194289924867568492889404296875,   finite := ((976095212753887 : Rat)/9007199254740992, (25381623183795089 : Rat)/9007199254740992),   tail := (104792926723521804424462944861125946044921875 : Rat)/1507767454339145083455716679411440488433057792,   box := { reLo := (61447944333814252349590897691128486513567824009087 : Rat)/1581008766201123395029661572830530621599182007304192,            reHi := (4565049445525787432394760795228274936881883279829489 : Rat)/1581008766201123395029661572830530621599182007304192,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] }
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C208_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C208_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C209_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -27, a6 := 55 },   conductor := 209,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -3, 0, -4, 0, -2, 0, 1, -2, 2, 0, -3, 4, 0, 0, 1, 6, -4, 0, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12418324381985351085662841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/6209162190992675495147705078125,   finite := ((665324298694995 : Rat)/4503599627370496, (27114133548805693 : Rat)/9007199254740992),   tail := (106813076531624431271659380130290985107421875 : Rat)/1507575294316889248070206735825942930968805376,   box := { reLo := (60766835668492708379406429463597696212613268754735 : Rat)/790403635906813230092232549112711967391773032972288,            reHi := (4870663924180020518329521903620067820906004102989729 : Rat)/1580807271813626460184465098225423934783546065944576,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [11, 11, 11, 19, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C209_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C209_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C209_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 193, a6 := -308 },   conductor := 209,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -3, 0, -4, 0, -2, 0, 1, -2, 2, 0, -3, 4, 0, 0, 1, 6, -4, 0, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12418324381985351085662841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/6209162190992675495147705078125,   finite := ((665324298694995 : Rat)/4503599627370496, (27114133548805693 : Rat)/9007199254740992),   tail := (106813076531624431271659380130290985107421875 : Rat)/1507575294316889248070206735825942930968805376,   box := { reLo := (60766835668492708379406429463597696212613268754735 : Rat)/790403635906813230092232549112711967391773032972288,            reHi := (4870663924180020518329521903620067820906004102989729 : Rat)/1580807271813626460184465098225423934783546065944576,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [11, 19, 19, 19, 19, 19, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C209_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C209_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C209_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C210_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -373, a6 := 2623 },   conductor := 210,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -4, -1, -2, 1, 1, 1, -6, -1, 0, -1, 1, 4, -8, 1, 1, 2, -1, -1, 10,                    -1, -8, -1, 4, 6, 1, 1, 2, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/12447997839779706287384033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3111999459944926548004150390625,   finite := ((1544061136965893 : Rat)/2251799813685248, (15638244790387115 : Rat)/9007199254740992),   tail := (7257195017992917617160911994533538818359375 : Rat)/100492087201316806356482362021663466332356608,   box := { reLo := (16161261129978454020396656458928529892487787663907 : Rat)/26343397707301992885513712309806947718229290647552,            reHi := (190558710683683872929539620903199501394141976051885 : Rat)/105373590829207971542054849239227790872917162590208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 5, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C210_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C210_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C210_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -23, a6 := 33 },   conductor := 210,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -4, -1, -2, 1, 1, 1, -6, -1, 0, -1, 1, 4, -8, 1, 1, 2, -1, -1, 10,                    -1, -8, -1, 4, 6, 1, 1, 2, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/12447997839779706287384033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3111999459944926548004150390625,   finite := ((1544061136965893 : Rat)/2251799813685248, (15638244790387115 : Rat)/9007199254740992),   tail := (7257195017992917617160911994533538818359375 : Rat)/100492087201316806356482362021663466332356608,   box := { reLo := (16161261129978454020396656458928529892487787663907 : Rat)/26343397707301992885513712309806947718229290647552,            reHi := (190558710683683872929539620903199501394141976051885 : Rat)/105373590829207971542054849239227790872917162590208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 5, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C210_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C210_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C210_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C210_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3, a6 := -3 },   conductor := 210,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -4, -1, -2, 1, 1, 1, -6, -1, 0, -1, 1, 4, -8, 1, 1, 2, -1, -1, 10,                    -1, -8, -1, 4, 6, 1, 1, 2, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/12447997839779706287384033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3111999459944926548004150390625,   finite := ((1544061136965893 : Rat)/2251799813685248, (15638244790387115 : Rat)/9007199254740992),   tail := (7257195017992917617160911994533538818359375 : Rat)/100492087201316806356482362021663466332356608,   box := { reLo := (16161261129978454020396656458928529892487787663907 : Rat)/26343397707301992885513712309806947718229290647552,            reHi := (190558710683683872929539620903199501394141976051885 : Rat)/105373590829207971542054849239227790872917162590208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 5, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C210_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C210_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C210_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C210_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 7, a6 := 147 },   conductor := 210,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -4, -1, -2, 1, 1, 1, -6, -1, 0, -1, 1, 4, -8, 1, 1, 2, -1, -1, 10,                    -1, -8, -1, 4, 6, 1, 1, 2, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/12447997839779706287384033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3111999459944926548004150390625,   finite := ((1544061136965893 : Rat)/2251799813685248, (15638244790387115 : Rat)/9007199254740992),   tail := (7257195017992917617160911994533538818359375 : Rat)/100492087201316806356482362021663466332356608,   box := { reLo := (16161261129978454020396656458928529892487787663907 : Rat)/26343397707301992885513712309806947718229290647552,            reHi := (190558710683683872929539620903199501394141976051885 : Rat)/105373590829207971542054849239227790872917162590208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 5, 5, 5, 5, 7, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C210_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C210_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C210_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C212_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 8 },   conductor := 212,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -2, 0, -2, 0, 2, 0, -7, 0, 2, 0, -3, 0, 5, 0, 2, 0, -3, 0, -1, 0, 5, 0, 9, 0, -8,                    0, -2, 0, 4, 0, -3, 0, 7, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3126783388574600696563720703125,   alphaHi := (5397215081808807583452231630848 : Rat)/12507133554298402690887451171875,   finite := ((7788949309582907 : Rat)/9007199254740992, (18930400561274491 : Rat)/9007199254740992),   tail := (28255531422614650300239230000972747802734375 : Rat)/376746963364814491241917443164976846466973696,   box := { reLo := (1247953529756396649867445974601281123018311811342789 : Rat)/1580191295428894879873939299536635047043813641027584,            reHi := (3439595051254997822941088392754560099729433368097157 : Rat)/1580191295428894879873939299536635047043813641027584,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 53] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C212_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C212_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C214_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := 0 },   conductor := 214,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -2, 1, -1, 2, 4, -1, 1, 1, -6, -2, -4, -4, 2, 1, -6, -1, -2, -1, -8, 6, 5, 2, -4, 4, 4, 4, 0,                    -2, -2, -1, 12, 6, -4, 1, 0, 2, 8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/12565990978468580913543701171875,   alphaHi := (2698607540904403791726115815424 : Rat)/6282995489234290409088134765625,   finite := ((4696996944222839 : Rat)/9007199254740992, (481391816368571 : Rat)/281474976710656),   tail := (10662393584295267784182268674755096435546875 : Rat)/136962462296172247979501505181299101812129792,   box := { reLo := (63711074568812895955601077244413052941418020718739 : Rat)/143615550864671111097353770296985886981755808776192,            reHi := (8024951150278285896187214767711692260239115293671 : Rat)/4487985964520972221792305321780808968179869024256,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 107] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C214_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C214_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C214_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -193, a6 := 1012 },   conductor := 214,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -4, -1, -2, -1, -2, 4, -3, 1, -1, 2, -4, 1, 6, 2, 1, -4, -2, 3, -7, -1, 11, 1, -5, -2,                    -6, 4, 4, -1, -3, -6, 8, -2, -9, -1, -1, 4],   alphaLo := (5397215081808807583435051761664 : Rat)/12565990978468580913543701171875,   alphaHi := (2698607540904403791726115815424 : Rat)/6282995489234290409088134765625,   finite := ((6982807462518231 : Rat)/9007199254740992, (8964467307644417 : Rat)/4503599627370496),   tail := (10662393584295267784182268674755096435546875 : Rat)/136962462296172247979501505181299101812129792,   box := { reLo := (100157246955247124491556814311730397707136283689331 : Rat)/143615550864671111097353770296985886981755808776192,            reHi := (148524375097084201702681128182199615739066991922117 : Rat)/71807775432335555548676885148492943490877904388096,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 107] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C214_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C214_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C214_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -12, a6 := 16 },   conductor := 214,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -4, 1, 1, -3, -2, -2, 4, -4, 6, 1, -2, 1, -2, -3, 8, -2, 1, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/12565990978468580913543701171875,   alphaHi := (2698607540904403791726115815424 : Rat)/6282995489234290409088134765625,   finite := ((125918615304001 : Rat)/1125899906842624, (7664113459625573 : Rat)/2251799813685248),   tail := (10662393584295267784182268674755096435546875 : Rat)/136962462296172247979501505181299101812129792,   box := { reLo := (610171777392157931053682366817798031022246212101 : Rat)/17951943858083888887169221287123235872719476097024,            reHi := (124995762788936106483457158817250513427766977266873 : Rat)/35903887716167777774338442574246471745438952194048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 107] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C214_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C214_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C215_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -8, a6 := -12 },   conductor := 215,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -1, 0, -2, 0, -3, 0, -1, 0, -1, 0, 0, 4, -3, 0, -2, 2, 0, 0, -1, 0, 1, 0, 0, 4, 4, 0, 3,                    0, 0, 0, 2, 6, -8, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3148829137889016056060791015625,   alphaHi := (5397215081808807583452231630848 : Rat)/12595316551556064128875732421875,   finite := ((4068279677770939 : Rat)/4503599627370496, (19654738119236597 : Rat)/9007199254740992),   tail := (29864044565278150509630963379764556884765625 : Rat)/376595989308630536534473861332277976316772352,   box := { reLo := (650809197713798313888130326250194957574576756293311 : Rat)/789779032170573146954344927240709422588671771541504,            reHi := (3572035090330933999771886476995907761469426442991153 : Rat)/1579558064341146293908689854481418845177343543083008,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 43] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C215_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C215_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C216_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 20 },   conductor := 216,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, -3, 0, 0, 0, -4, 0, 1, 0, 0, 0, 4, 0, -1, 0, 0, 0, -4, 0, 11, 0, 0, 0, 0, 0, -4,                    0, 0, 0, 12, 0, -9, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/12624574004569442272186279296875,   finite := ((8311000414350383 : Rat)/9007199254740992, (2510129618337497 : Rat)/1125899906842624),   tail := (5068805026829425618909603813076019287109375 : Rat)/62757458308415336113586145151203906055831552,   box := { reLo := (221618230056358197817629963431053547471830348485067 : Rat)/263223858412819677922558822952275147985598501879808,            reHi := (76012835828142539728500078674014012267686522089053 : Rat)/32902982301602459740319852869034393498199812734976,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C216_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C216_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C218_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := 4 },   conductor := 218,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -4, 1, 1, -3, 3, -2, -4, -4, 6, 1, -6, 1, 5, -3, 8, 3, 3, -2, 4, -4, 4, -4, -3,                    6, -4, 1, -6, -6, 12, 1, -4, 5, 8, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/12682886434985818767547607421875,   alphaHi := (2698607540904403791726115815424 : Rat)/6341443217492909336090087890625,   finite := ((9075516055128341 : Rat)/9007199254740992, (2889765715841565 : Rat)/1125899906842624),   tail := (126117866380189799504729854540538787841796875 : Rat)/1505763593225333340331228286258658358838951936,   box := { reLo := (1458638919689120212069103950732196881541421395606953 : Rat)/1578907565529847132671158031491958947277912865243136,            reHi := (523088977424616307396623671220707062558391868712145 : Rat)/197363445691230891583894753936494868409739108155392,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 109] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C218_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C218_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C218_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 18, a6 := -104 },   conductor := 218,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -4, 1, 1, -3, 3, -2, -4, -4, 6, 1, -6, 1, 5, -3, 8, 3, 3, -2, 4, -4, 4, -4, -3,                    6, -4, 1, -6, -6, 12, 1, -4, 5, 8, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/12682886434985818767547607421875,   alphaHi := (2698607540904403791726115815424 : Rat)/6341443217492909336090087890625,   finite := ((9075516055128341 : Rat)/9007199254740992, (2889765715841565 : Rat)/1125899906842624),   tail := (126117866380189799504729854540538787841796875 : Rat)/1505763593225333340331228286258658358838951936,   box := { reLo := (1458638919689120212069103950732196881541421395606953 : Rat)/1578907565529847132671158031491958947277912865243136,            reHi := (523088977424616307396623671220707062558391868712145 : Rat)/197363445691230891583894753936494868409739108155392,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 109, 109, 109] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C218_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C218_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C218_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C219_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -6, a6 := 8 },   conductor := 219,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, -1, 2, 2, 0, 1, 2, -4, -2, -2, -4, 1, -4, -3, -2, -1, -2, -2, 8, 0, 0, -4, 4, -1, 4,                    -10, -2, -6, 8, 4, 6, -2, 2, 1, 2, 2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/794496396324268245697021484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12711942341188291835784912109375,   finite := ((3455069936224511 : Rat)/9007199254740992, (13574753297389619 : Rat)/9007199254740992),   tail := (160486821562497199007307452709197998046875 : Rat)/1881941430678392158306912558899466711597056,   box := { reLo := (9418842344170030294672503307480865486411096346743 : Rat)/31573737881840411772621266293769075305273513476096,            reHi := (50277314002009325422484686270759207475974662959947 : Rat)/31573737881840411772621266293769075305273513476096,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 73] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C219_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C219_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C219_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -27, a6 := -85 },   conductor := 219,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -3, 0, -4, 0, 1, 0, 0, -2, -4, 0, -3, 4, 3, 0, -1, 6, -4, 0, 6, 0, 4, 0, 1, 8, -6, 0,                    -10, 0, 0, 0, 12, -2, -7, 0, -4, 0],   alphaLo := (337325942613050473964690735104 : Rat)/794496396324268245697021484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12711942341188291835784912109375,   finite := ((4314122907995327 : Rat)/4503599627370496, (10519956765488457 : Rat)/4503599627370496),   tail := (160486821562497199007307452709197998046875 : Rat)/1881941430678392158306912558899466711597056,   box := { reLo := (13776418283224876244318448495131814445600940560951 : Rat)/15786868940920205886310633146884537652636756738048,            reHi := (38222802571402704824857608778899351136408951194641 : Rat)/15786868940920205886310633146884537652636756738048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 73, 73, 73] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C219_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C219_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C219_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 3, a6 := 2 },   conductor := 219,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -3, 0, -4, 0, 1, 0, 0, -2, -4, 0, -3, 4, 3, 0, -1, 6, -4, 0, 6, 0, 4, 0, 1, 8, -6, 0,                    -10, 0, 0, 0, 12, -2, -7, 0, -4, 0],   alphaLo := (337325942613050473964690735104 : Rat)/794496396324268245697021484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12711942341188291835784912109375,   finite := ((4314122907995327 : Rat)/4503599627370496, (10519956765488457 : Rat)/4503599627370496),   tail := (160486821562497199007307452709197998046875 : Rat)/1881941430678392158306912558899466711597056,   box := { reLo := (13776418283224876244318448495131814445600940560951 : Rat)/15786868940920205886310633146884537652636756738048,            reHi := (38222802571402704824857608778899351136408951194641 : Rat)/15786868940920205886310633146884537652636756738048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 73] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C219_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C219_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C219_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C219_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1297, a6 := -18530 },   conductor := 219,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -4, -1, 2, -3, 1, -4, -4, 1, -2, 2, 4, -1, 0, 1, -4, 4, -2, -4, 0, 3, 11, -2, -1, -2,                    8, 4, 6, 5, 4, 0, -8, -1, -2, -4, 2, 12],   alphaLo := (337325942613050473964690735104 : Rat)/794496396324268245697021484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12711942341188291835784912109375,   finite := ((1155247418372663 : Rat)/1125899906842624, (5939464041546149 : Rat)/2251799813685248),   tail := (160486821562497199007307452709197998046875 : Rat)/1881941430678392158306912558899466711597056,   box := { reLo := (3713026422770850456574077248530074746755140951919 : Rat)/3946717235230051471577658286721134413159189184512,            reHi := (21493262892036873333945118957108402377876670357837 : Rat)/7893434470460102943155316573442268826318378369024,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 73, 73] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C219_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C219_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C219_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -82, a6 := -305 },   conductor := 219,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -4, -1, 2, -3, 1, -4, -4, 1, -2, 2, 4, -1, 0, 1, -4, 4, -2, -4, 0, 3, 11, -2, -1, -2,                    8, 4, 6, 5, 4, 0, -8, -1, -2, -4, 2, 12],   alphaLo := (337325942613050473964690735104 : Rat)/794496396324268245697021484375,   alphaHi := (5397215081808807583452231630848 : Rat)/12711942341188291835784912109375,   finite := ((1155247418372663 : Rat)/1125899906842624, (5939464041546149 : Rat)/2251799813685248),   tail := (160486821562497199007307452709197998046875 : Rat)/1881941430678392158306912558899466711597056,   box := { reLo := (3713026422770850456574077248530074746755140951919 : Rat)/3946717235230051471577658286721134413159189184512,            reHi := (21493262892036873333945118957108402377876670357837 : Rat)/7893434470460102943155316573442268826318378369024,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 73] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C219_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C219_c2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C219_c2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C220_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7100, a6 := -232652 },   conductor := 220,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -4, 0, 1, 0, -1, 0, -4, 0, -2, 0, 0, 0, -4, 0, 8, 0, -6, 0, 1, 0, 4, 0, -6, 0, 8,                    0, 2, 0, -4, 0, 2, 0, 8, 0],   alphaLo := (42165742826631309245586341888 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/12740931985088220119476318359375,   finite := ((971080606161993 : Rat)/1125899906842624, (9383375475140809 : Rat)/4503599627370496),   tail := (510494987154525473346467998218536376953125 : Rat)/5880237755357486632428179953711826381832192,   box := { reLo := (76523700138453818177989019094334810118049864303179 : Rat)/98654018952987710449360179570293312962497160937472,            reHi := (856452342503400257026359596849816688582962521006027 : Rat)/394616075811950841797440718281173251849988643749888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 11, 11, 11] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C220_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C220_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C220_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -445, a6 := -3720 },   conductor := 220,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -4, 0, 1, 0, -1, 0, -4, 0, -2, 0, 0, 0, -4, 0, 8, 0, -6, 0, 1, 0, 4, 0, -6, 0, 8,                    0, 2, 0, -4, 0, 2, 0, 8, 0],   alphaLo := (42165742826631309245586341888 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/12740931985088220119476318359375,   finite := ((971080606161993 : Rat)/1125899906842624, (9383375475140809 : Rat)/4503599627370496),   tail := (510494987154525473346467998218536376953125 : Rat)/5880237755357486632428179953711826381832192,   box := { reLo := (76523700138453818177989019094334810118049864303179 : Rat)/98654018952987710449360179570293312962497160937472,            reHi := (856452342503400257026359596849816688582962521006027 : Rat)/394616075811950841797440718281173251849988643749888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 11, 11, 11, 11, 11, 11] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C220_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C220_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C220_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C220_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -100, a6 := -252 },   conductor := 220,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -4, 0, 1, 0, -1, 0, -4, 0, -2, 0, 0, 0, -4, 0, 8, 0, -6, 0, 1, 0, 4, 0, -6, 0, 8,                    0, 2, 0, -4, 0, 2, 0, 8, 0],   alphaLo := (42165742826631309245586341888 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/12740931985088220119476318359375,   finite := ((971080606161993 : Rat)/1125899906842624, (9383375475140809 : Rat)/4503599627370496),   tail := (510494987154525473346467998218536376953125 : Rat)/5880237755357486632428179953711826381832192,   box := { reLo := (76523700138453818177989019094334810118049864303179 : Rat)/98654018952987710449360179570293312962497160937472,            reHi := (856452342503400257026359596849816688582962521006027 : Rat)/394616075811950841797440718281173251849988643749888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C220_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C220_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C220_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C220_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -45, a6 := 100 },   conductor := 220,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -4, 0, 1, 0, -1, 0, -4, 0, -2, 0, 0, 0, -4, 0, 8, 0, -6, 0, 1, 0, 4, 0, -6, 0, 8,                    0, 2, 0, -4, 0, 2, 0, 8, 0],   alphaLo := (42165742826631309245586341888 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/12740931985088220119476318359375,   finite := ((971080606161993 : Rat)/1125899906842624, (9383375475140809 : Rat)/4503599627370496),   tail := (510494987154525473346467998218536376953125 : Rat)/5880237755357486632428179953711826381832192,   box := { reLo := (76523700138453818177989019094334810118049864303179 : Rat)/98654018952987710449360179570293312962497160937472,            reHi := (856452342503400257026359596849816688582962521006027 : Rat)/394616075811950841797440718281173251849988643749888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C220_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C220_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C220_a4
