module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C37_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1, a6 := 0 },   conductor := 37,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   finite := ((67275646462285 : Rat)/2251799813685248, (916571988775781 : Rat)/2251799813685248),   tail := (3032403881083705372597559290790557861328125 : Rat)/758024334991772882370407397346757837370425344,   box := { reLo := (10283712920796241229017211494935974495928793484615 : Rat)/397423062544166620952216153540136973039265562755072,            reHi := (163356829145525307802728876771554607105780530671759 : Rat)/397423062544166620952216153540136973039265562755072,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [37] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C37_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C37_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C43_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 0, a6 := 0 },   conductor := 43,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -2, -2, 2, -4, 4, 0, 0, 1, 8, 3, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/5632796801481518840789794921875,   alphaHi := (2698607540904403791726115815424 : Rat)/2816398400740759372711181640625,   finite := ((11912831401733 : Rat)/281474976710656, (4202916438092519 : Rat)/9007199254740992),   tail := (110106513253349709591072276592254638671875 : Rat)/14013739891128292510296009532878432111689728,   box := { reLo := (7913395085900170377399651711521041984866840161 : Rat)/229601114376245944488689820186680231717924503552,            reHi := (3486075965436971095744586210295714307335449232923 : Rat)/7347235660039870223638074245973767414973584113664,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [43] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C43_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C43_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C53_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 0 },   conductor := 53,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -3, -1, 0, 3, -4, 3, 6, 0, 0, 3],   alphaLo := (2698607540904403791717525880832 : Rat)/3126783388574600696563720703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6253566777149201297760009765625,   finite := ((460090882894569 : Rat)/9007199254740992, (2807706266681087 : Rat)/4503599627370496),   tail := (28255531422614650300239230000972747802734375 : Rat)/1506987853459257964967669772659907385867894784,   box := { reLo := (51088650994628668482765029441731590225928781661463 : Rat)/1580191295428894879873939299536635047043813641027584,            reHi := (507388128987033953881588113659845929026206300475649 : Rat)/790095647714447439936969649768317523521906820513792,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [53] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C53_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C53_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C57_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -2, a6 := 2 },   conductor := 57,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -2, -1, 2, -3, 2, -5, 0, 1, 6, 1, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   finite := ((244416957963941 : Rat)/9007199254740992, (2849020420487037 : Rat)/4503599627370496),   tail := (18749947628160150668713386762142181396484375 : Rat)/751788376915434021761454002627034175831539712,   box := { reLo := (865275145946206180192430552574551567554813315913 : Rat)/394153624556239072401269196129322493978366292525056,            reHi := (129587872353631261895247344766151694630935669610241 : Rat)/197076812278119536200634598064661246989183146262528,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C57_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C57_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C58_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1, a6 := 1 },   conductor := 58,   policy := { precisionBits := 53 },   termLimit := 12,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -3, 1, -3, 3, -2, -1, 6, 3, -1, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/6541899284688366413116455078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1635474821172091579437255859375,   finite := ((162654945878633 : Rat)/4503599627370496, (6286691378301321 : Rat)/9007199254740992),   tail := (40072030995114075153526360879421234130859375 : Rat)/1502650822859663863872923403321087535557378048,   box := { reLo := (3722100775290004330393614473482177968747446742551 : Rat)/393910897307723723931103632640203170921153311014912,            reHi := (570879710162080812462480049836319536983498279933687 : Rat)/787821794615447447862207265280406341842306622029824,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 29] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C58_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C58_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C61_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := 1 },   conductor := 61,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -2, -1, -3, 2, 1, 3, 1, 3, -5, 2, 1, -1, 6, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1677238346580683994293212890625,   alphaHi := (5397215081808807583452231630848 : Rat)/6708953386322735881805419921875,   finite := ((489947684268019 : Rat)/4503599627370496, (1491536441367301 : Rat)/2251799813685248),   tail := (24217911671036451457004652958202362060546875 : Rat)/749849088684165446127098305404975640481890304,   box := { reLo := (60144589881859701549447570079982340703265500388381 : Rat)/786273758016087466838168232688327737193938607407104,            reHi := (273101294945734435957435782530395608698950881768299 : Rat)/393136879008043733419084116344163868596969303703552,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [61] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C61_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C61_a1
