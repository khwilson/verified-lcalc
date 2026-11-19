module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C65_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 0 },   conductor := 65,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -2, -1, -1, 2, -4, 3, 1, 1, 2, 2, -1, 4, 2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/6925426672172974109649658203125,   alphaHi := (1349303770452201895863057907712 : Rat)/1731356668043243503570556640625,   finite := ((1114914038796987 : Rat)/9007199254740992, (6290259410416321 : Rat)/9007199254740992),   tail := (15284997624785049065738592284679412841796875 : Rat)/373839194140416567894310597417012311804084224,   box := { reLo := (16247128752585327352762478178243743756366835349457 : Rat)/195999403417490721548172314498570550931139709632512,            reHi := (144891704440750822627223228063102870049813229655331 : Rat)/195999403417490721548172314498570550931139709632512,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C65_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C65_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C65_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 4, a6 := 1 },   conductor := 65,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -2, -1, -1, 2, -4, 3, 1, 1, 2, 2, -1, 4, 2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/6925426672172974109649658203125,   alphaHi := (1349303770452201895863057907712 : Rat)/1731356668043243503570556640625,   finite := ((1114914038796987 : Rat)/9007199254740992, (6290259410416321 : Rat)/9007199254740992),   tail := (15284997624785049065738592284679412841796875 : Rat)/373839194140416567894310597417012311804084224,   box := { reLo := (16247128752585327352762478178243743756366835349457 : Rat)/195999403417490721548172314498570550931139709632512,            reHi := (144891704440750822627223228063102870049813229655331 : Rat)/195999403417490721548172314498570550931139709632512,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C65_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C65_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C65_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C77_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 2, a6 := 0 },   conductor := 77,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -3, -2, -1, 0, -1, 0, 6, 0, -1, 6, -4, 0, 3, 4],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   finite := ((1400687061789515 : Rat)/9007199254740992, (8167234335559479 : Rat)/9007199254740992),   tail := (27604071905853748849114792745304107666015625 : Rat)/369912500758622560014386565680750835005390848,   box := { reLo := (62746991847777769601619482512572249789264710047445 : Rat)/775762740790946818979290814990517975133225427664896,            reHi := (761309045657216719534141464458760081020847158575977 : Rat)/775762740790946818979290814990517975133225427664896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 7, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C77_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C77_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C79_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2, a6 := 0 },   conductor := 79,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, -1, -3, 1, -1, 3, -2, 3, -2, 1, 3, 1, 3, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3817450434286023044586181640625,   alphaHi := (5397215081808807583452231630848 : Rat)/7634900868572045993804931640625,   finite := ((1210497469096807 : Rat)/9007199254740992, (3849142848439269 : Rat)/4503599627370496),   tail := (120307818583797278758875771732616424560546875 : Rat)/1476657374276187207317634915113601887803277312,   box := { reLo := (81939334096034031248128645655122747792547058085177 : Rat)/1548387482889027277100296348750160213105209310707712,            reHi := (724764938784535232967790761178035160618964592472059 : Rat)/774193741444513638550148174375080106552604655353856,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [79] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C79_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C79_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C82_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -12, a6 := -16 },   conductor := 82,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -2, 1, -2, 2, -4, -1, 1, 2, -2, -2, 4, 4, 4, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/7778516604196929264068603515625,   finite := ((1200668727533991 : Rat)/9007199254740992, (3960764852837207 : Rat)/4503599627370496),   tail := (45353697239890496811241469825649261474609375 : Rat)/490659065463126502932016156692684386269659136,   box := { reLo := (21025679051380024756768428020435519816220172407753 : Rat)/514493320227063335938441773520188223017094098190336,            reHi := (250018210523033851458986118841569035055193760998681 : Rat)/257246660113531667969220886760094111508547049095168,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 41, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C82_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C82_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C82_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2, a6 := 0 },   conductor := 82,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -2, 1, -2, 2, -4, -1, 1, 2, -2, -2, 4, 4, 4, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/7778516604196929264068603515625,   finite := ((1200668727533991 : Rat)/9007199254740992, (3960764852837207 : Rat)/4503599627370496),   tail := (45353697239890496811241469825649261474609375 : Rat)/490659065463126502932016156692684386269659136,   box := { reLo := (21025679051380024756768428020435519816220172407753 : Rat)/514493320227063335938441773520188223017094098190336,            reHi := (250018210523033851458986118841569035055193760998681 : Rat)/257246660113531667969220886760094111508547049095168,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C82_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C82_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C82_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C83_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 1, a6 := 0 },   conductor := 83,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, -1, -2, 1, -3, 3, -2, 2, 3, 1, -6, 3, 2, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3912901427480499172210693359375,   alphaHi := (5397215081808807583452231630848 : Rat)/7825802854960998249053955078125,   finite := ((74543708549861 : Rat)/562949953421312, (8124711673914343 : Rat)/9007199254740992),   tail := (7077868811774598837395644185333251953125 : Rat)/73518355463053534619636037635764278788096,   box := { reLo := (174139270651186420511455174228898590184911643 : Rat)/4818098943626676444832467362497447774656659456,            reHi := (76958352649145066257116278301247606242055478809 : Rat)/77089583098026823117319477799959164394506551296,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [83] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C83_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C83_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C88_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 4 },   conductor := 88,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -3, 0, -3, 0, -2, 0, 6, 0, -1, 0, 0, 0, 9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8058072917233848285675048828125,   alphaHi := (1349303770452201895863057907712 : Rat)/2014518229308462047576904296875,   finite := ((1263973079157721 : Rat)/9007199254740992, (9541446074952029 : Rat)/9007199254740992),   tail := (21360570730819568745868214199161529541015625 : Rat)/182744077437661152155785450990902782378115072,   box := { reLo := (2245923823749024260511134653957520603706898837793 : Rat)/95810526871636490141452442529118437967457194868736,            reHi := (112692457458224491432855847825431692521201948533957 : Rat)/95810526871636490141452442529118437967457194868736,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C88_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C88_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C89_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1, a6 := 0 },   conductor := 89,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, -1, -1, 1, -4, 3, -2, 1, -2, 1, 2, 4, 1, -1, 3, 2, -5, 1, 4, 2, 7, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/4051864043326417064666748046875,   alphaHi := (5397215081808807583452231630848 : Rat)/8103728086652834033966064453125,   finite := ((1980689233853169 : Rat)/9007199254740992, (7899802974796523 : Rat)/9007199254740992),   tail := (9839985568608821213694101796054840087890625 : Rat)/81122148416549900239041027485508422487506944,   box := { reLo := (8387381131232692605447102721366467265156541985783 : Rat)/85062737898032228193052684436644479618260081311744,            reHi := (84922614049071148106739236036844049797567475966861 : Rat)/85062737898032228193052684436644479618260081311744,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [89] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C89_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C89_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C91_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 1, a6 := 0 },   conductor := 91,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -2, 0, 2, -3, 0, -1, 0, -3, 6, -6, 0, -1, 2, 0, -4, 4, 6, 5, -6, 0, 12, 3, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2048568836229069232940673828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8194275344916276836395263671875,   finite := ((1715835966567447 : Rat)/9007199254740992, (913214899209295 : Rat)/1125899906842624),   tail := (47490010649139960600360412542819976806640625 : Rat)/364155438416414627104135486348429598532829184,   box := { reLo := (45886032779106401415716416213637050507479923786663 : Rat)/763689305985860768060691943466581829422319788883968,            reHi := (89877557604523519862070598694672197189196647209055 : Rat)/95461163248232596007586492933322728677789973610496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C91_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C91_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C91_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -117, a6 := -1245 },   conductor := 91,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, -2, -3, 0, 1, 0, 1, 0, 0, 4, 1, 0, 6, 4],   alphaLo := (1349303770452201895858762940416 : Rat)/2048568836229069232940673828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8194275344916276836395263671875,   finite := ((1195640933189811 : Rat)/9007199254740992, (5055934075477419 : Rat)/4503599627370496),   tail := (47490010649139960600360412542819976806640625 : Rat)/364155438416414627104135486348429598532829184,   box := { reLo := (1780493112227764994560391681572792146794751103619 : Rat)/763689305985860768060691943466581829422319788883968,            reHi := (478472068003205836558152232910309240733664945709051 : Rat)/381844652992930384030345971733290914711159894441984,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 7, 7, 7, 7, 7, 7, 7, 7, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C91_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C91_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C91_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -7, a6 := 5 },   conductor := 91,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, -2, -3, 0, 1, 0, 1, 0, 0, 4, 1, 0, 6, 4],   alphaLo := (1349303770452201895858762940416 : Rat)/2048568836229069232940673828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8194275344916276836395263671875,   finite := ((1195640933189811 : Rat)/9007199254740992, (5055934075477419 : Rat)/4503599627370496),   tail := (47490010649139960600360412542819976806640625 : Rat)/364155438416414627104135486348429598532829184,   box := { reLo := (1780493112227764994560391681572792146794751103619 : Rat)/763689305985860768060691943466581829422319788883968,            reHi := (478472068003205836558152232910309240733664945709051 : Rat)/381844652992930384030345971733290914711159894441984,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C91_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C91_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C91_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C91_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 13, a6 := 42 },   conductor := 91,   policy := { precisionBits := 53 },   termLimit := 16,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, -2, -3, 0, 1, 0, 1, 0, 0, 4, 1, 0, 6, 4],   alphaLo := (1349303770452201895858762940416 : Rat)/2048568836229069232940673828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8194275344916276836395263671875,   finite := ((1195640933189811 : Rat)/9007199254740992, (5055934075477419 : Rat)/4503599627370496),   tail := (47490010649139960600360412542819976806640625 : Rat)/364155438416414627104135486348429598532829184,   box := { reLo := (1780493112227764994560391681572792146794751103619 : Rat)/763689305985860768060691943466581829422319788883968,            reHi := (478472068003205836558152232910309240733664945709051 : Rat)/381844652992930384030345971733290914711159894441984,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [7, 7, 7, 13, 13, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C91_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C91_b3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C91_b3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C92_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 1 },   conductor := 92,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -3, 0, -2, 0, -4, 0, 6, 0, 2, 0, -5, 0, 6, 0, 4, 0, -2, 0, 12, 0, 1, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8239175819901596736907958984375,   finite := ((35263964128563 : Rat)/140737488355328, (4480965302897107 : Rat)/4503599627370496),   tail := (49141280166925983137535329297733306884765625 : Rat)/363699823242711734395839813993313445775147008,   box := { reLo := (2751814748690013723356951571372017453123392869723 : Rat)/23835431616034356225365758049865789982320034316288,            reHi := (861957175502869797254603050339938355952404291460347 : Rat)/762733811713099399211704257595705279434241098121216,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C92_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C92_a1
