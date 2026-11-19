module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C101_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1, a6 := -1 },   conductor := 101,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, -2, -1, 0, -2, 0, 1, 0, -2, 4, 1, 0, 2, 4, 3, 0, -5, 2, 4, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8632777424316382122039794921875,   alphaHi := (2698607540904403791726115815424 : Rat)/4316388712158191013336181640625,   finite := ((2651508586026997 : Rat)/9007199254740992, (9776608846384001 : Rat)/9007199254740992),   tail := (523084645896308762952194385185146331787109375 : Rat)/2874845638736675962822620380634462425211469824,   box := { reLo := (169451247314507766119454931960154581869590543566117 : Rat)/1507247070241974367196345994122081035989271091085312,            reHi := (1910245566183301740782125013379306334593675769150961 : Rat)/1507247070241974367196345994122081035989271091085312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [101] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C101_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C101_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C102_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2, a6 := 0 },   conductor := 102,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, 1, -4, 1, -2, -1, 1, 4, 0, -1, -6, 2, 4, 1, -1, -1, 4, -4, 2, 0, 6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8675408683211124134063720703125,   alphaHi := (1349303770452201895863057907712 : Rat)/2168852170802781009674072265625,   finite := ((1177821484403821 : Rat)/4503599627370496, (548715091723217 : Rat)/562949953421312),   tail := (538747765449396788654553808337879180908203125 : Rat)/2870776930691030859701457882144777235958071296,   box := { reLo := (55585901146647774540141901048802614296317320773049 : Rat)/752556947719069593685578975056960483742992641818624,            reHi := (109344642627204198806832848312091981553528511525773 : Rat)/94069618464883699210697371882120060467874080227328,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C102_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C102_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C102_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 8, a6 := 10 },   conductor := 102,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, 1, -4, 1, -2, -1, 1, 4, 0, -1, -6, 2, 4, 1, -1, -1, 4, -4, 2, 0, 6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8675408683211124134063720703125,   alphaHi := (1349303770452201895863057907712 : Rat)/2168852170802781009674072265625,   finite := ((1177821484403821 : Rat)/4503599627370496, (548715091723217 : Rat)/562949953421312),   tail := (538747765449396788654553808337879180908203125 : Rat)/2870776930691030859701457882144777235958071296,   box := { reLo := (55585901146647774540141901048802614296317320773049 : Rat)/752556947719069593685578975056960483742992641818624,            reHi := (109344642627204198806832848312091981553528511525773 : Rat)/94069618464883699210697371882120060467874080227328,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 17, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C102_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C102_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C102_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C106_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -7, a6 := 5 },   conductor := 106,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, 1, -4, 1, 0, -1, -2, 4, -4, -1, 1, 0, 4, 1, 5, 2, -7, -4, 0, 4, 1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/2210969737362551784515380859375,   alphaHi := (5397215081808807583452231630848 : Rat)/8843878949450207042694091796875,   finite := ((305934687635067 : Rat)/1125899906842624, (9021554064213181 : Rat)/9007199254740992),   tail := (37739264817416519989821100063037872314453125 : Rat)/178381922799140360008621326363133190678249472,   box := { reLo := (2813195597627029097100970925374695045435213467269 : Rat)/46761750770257850534100028978137187137159029587968,            reHi := (453835175966064824164291877540979551192016233049667 : Rat)/374094006162062804272800231825097497097272236703744,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 53] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C106_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C106_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C112_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 },   conductor := 112,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -4, 0, -1, 0, 1, 0, 0, 0, 0, 0, 8, 0, -2, 0, 2, 0, 2, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   finite := ((3008030843631027 : Rat)/9007199254740992, (5334132766546087 : Rat)/4503599627370496),   tail := (11811205609887788124074432197551727294921875 : Rat)/47133179186103571059895619727688494751940608,   box := { reLo := (8240382741953613776881793888472799714613955175971 : Rat)/98845440996495476255402218703161382146021749948416,            reHi := (70921978138287095637870473566621599434376616555351 : Rat)/49422720498247738127701109351580691073010874974208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C112_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C112_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C112_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 },   conductor := 112,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -4, 0, -1, 0, 1, 0, 0, 0, 0, 0, 8, 0, -2, 0, 2, 0, 2, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   finite := ((3008030843631027 : Rat)/9007199254740992, (5334132766546087 : Rat)/4503599627370496),   tail := (11811205609887788124074432197551727294921875 : Rat)/47133179186103571059895619727688494751940608,   box := { reLo := (8240382741953613776881793888472799714613955175971 : Rat)/98845440996495476255402218703161382146021749948416,            reHi := (70921978138287095637870473566621599434376616555351 : Rat)/49422720498247738127701109351580691073010874974208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C112_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C112_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C112_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C117_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -626, a6 := 6180 },   conductor := 117,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -2, 0, -4, 3, 0, 2, -4, 0, 1, 4, 0, -1, -2, 0, 0, 2, 0, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9291434887301352787017822265625,   alphaHi := (674651885226100947931528953856 : Rat)/1161429360912669086456298828125,   finite := ((1369471112446297 : Rat)/4503599627370496, (9922856852971903 : Rat)/9007199254740992),   tail := (802576319451515057685313915661334991455078125 : Rat)/2805261436948299895542907297167727339165974528,   box := { reLo := (13227230376916619341143682929910668017604242644249 : Rat)/735382454127375127817199890508736715598325226668032,            reHi := (2041061670777661513039442300831687941228855867785151 : Rat)/1470764908254750255634399781017473431196650453336064,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C117_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C117_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C117_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -768 },   conductor := 117,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -2, 0, -4, 3, 0, 2, -4, 0, 1, 4, 0, -1, -2, 0, 0, 2, 0, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9291434887301352787017822265625,   alphaHi := (674651885226100947931528953856 : Rat)/1161429360912669086456298828125,   finite := ((1369471112446297 : Rat)/4503599627370496, (9922856852971903 : Rat)/9007199254740992),   tail := (802576319451515057685313915661334991455078125 : Rat)/2805261436948299895542907297167727339165974528,   box := { reLo := (13227230376916619341143682929910668017604242644249 : Rat)/735382454127375127817199890508736715598325226668032,            reHi := (2041061670777661513039442300831687941228855867785151 : Rat)/1470764908254750255634399781017473431196650453336064,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C117_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C117_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C117_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C117_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 96 },   conductor := 117,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -2, 0, -4, 3, 0, 2, -4, 0, 1, 4, 0, -1, -2, 0, 0, 2, 0, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9291434887301352787017822265625,   alphaHi := (674651885226100947931528953856 : Rat)/1161429360912669086456298828125,   finite := ((1369471112446297 : Rat)/4503599627370496, (9922856852971903 : Rat)/9007199254740992),   tail := (802576319451515057685313915661334991455078125 : Rat)/2805261436948299895542907297167727339165974528,   box := { reLo := (13227230376916619341143682929910668017604242644249 : Rat)/735382454127375127817199890508736715598325226668032,            reHi := (2041061670777661513039442300831687941228855867785151 : Rat)/1470764908254750255634399781017473431196650453336064,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C117_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C117_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C117_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C117_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := 6 },   conductor := 117,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -2, 0, -4, 3, 0, 2, -4, 0, 1, 4, 0, -1, -2, 0, 0, 2, 0, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9291434887301352787017822265625,   alphaHi := (674651885226100947931528953856 : Rat)/1161429360912669086456298828125,   finite := ((1369471112446297 : Rat)/4503599627370496, (9922856852971903 : Rat)/9007199254740992),   tail := (802576319451515057685313915661334991455078125 : Rat)/2805261436948299895542907297167727339165974528,   box := { reLo := (13227230376916619341143682929910668017604242644249 : Rat)/735382454127375127817199890508736715598325226668032,            reHi := (2041061670777661513039442300831687941228855867785151 : Rat)/1470764908254750255634399781017473431196650453336064,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C117_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C117_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C117_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C118_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 1, a6 := 1 },   conductor := 118,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, -1, 1, -3, 1, -1, -1, -2, 3, -2, -1, -2, 1, 3, 1, -2, 2, 3, -3, 1, 2, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/9331057390666348552703857421875,   alphaHi := (2698607540904403791726115815424 : Rat)/4665528695333174228668212890625,   finite := ((2753872395646461 : Rat)/9007199254740992, (2443732535227567 : Rat)/2251799813685248),   tail := (822061380036928118764749089898586273193359375 : Rat)/2800616035831604328567274682375421587858915328,   box := { reLo := (17931949246063870508099648252510309833499573376637 : Rat)/1468329380194080170215879308673245033455374999486464,            reHi := (506119929943625911597000579989663171554701399368239 : Rat)/367082345048520042553969827168311258363843749871616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 59] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C118_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C118_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C121_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -887, a6 := -10143 },   conductor := 121,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -1, -2, -3, 0, 0, 0, -2, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 6, 0, 0, -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9448928051200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/550000000000000000000,   finite := ((416419798529255 : Rat)/1125899906842624, (11566484204147333 : Rat)/9007199254740992),   tail := (440955630913705402113052420713710784912109375 : Rat)/1393244355760212777416031161358881123532275712,   box := { reLo := (4872134313931344008461225840806969597302256588965 : Rat)/91307662099101304580737018190815633311811221061632,            reHi := (1169200641077343584240831898886378311919277053069919 : Rat)/730461296792810436645896145526525066494489768493056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C121_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C121_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C121_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7, a6 := 10 },   conductor := 121,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -1, -2, -3, 0, 0, 0, -2, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 6, 0, 0, -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/9448928051200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/550000000000000000000,   finite := ((416419798529255 : Rat)/1125899906842624, (11566484204147333 : Rat)/9007199254740992),   tail := (440955630913705402113052420713710784912109375 : Rat)/1393244355760212777416031161358881123532275712,   box := { reLo := (4872134313931344008461225840806969597302256588965 : Rat)/91307662099101304580737018190815633311811221061632,            reHi := (1169200641077343584240831898886378311919277053069919 : Rat)/730461296792810436645896145526525066494489768493056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [11, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C121_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C121_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C121_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C122_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 2, a6 := 0 },   conductor := 122,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -1, -2, 1, 1, 2, -5, -1, 1, -1, -3, -2, -3, 5, -2, 1, 0, -1, 0, 1, 10, 3, 5, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/9487892868266515827178955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2371973217066628932952880859375,   finite := ((1899962637771319 : Rat)/4503599627370496, (7264740503821457 : Rat)/9007199254740992),   tail := (451161726073836920258557369841861724853515625 : Rat)/1390858668254807552344874956906314466127249408,   box := { reLo := (35549032191894152133119878419678147042146740159903 : Rat)/364605254730988271001894900703248899408461668810752,            reHi := (824682115648279131031370207632792542843988671007209 : Rat)/729210509461976542003789801406497798816923337621504,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 61] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C122_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C122_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C123_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -10, a6 := 10 },   conductor := 123,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -2, 1, 2, -4, -2, -2, 0, 1, 8, -3, 2, -6, 4, -4, -4, 3, -2, 0, -8, -2, 6, -6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2381674579506127071380615234375,   alphaHi := (5397215081808807583452231630848 : Rat)/9526698318024508190155029296875,   finite := ((3501094617935631 : Rat)/9007199254740992, (3456265960885815 : Rat)/4503599627370496),   tail := (23074134821211727751553746698169708251953125 : Rat)/69422888449284288195482318760096650055647232,   box := { reLo := (8200940477178305982911673515928289873438715747177 : Rat)/145590349357193443557732135752374209857500703883264,            reHi := (80061292097982957733147961191283973095175029663105 : Rat)/72795174678596721778866067876187104928750351941632,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C123_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C123_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C123_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 20, a6 := -890 },   conductor := 123,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 2,   cutoff := 8,   coefficients := [1, -2, 1, 2, -4, -2, -2, 0, 1, 8, -3, 2, -6, 4, -4, -4, 3, -2, 0, -8, -2, 6, -6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2381674579506127071380615234375,   alphaHi := (5397215081808807583452231630848 : Rat)/9526698318024508190155029296875,   finite := ((3501094617935631 : Rat)/9007199254740992, (3456265960885815 : Rat)/4503599627370496),   tail := (23074134821211727751553746698169708251953125 : Rat)/69422888449284288195482318760096650055647232,   box := { reLo := (8200940477178305982911673515928289873438715747177 : Rat)/145590349357193443557732135752374209857500703883264,            reHi := (80061292097982957733147961191283973095175029663105 : Rat)/72795174678596721778866067876187104928750351941632,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 41, 41, 41, 41, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C123_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C123_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C123_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C123_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 1, a6 := -1 },   conductor := 123,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -1, -2, -2, 0, -4, 0, 1, 0, 5, 2, -4, 0, 2, 4, -5, 0, -2, 4, 4, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2381674579506127071380615234375,   alphaHi := (5397215081808807583452231630848 : Rat)/9526698318024508190155029296875,   finite := ((3321779931836159 : Rat)/9007199254740992, (2936263259738319 : Rat)/2251799813685248),   tail := (23074134821211727751553746698169708251953125 : Rat)/69422888449284288195482318760096650055647232,   box := { reLo := (5302538093068028319383307193671744955131472853753 : Rat)/145590349357193443557732135752374209857500703883264,            reHi := (59558593023078991000929521403341357888060871362473 : Rat)/36397587339298360889433033938093552464375175970816,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C123_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C123_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C124_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 1 },   conductor := 124,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -3, 0, -1, 0, 1, 0, -6, 0, 2, 0, 6, 0, 6, 0, -1, 0, 2, 0, -6, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1195668292509461116790771484375,   alphaHi := (5397215081808807583452231630848 : Rat)/9565346340075688838958740234375,   finite := ((3329587460992849 : Rat)/9007199254740992, (5780680993997969 : Rat)/4503599627370496),   tail := (4719181244470271326714961648151397705078125 : Rat)/13860418678749468009510413117252971849056256,   box := { reLo := (1696343742634637711126196523945013116848756866303 : Rat)/58134809505953608670161563779346608838384050765824,            reHi := (47206860836218874172207373307022153671703951018943 : Rat)/29067404752976804335080781889673304419192025382912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C124_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C124_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C124_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 18, a6 := -11 },   conductor := 124,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -3, 0, -1, 0, 1, 0, -6, 0, 2, 0, 6, 0, 6, 0, -1, 0, 2, 0, -6, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1195668292509461116790771484375,   alphaHi := (5397215081808807583452231630848 : Rat)/9565346340075688838958740234375,   finite := ((3329587460992849 : Rat)/9007199254740992, (5780680993997969 : Rat)/4503599627370496),   tail := (4719181244470271326714961648151397705078125 : Rat)/13860418678749468009510413117252971849056256,   box := { reLo := (1696343742634637711126196523945013116848756866303 : Rat)/58134809505953608670161563779346608838384050765824,            reHi := (47206860836218874172207373307022153671703951018943 : Rat)/29067404752976804335080781889673304419192025382912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31, 31, 31] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C124_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C124_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C124_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C99_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -17, a6 := 30 },   conductor := 99,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -4, 0, -2, 3, 0, 4, -1, 0, -2, 2, 0, -1, 2, 0, -6, 4, 0, 1, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/4273438502303789615631103515625,   alphaHi := (5397215081808807583452231630848 : Rat)/8546877004607579135894775390625,   finite := ((2276178009546953 : Rat)/9007199254740992, (2190717222739641 : Rat)/2251799813685248),   tail := (49249009077521065077607175119686126708984375 : Rat)/288286220137978148005576880165639661144768512,   box := { reLo := (24749328949686341442317885472541794686062606283483 : Rat)/302290011567400574523095782696565773324536787238912,            reHi := (86432846379434372654909540551849354735701635835051 : Rat)/75572502891850143630773945674141443331134196809728,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 11, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C99_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C99_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C99_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := 0 },   conductor := 99,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, -1, 0, -1, -4, 0, -2, 3, 0, 4, -1, 0, -2, 2, 0, -1, 2, 0, -6, 4, 0, 1, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/4273438502303789615631103515625,   alphaHi := (5397215081808807583452231630848 : Rat)/8546877004607579135894775390625,   finite := ((2276178009546953 : Rat)/9007199254740992, (2190717222739641 : Rat)/2251799813685248),   tail := (49249009077521065077607175119686126708984375 : Rat)/288286220137978148005576880165639661144768512,   box := { reLo := (24749328949686341442317885472541794686062606283483 : Rat)/302290011567400574523095782696565773324536787238912,            reHi := (86432846379434372654909540551849354735701635835051 : Rat)/75572502891850143630773945674141443331134196809728,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 11] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C99_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C99_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C99_a2
