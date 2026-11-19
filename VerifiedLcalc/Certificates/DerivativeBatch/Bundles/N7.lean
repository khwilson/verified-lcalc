module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C224_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -8 },   conductor := 224,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -1, 0, 1, 0, -4, 0, -4, 0, 0, 0, -2, 0, -6, 0, 2, 0, 8, 0, -5, 0, 4, 0, 2, 0, -4,                    0, 8, 0, 0, 0, 10, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12856236887224721050262451171875,   alphaHi := (2698607540904403791726115815424 : Rat)/6428118443612360477447509765625,   finite := ((7896256778942551 : Rat)/9007199254740992, (4709204454748753 : Rat)/2251799813685248),   tail := (140134247626199519358131252027225494384765625 : Rat)/1504473445532456140902954002244264586591076352,   box := { reLo := (1236038696049051316701572439885440957482215993706081 : Rat)/1577554747622640730403455895857281983149324476874752,            reHi := (861523128632484743205282546531037575160754527372343 : Rat)/394388686905660182600863973964320495787331119218688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C224_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C224_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C224_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 0 },   conductor := 224,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -1, 0, 1, 0, -4, 0, -4, 0, 0, 0, -2, 0, -6, 0, 2, 0, 8, 0, -5, 0, 4, 0, 2, 0, -4,                    0, 8, 0, 0, 0, 10, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12856236887224721050262451171875,   alphaHi := (2698607540904403791726115815424 : Rat)/6428118443612360477447509765625,   finite := ((7896256778942551 : Rat)/9007199254740992, (4709204454748753 : Rat)/2251799813685248),   tail := (140134247626199519358131252027225494384765625 : Rat)/1504473445532456140902954002244264586591076352,   box := { reLo := (1236038696049051316701572439885440957482215993706081 : Rat)/1577554747622640730403455895857281983149324476874752,            reHi := (861523128632484743205282546531037575160754527372343 : Rat)/394388686905660182600863973964320495787331119218688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C224_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C224_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C224_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C225_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -75, a6 := 256 },   conductor := 225,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, 0, 0, -3, 0, 0, 0, -2, 0, 1, 6, 0, -4, -2, 0, -5, 0, 0, 4, -6, 0, 0, -2, 0, -6, -10, 0,                    -3, 8, 0, 4, 0, 0, 2, 10, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12884901888000000095367431640625,   alphaHi := (314159265358979323847 : Rat)/750000000000000000000,   finite := ((4754978682995175 : Rat)/9007199254740992, (3712622842298661 : Rat)/2251799813685248),   tail := (142561196369648662092220817517948150634765625 : Rat)/1504252015881140094467556168540251728790945792,   box := { reLo := (683196024930995999776492964870561221302398234812675 : Rat)/1577322561804582355696412176983262996768694774792192,            reHi := (687518584327545225841719200024067896662426007880761 : Rat)/394330640451145588924103044245815749192173693698048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C225_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C225_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C225_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 375, a6 := -12344 },   conductor := 225,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, 0, 0, -3, 0, 0, 0, -2, 0, 1, 6, 0, -4, -2, 0, -5, 0, 0, 4, -6, 0, 0, -2, 0, -6, -10, 0,                    -3, 8, 0, 4, 0, 0, 2, 10, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12884901888000000095367431640625,   alphaHi := (314159265358979323847 : Rat)/750000000000000000000,   finite := ((4754978682995175 : Rat)/9007199254740992, (3712622842298661 : Rat)/2251799813685248),   tail := (142561196369648662092220817517948150634765625 : Rat)/1504252015881140094467556168540251728790945792,   box := { reLo := (683196024930995999776492964870561221302398234812675 : Rat)/1577322561804582355696412176983262996768694774792192,            reHi := (687518584327545225841719200024067896662426007880761 : Rat)/394330640451145588924103044245815749192173693698048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 0],                kodaira := -9 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C225_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C225_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C225_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C225_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -34 },   conductor := 225,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, -5, 0, 0, 0, 0, 0, -5, 0, 0, 4, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, -7, 0,                    0, 0, 0, 0, 10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12884901888000000095367431640625,   alphaHi := (314159265358979323847 : Rat)/750000000000000000000,   finite := ((4295458988413993 : Rat)/4503599627370496, (20458463568768827 : Rat)/9007199254740992),   tail := (142561196369648662092220817517948150634765625 : Rat)/1504252015881140094467556168540251728790945792,   box := { reLo := (677468987601887195085730634815291071786648932521293 : Rat)/788661280902291177848206088491631498384347387396096,            reHi := (3732131115026662038760482526344199099511755314863527 : Rat)/1577322561804582355696412176983262996768694774792192,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C225_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C225_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C225_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 1 },   conductor := 225,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, -5, 0, 0, 0, 0, 0, -5, 0, 0, 4, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, -7, 0,                    0, 0, 0, 0, 10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/12884901888000000095367431640625,   alphaHi := (314159265358979323847 : Rat)/750000000000000000000,   finite := ((4295458988413993 : Rat)/4503599627370496, (20458463568768827 : Rat)/9007199254740992),   tail := (142561196369648662092220817517948150634765625 : Rat)/1504252015881140094467556168540251728790945792,   box := { reLo := (677468987601887195085730634815291071786648932521293 : Rat)/788661280902291177848206088491631498384347387396096,            reHi := (3732131115026662038760482526344199099511755314863527 : Rat)/1577322561804582355696412176983262996768694774792192,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C225_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C225_c2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C225_c2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C226_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -45, a6 := -119 },   conductor := 226,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -4, -2, 0, 1, 1, -4, -4, -2, -2, 0, 8, 1, -2, 1, -2, -4, 0, -4, 4, -2, 11, -2, 4, 0, -4,                    8, 8, 1, 8, -2, 0, 1, -8, -2, 4, -4],   alphaLo := (2698607540904403791717525880832 : Rat)/6456751629618688297271728515625,   alphaHi := (5397215081808807583452231630848 : Rat)/12913503259237376499176025390625,   finite := ((9424379443144201 : Rat)/9007199254740992, (11843533247459847 : Rat)/4503599627370496),   tail := (725071725161817013541589109676361083984375 : Rat)/7520143785257304765980711009708563115278336,   box := { reLo := (14980748062198115087730114520488001224201212993691 : Rat)/15770884579539927204585980055432332554332192899072,            reHi := (21497371070466254557351821206621608119319733161877 : Rat)/7885442289769963602292990027716166277166096449536,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 113, 113] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C226_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C226_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C226_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5, a6 := 1 },   conductor := 226,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -4, -2, 0, 1, 1, -4, -4, -2, -2, 0, 8, 1, -2, 1, -2, -4, 0, -4, 4, -2, 11, -2, 4, 0, -4,                    8, 8, 1, 8, -2, 0, 1, -8, -2, 4, -4],   alphaLo := (2698607540904403791717525880832 : Rat)/6456751629618688297271728515625,   alphaHi := (5397215081808807583452231630848 : Rat)/12913503259237376499176025390625,   finite := ((9424379443144201 : Rat)/9007199254740992, (11843533247459847 : Rat)/4503599627370496),   tail := (725071725161817013541589109676361083984375 : Rat)/7520143785257304765980711009708563115278336,   box := { reLo := (14980748062198115087730114520488001224201212993691 : Rat)/15770884579539927204585980055432332554332192899072,            reHi := (21497371070466254557351821206621608119319733161877 : Rat)/7885442289769963602292990027716166277166096449536,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 113] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C226_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C226_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C226_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C228_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 9 },   conductor := 228,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, 1, 0, 1, 0, -5, 0, -6, 0, 3, 0, -5, 0, 1, 0, -1, 0, 4, 0, 4, 0, -1, 0, 6, 0, 6,                    0, 5, 0, -3, 0, -8, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6485258397940499782562255859375,   alphaHi := (5397215081808807583452231630848 : Rat)/12970516795880999469757080078125,   finite := ((8395199907717135 : Rat)/9007199254740992, (9981999683005695 : Rat)/4503599627370496),   tail := (18749947628160150668713386762142181396484375 : Rat)/187947094228858505440363500656758543957884928,   box := { reLo := (328051139093707283334867710785636921552982064402555 : Rat)/394153624556239072401269196129322493978366292525056,            reHi := (456471483261721548462174791033161535982831650542635 : Rat)/197076812278119536200634598064661246989183146262528,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 19] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C228_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C228_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C229_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := -1 },   conductor := 229,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, -3, -1, 2, 3, -2, 3, -3, -1, -6, -2, -3, -1, -7, 2, 3, 3, 2, 3, 4, 3, 4, 6, -5, -2, -6,                    3, 4, -5, -3, 7, -6, 2, 2, -3, -6, -9],   alphaLo := (1349303770452201895858762940416 : Rat)/3249732447786851024627685546875,   alphaHi := (5397215081808807583452231630848 : Rat)/12998929791147404003143310546875,   finite := ((7094089401579055 : Rat)/9007199254740992, (18131445936113069 : Rat)/9007199254740992),   tail := (38132958824707251408187859105205535888671875 : Rat)/375837002650617806505512614544051463763525632,   box := { reLo := (1081614819782793006731579905001019684239741636771995 : Rat)/1576374643565496868297297581232573230669210612400128,            reHi := (3333175299995314822897301693910252563613983541873521 : Rat)/1576374643565496868297297581232573230669210612400128,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [229] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C229_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C229_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C232_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -4 },   conductor := 232,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, 2, 0, -2, 0, -3, 0, -5, 0, 3, 0, -4, 0, 0, 0, -2, 0, 0, 0, 4, 0, 5, 0, -1, 0, 9,                    0, 3, 0, -6, 0, 8, 0, 5, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6541899284688366413116455078125,   alphaHi := (5397215081808807583452231630848 : Rat)/13083798569376732730865478515625,   finite := ((1066073684539739 : Rat)/1125899906842624, (20268974592632573 : Rat)/9007199254740992),   tail := (40072030995114075153526360879421234130859375 : Rat)/375662705714915965968230850830271883889344512,   box := { reLo := (82740334063133795743383059957526138989211495172133 : Rat)/98477724326930930982775908160050792730288327753728,            reHi := (1856879006431062804564433981191451694402693684601731 : Rat)/787821794615447447862207265280406341842306622029824,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C232_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C232_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C234_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -63, a6 := 209 },   conductor := 234,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -2, -1, 0, 2, -4, 0, -1, 2, 0, 1, 0, 0, -6, -2, 0, 4, 4, 0, -1, 1, 0, -2, -8, 0,                    -2, -1, 0, 0, 4, 0, 6, 6, 0, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/6570036615764051532745361328125,   alphaHi := (5397215081808807583452231630848 : Rat)/13140073231528102970123291015625,   finite := ((938031821616509 : Rat)/1125899906842624, (1116050482667619 : Rat)/562949953421312),   tail := (646846558226869523918714774227142333984375 : Rat)/5867878545557483624451299274928423851524096,   box := { reLo := (1111992709679671889341233213161654127852951422459 : Rat)/1538229153446620987248161397126836742133932621824,            reHi := (1609556126135622138029284056279688811121090124069 : Rat)/769114576723310493624080698563418371066966310912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 13, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C234_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C234_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C234_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 5 },   conductor := 234,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -2, -1, 0, 2, -4, 0, -1, 2, 0, 1, 0, 0, -6, -2, 0, 4, 4, 0, -1, 1, 0, -2, -8, 0,                    -2, -1, 0, 0, 4, 0, 6, 6, 0, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/6570036615764051532745361328125,   alphaHi := (5397215081808807583452231630848 : Rat)/13140073231528102970123291015625,   finite := ((938031821616509 : Rat)/1125899906842624, (1116050482667619 : Rat)/562949953421312),   tail := (646846558226869523918714774227142333984375 : Rat)/5867878545557483624451299274928423851524096,   box := { reLo := (1111992709679671889341233213161654127852951422459 : Rat)/1538229153446620987248161397126836742133932621824,            reHi := (1609556126135622138029284056279688811121090124069 : Rat)/769114576723310493624080698563418371066966310912,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 13] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C234_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C234_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C234_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C235_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -5, a6 := 0 },   conductor := 235,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, -1, 1, 1, 1, 3, -2, -1, -3, 1, -3, -1, -1, -1, -6, 2, -7, -1, -1, 3, 4, -3, 1, 3, 5, -1,                    -10, 1, 3, -5, 3, 6, 1, 2, 12, 7, 3, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/13168120378127995586395263671875,   alphaHi := (2698607540904403791726115815424 : Rat)/6584060189063997745513916015625,   finite := ((6016011401603103 : Rat)/9007199254740992, (16761189031243943 : Rat)/9007199254740992),   tail := (42071342816899680573719542585086822509765625 : Rat)/375484303974544032280257716141750036520239104,   box := { reLo := (218857648569104568129577300620965353520792290706361 : Rat)/393723829524411483192303514961051686294246238715904,            reHi := (776782208686778961513174328557221697625942529251441 : Rat)/393723829524411483192303514961051686294246238715904,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 47] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C235_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C235_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C236_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 2 },   conductor := 236,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -3, 0, -2, 0, -2, 0, 0, 0, 1, 0, 2, 0, -5, 0, 3, 0, -4, 0, -4, 0, 5, 0, 5, 0, -4,                    0, 2, 0, 3, 0, 8, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13196107913162053585052490234375,   alphaHi := (2698607540904403791726115815424 : Rat)/6598053956581026744842529296875,   finite := ((8821602184210145 : Rat)/9007199254740992, (20698561369598283 : Rat)/9007199254740992),   tail := (171005028711483670315163049223423004150390625 : Rat)/1501695702768106498482784053391916829239148544,   box := { reLo := (1362884152260501790010326770394856168793336513467515 : Rat)/1574642073225770039753083771569482581136269423673344,            reHi := (3797842309504597471054145187259033887047074489719081 : Rat)/1574642073225770039753083771569482581136269423673344,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 59] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C236_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C236_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C238_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8, a6 := 6 },   conductor := 238,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -1, -1, -3, 2, -2, 0, 0, 1, 0, 1, -1, 3, -2, -2, 0, 2, -8, 0, -1, 0, 0, -1, 0, 0,                    8, -1, 0, 1, 2, -3, -4, 2, 0, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/13251905658497382068634033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3312976414624345493316650390625,   finite := ((7610931298341667 : Rat)/9007199254740992, (18108703672577767 : Rat)/9007199254740992),   tail := (176525658564526903977347883649539947509765625 : Rat)/1501207217016007380640928080162456158932566016,   box := { reLo := (1145012585099140667051135516802121012388169168387491 : Rat)/1574129858789776955162941802584427629308874342793216,            reHi := (3349841388913697012223292489670583195000281047762791 : Rat)/1574129858789776955162941802584427629308874342793216,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 7, 7, 17, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C238_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C238_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C238_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 2, a6 := 0 },   conductor := 238,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, -1, -1, -3, 2, -2, 0, 0, 1, 0, 1, -1, 3, -2, -2, 0, 2, -8, 0, -1, 0, 0, -1, 0, 0,                    8, -1, 0, 1, 2, -3, -4, 2, 0, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/13251905658497382068634033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3312976414624345493316650390625,   finite := ((7610931298341667 : Rat)/9007199254740992, (18108703672577767 : Rat)/9007199254740992),   tail := (176525658564526903977347883649539947509765625 : Rat)/1501207217016007380640928080162456158932566016,   box := { reLo := (1145012585099140667051135516802121012388169168387491 : Rat)/1574129858789776955162941802584427629308874342793216,            reHi := (3349841388913697012223292489670583195000281047762791 : Rat)/1574129858789776955162941802584427629308874342793216,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 7, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C238_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C238_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C238_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C238_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -700, a6 := 7056 },   conductor := 238,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -4, -2, 1, 1, 1, -4, -6, -2, -2, 1, 8, 1, -1, 1, 0, -4, -2, -6, -4, -2, 11, -2, 4, 1, 8,                    8, 0, 1, 12, -1, -4, 1, 4, 0, 4, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/13251905658497382068634033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3312976414624345493316650390625,   finite := ((9971935487739157 : Rat)/9007199254740992, (771957855385857 : Rat)/281474976710656),   tail := (176525658564526903977347883649539947509765625 : Rat)/1501207217016007380640928080162456158932566016,   box := { reLo := (1557629991037188159280496775696587958097877877530261 : Rat)/1574129858789776955162941802584427629308874342793216,            reHi := (140694465880600187755317387335267323179585812319361 : Rat)/49191558087180529848841931330763363415902323212288,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 17, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C238_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C238_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C238_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -60, a6 := 16 },   conductor := 238,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -4, -2, 1, 1, 1, -4, -6, -2, -2, 1, 8, 1, -1, 1, 0, -4, -2, -6, -4, -2, 11, -2, 4, 1, 8,                    8, 0, 1, 12, -1, -4, 1, 4, 0, 4, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/13251905658497382068634033203125,   alphaHi := (1349303770452201895863057907712 : Rat)/3312976414624345493316650390625,   finite := ((9971935487739157 : Rat)/9007199254740992, (771957855385857 : Rat)/281474976710656),   tail := (176525658564526903977347883649539947509765625 : Rat)/1501207217016007380640928080162456158932566016,   box := { reLo := (1557629991037188159280496775696587958097877877530261 : Rat)/1574129858789776955162941802584427629308874342793216,            reHi := (140694465880600187755317387335267323179585812319361 : Rat)/49191558087180529848841931330763363415902323212288,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C238_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C238_c2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C238_c2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C240_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -216, a6 := 1296 },   conductor := 240,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -4, 0, 1, 0, 0, 0, -6, 0, 1, 0, -2, 0, -4, 0, 4, 0, 8, 0, 1, 0, -1, 0, -6, 0, 0,                    0, 0, 0, 4, 0, -6, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3326867361982700252532958984375,   alphaHi := (5397215081808807583452231630848 : Rat)/13307469447930800914764404296875,   finite := ((8975365268376919 : Rat)/9007199254740992, (10480825401544793 : Rat)/4503599627370496),   tail := (4553879961075255642778034517536163330078125 : Rat)/37517786505386571720512510865822757827903488,   box := { reLo := (137704486844711898370690697612106186485688730845689 : Rat)/157361002010688919313632506374563856448606911332352,            reHi := (192656285088126790625084285903597490930765234544983 : Rat)/78680501005344459656816253187281928224303455666176,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5] }
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C240_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C240_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C240_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -136, a6 := -560 },   conductor := 240,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -4, 0, 1, 0, 0, 0, -6, 0, 1, 0, -2, 0, -4, 0, 4, 0, 8, 0, 1, 0, -1, 0, -6, 0, 0,                    0, 0, 0, 4, 0, -6, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3326867361982700252532958984375,   alphaHi := (5397215081808807583452231630848 : Rat)/13307469447930800914764404296875,   finite := ((8975365268376919 : Rat)/9007199254740992, (10480825401544793 : Rat)/4503599627370496),   tail := (4553879961075255642778034517536163330078125 : Rat)/37517786505386571720512510865822757827903488,   box := { reLo := (137704486844711898370690697612106186485688730845689 : Rat)/157361002010688919313632506374563856448606911332352,            reHi := (192656285088126790625084285903597490930765234544983 : Rat)/78680501005344459656816253187281928224303455666176,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5] }
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C240_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C240_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C240_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C240_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 16 },   conductor := 240,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -4, 0, 1, 0, 0, 0, -6, 0, 1, 0, -2, 0, -4, 0, 4, 0, 8, 0, 1, 0, -1, 0, -6, 0, 0,                    0, 0, 0, 4, 0, -6, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3326867361982700252532958984375,   alphaHi := (5397215081808807583452231630848 : Rat)/13307469447930800914764404296875,   finite := ((8975365268376919 : Rat)/9007199254740992, (10480825401544793 : Rat)/4503599627370496),   tail := (4553879961075255642778034517536163330078125 : Rat)/37517786505386571720512510865822757827903488,   box := { reLo := (137704486844711898370690697612106186485688730845689 : Rat)/157361002010688919313632506374563856448606911332352,            reHi := (192656285088126790625084285903597490930765234544983 : Rat)/78680501005344459656816253187281928224303455666176,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C240_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C240_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C240_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C240_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := 0 },   conductor := 240,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -4, 0, 1, 0, 0, 0, -6, 0, 1, 0, -2, 0, -4, 0, 4, 0, 8, 0, 1, 0, -1, 0, -6, 0, 0,                    0, 0, 0, 4, 0, -6, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3326867361982700252532958984375,   alphaHi := (5397215081808807583452231630848 : Rat)/13307469447930800914764404296875,   finite := ((8975365268376919 : Rat)/9007199254740992, (10480825401544793 : Rat)/4503599627370496),   tail := (4553879961075255642778034517536163330078125 : Rat)/37517786505386571720512510865822757827903488,   box := { reLo := (137704486844711898370690697612106186485688730845689 : Rat)/157361002010688919313632506374563856448606911332352,            reHi := (192656285088126790625084285903597490930765234544983 : Rat)/78680501005344459656816253187281928224303455666176,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C240_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C240_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C240_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C242_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -52, a6 := 144 },   conductor := 242,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -2, 1, 1, -3, 0, -2, -5, -2, 6, 1, -3, 1, -2, -3, 4, 0, 6, -2, 4, -5, 4, -2, 3,                    6, 2, 1, 0, -3, 6, 1, -7, -2, 10, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/13362802199894618701934814453125,   alphaHi := (1349303770452201895863057907712 : Rat)/3340700549973654651641845703125,   finite := ((10234652523130001 : Rat)/9007199254740992, (6284052347008263 : Rat)/2251799813685248),   tail := (93947111661515636112313709044551849365234375 : Rat)/750104221557035745687130630135958435490955264,   box := { reLo := (795216265789525209185685587787586668693663409090367 : Rat)/786541284223390314069628687625442752453363906904064,            reHi := (573373898224901021725608556764971034555113751972521 : Rat)/196635321055847578517407171906360688113340976726016,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C242_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C242_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C242_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 3, a6 := 1 },   conductor := 242,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -2, 1, 1, -3, 0, -2, -5, -2, 6, 1, -3, 1, -2, -3, 4, 0, 6, -2, 4, -5, 4, -2, 3,                    6, 2, 1, 0, -3, 6, 1, -7, -2, 10, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/13362802199894618701934814453125,   alphaHi := (1349303770452201895863057907712 : Rat)/3340700549973654651641845703125,   finite := ((10234652523130001 : Rat)/9007199254740992, (6284052347008263 : Rat)/2251799813685248),   tail := (93947111661515636112313709044551849365234375 : Rat)/750104221557035745687130630135958435490955264,   box := { reLo := (795216265789525209185685587787586668693663409090367 : Rat)/786541284223390314069628687625442752453363906904064,            reHi := (573373898224901021725608556764971034555113751972521 : Rat)/196635321055847578517407171906360688113340976726016,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C242_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C242_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C242_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C243_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -1 },   conductor := 243,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, -4, 0, 0, 0, 0, 0, -7, 0, 0, 4, 0, 0, -1, 0, 0, 0, 0, 0, -5, 0, 0, 8, 0, 0, 11, 0,                    0, 0, 0, 0, -10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13390382832333691120147705078125,   alphaHi := (1349303770452201895863057907712 : Rat)/3347595708083422756195068359375,   finite := ((4669768684871059 : Rat)/4503599627370496, (21755363415107791 : Rat)/9007199254740992),   tail := (190804968263208101020007731683254241943359375 : Rat)/1499954215558505600889116002203225919814893568,   box := { reLo := (715387291343046855742815195721974972306264660685261 : Rat)/786407995766737784478952850563124911047910918979584,            reHi := (3998944004233864222734979586714321819058869386383889 : Rat)/1572815991533475568957905701126249822095821837959168,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C243_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C243_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C243_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 20 },   conductor := 243,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, -4, 0, 0, 0, 0, 0, -7, 0, 0, 4, 0, 0, -1, 0, 0, 0, 0, 0, -5, 0, 0, 8, 0, 0, 11, 0,                    0, 0, 0, 0, -10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13390382832333691120147705078125,   alphaHi := (1349303770452201895863057907712 : Rat)/3347595708083422756195068359375,   finite := ((4669768684871059 : Rat)/4503599627370496, (21755363415107791 : Rat)/9007199254740992),   tail := (190804968263208101020007731683254241943359375 : Rat)/1499954215558505600889116002203225919814893568,   box := { reLo := (715387291343046855742815195721974972306264660685261 : Rat)/786407995766737784478952850563124911047910918979584,            reHi := (3998944004233864222734979586714321819058869386383889 : Rat)/1572815991533475568957905701126249822095821837959168,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C243_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C243_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C243_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C244_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 6 },   conductor := 244,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -3, 0, -3, 0, -3, 0, -1, 0, 1, 0, 0, 0, -2, 0, 2, 0, 0, 0, 3, 0, 4, 0, 0, 0, -8, 0, 0, 0,                    0, 0, 9, 0, -2, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1677238346580683994293212890625,   alphaHi := (5397215081808807583452231630848 : Rat)/13417906772645471858978271484375,   finite := ((9587837099234589 : Rat)/9007199254740992, (22275529303420281 : Rat)/9007199254740992),   tail := (24217911671036451457004652958202362060546875 : Rat)/187462272171041361531774576351243910120472576,   box := { reLo := (1470765258999149807494942105345580616784235910713811 : Rat)/1572547516032174933676336465376655474387877214814208,            reHi := (4092191246325637033033802305353952843369880941403319 : Rat)/1572547516032174933676336465376655474387877214814208,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 61] }
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C244_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C244_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C245_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -7, a6 := 12 },   conductor := 245,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -2, -3, 2, 1, 6, 0, 0, 6, -2, 1, -6, -3, 0, -3, -4, 3, -12, -6, 2, 0, -2, -4, 0, 1, 6, -9, 0, -1,                    6, -6, 8, -3, -6, 0, 12, 0, 12, 9, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6722687184496122455596923828125,   alphaHi := (5397215081808807583452231630848 : Rat)/13445374368992244815826416015625,   finite := ((977074509954165 : Rat)/2251799813685248, (156356589350071 : Rat)/140737488355328),   tail := (19670926637549323196656775585155487060546875 : Rat)/149944033013786715968680896761416108090589184,   box := { reLo := (23797970181341992250500586888147049658144813788535 : Rat)/78613857180732209741787770001249328478598822100992,            reHi := (6103230268699291093882367899595860339306650260909 : Rat)/4913366073795763108861735625078083029912426381312,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C245_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C245_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C245_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -6435, a6 := 210006 },   conductor := 245,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 1, 0, 0, 0, -2, 0, -3, 2, -5, 0, -1, 4, -3, 0, -2, -2, 0, 0, -6, 0, 1, 0, 5, 0, 3, 0,                    4, 0, 3, 0, 0, 4, 2, 0, 5, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6722687184496122455596923828125,   alphaHi := (5397215081808807583452231630848 : Rat)/13445374368992244815826416015625,   finite := ((8844704864958409 : Rat)/9007199254740992, (2608436322629487 : Rat)/1125899906842624),   tail := (19670926637549323196656775585155487060546875 : Rat)/149944033013786715968680896761416108090589184,   box := { reLo := (267529572015331281574290701997375901406825510573011 : Rat)/314455428722928838967151080004997313914395288403968,            reHi := (96221211492885157966071755641567602964710545623573 : Rat)/39306928590366104870893885000624664239299411050496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C245_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C245_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C245_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -65, a6 := -204 },   conductor := 245,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 1, 0, 0, 0, -2, 0, -3, 2, -5, 0, -1, 4, -3, 0, -2, -2, 0, 0, -6, 0, 1, 0, 5, 0, 3, 0,                    4, 0, 3, 0, 0, 4, 2, 0, 5, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6722687184496122455596923828125,   alphaHi := (5397215081808807583452231630848 : Rat)/13445374368992244815826416015625,   finite := ((8844704864958409 : Rat)/9007199254740992, (2608436322629487 : Rat)/1125899906842624),   tail := (19670926637549323196656775585155487060546875 : Rat)/149944033013786715968680896761416108090589184,   box := { reLo := (267529572015331281574290701997375901406825510573011 : Rat)/314455428722928838967151080004997313914395288403968,            reHi := (96221211492885157966071755641567602964710545623573 : Rat)/39306928590366104870893885000624664239299411050496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 7, 7, 7, 7, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C245_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C245_c2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C245_c2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C245_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 425, a6 := 433 },   conductor := 245,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 1, 0, 0, 0, -2, 0, -3, 2, -5, 0, -1, 4, -3, 0, -2, -2, 0, 0, -6, 0, 1, 0, 5, 0, 3, 0,                    4, 0, 3, 0, 0, 4, 2, 0, 5, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6722687184496122455596923828125,   alphaHi := (5397215081808807583452231630848 : Rat)/13445374368992244815826416015625,   finite := ((8844704864958409 : Rat)/9007199254740992, (2608436322629487 : Rat)/1125899906842624),   tail := (19670926637549323196656775585155487060546875 : Rat)/149944033013786715968680896761416108090589184,   box := { reLo := (267529572015331281574290701997375901406825510573011 : Rat)/314455428722928838967151080004997313914395288403968,            reHi := (96221211492885157966071755641567602964710545623573 : Rat)/39306928590366104870893885000624664239299411050496,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C245_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C245_c3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C245_c3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C246_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -66, a6 := 180 },   conductor := 246,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 2, -1, 1, 2, -4, -1, -4, -2, 2, 1, -2, -1, -8, -2, -2, 4, 4, 1, -1, 4, -1, 2,                    -8, -2, 4, -1, 4, 2, -4, 1, 2, 8, 4, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/6736392982993606281280517578125,   alphaHi := (5397215081808807583452231630848 : Rat)/13472785965987212467193603515625,   finite := ((6883918537363427 : Rat)/9007199254740992, (8779982738786363 : Rat)/4503599627370496),   tail := (99851477059987749862766325610256195068359375 : Rat)/749590337757328742314873028960036175151628288,   box := { reLo := (992030061724753767485195201480124746099471073719581 : Rat)/1572004876008457486603120602429597784791587567435776,            reHi := (1637051185022606644089576463052888407701752574190789 : Rat)/786002438004228743301560301214798892395793783717888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C246_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C246_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C246_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -26, a6 := 444 },   conductor := 246,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 2, -1, 1, 2, -4, -1, -4, -2, 2, 1, -2, -1, -8, -2, -2, 4, 4, 1, -1, 4, -1, 2,                    -8, -2, 4, -1, 4, 2, -4, 1, 2, 8, 4, 2],   alphaLo := (2698607540904403791717525880832 : Rat)/6736392982993606281280517578125,   alphaHi := (5397215081808807583452231630848 : Rat)/13472785965987212467193603515625,   finite := ((6883918537363427 : Rat)/9007199254740992, (8779982738786363 : Rat)/4503599627370496),   tail := (99851477059987749862766325610256195068359375 : Rat)/749590337757328742314873028960036175151628288,   box := { reLo := (992030061724753767485195201480124746099471073719581 : Rat)/1572004876008457486603120602429597784791587567435776,            reHi := (1637051185022606644089576463052888407701752574190789 : Rat)/786002438004228743301560301214798892395793783717888,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 41, 41] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C246_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C246_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C246_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C248_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 1 },   conductor := 248,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 1, 0, -3, 0, 1, 0, -2, 0, -2, 0, -2, 0, -6, 0, 1, 0, 6, 0, -6, 0, -4, 0, 4, 0, 4, 0, -1,                    0, 4, 0, -3, 0, -2, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13527442522930886745452880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/6763721261465443325042724609375,   finite := ((4398506113934277 : Rat)/4503599627370496, (20612216245835799 : Rat)/9007199254740992),   tail := (51443434171831677963464548013210296630859375 : Rat)/374663987735260069319535708447430338299297792,   box := { reLo := (164876832831373741110571092960039002480015535360977 : Rat)/196431832801744031223400737510486357206262240772096,            reHi := (952977733297761496756347207239880745939827227228699 : Rat)/392863665603488062446801475020972714412524481544192,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C248_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C248_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C248_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -1 },   conductor := 248,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -3, 0, -3, 0, -3, 0, 2, 0, -4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 4, 0, 0, 0, -6, 0, 1, 0,                    0, 0, 9, 0, -10, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13527442522930886745452880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/6763721261465443325042724609375,   finite := ((9755809435745667 : Rat)/9007199254740992, (22570858692673433 : Rat)/9007199254740992),   tail := (51443434171831677963464548013210296630859375 : Rat)/374663987735260069319535708447430338299297792,   box := { reLo := (371573167486105750716399477045354647640651242241367 : Rat)/392863665603488062446801475020972714412524481544192,            reHi := (1038407113675485224751036670002464933243357159787733 : Rat)/392863665603488062446801475020972714412524481544192,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C248_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C248_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C249_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -55, a6 := 134 },   conductor := 249,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, -1, 1, 1, 0, 3, 1, -1, -3, 1, -6, 0, -1, -1, -4, -1, -7, -1, 0, 3, 5, -3, -4, 6, -1, 0, 8,                    1, -10, -5, 3, 4, 0, -1, 7, 7, 6, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/13554688154810022640228271484375,   alphaHi := (2698607540904403791726115815424 : Rat)/6777344077405011272430419921875,   finite := ((6286816369650985 : Rat)/9007199254740992, (17473010586701441 : Rat)/9007199254740992),   tail := (208850960724199692667027340962314605712890625 : Rat)/1498390884544026923077017116501303007805177856,   box := { reLo := (877648839179921882288270200096393710090700495824355 : Rat)/1571176720151637574892406299952470302712322175533056,            reHi := (3266912187268220665057375872677962573188601968181163 : Rat)/1571176720151637574892406299952470302712322175533056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 83] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C249_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C249_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C249_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := 1 },   conductor := 249,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -1, -1, -4, -3, 1, -1, -3, 1, 2, -4, 1, -1, 4, 1, -1, 1, 4, -3, -3, 3, -4, 2, -1, 4, 4,                    1, -6, 5, 3, 4, 4, -1, -9, -1, -2, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/13554688154810022640228271484375,   alphaHi := (2698607540904403791726115815424 : Rat)/6777344077405011272430419921875,   finite := ((675538673891723 : Rat)/562949953421312, (13391799107773093 : Rat)/4503599627370496),   tail := (208850960724199692667027340962314605712890625 : Rat)/1498390884544026923077017116501303007805177856,   box := { reLo := (104150775878763908231144658341678204679478648281689 : Rat)/98198545009477348430775393747029393919520135970816,            reHi := (2445505328898494037108584653623319442729877388124599 : Rat)/785588360075818787446203149976235151356161087766528,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 83] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C249_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C249_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C252_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 2270 },   conductor := 252,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, -1, 0, 0, 0, -2, 0, -6, 0, 0, 0, 4, 0, -4, 0, 0, 0, -2, 0, 11, 0, 0, 0, 2, 0, 0,                    0, 0, 0, 4, 0, 2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6818049212622923755645751953125,   alphaHi := (5397215081808807583452231630848 : Rat)/13636098425245847415924072265625,   finite := ((2464942070154621 : Rat)/2251799813685248, (2841594291315133 : Rat)/1125899906842624),   tail := (36375120115145538030838916054248809814453125 : Rat)/249597481879720492992624045972089509462933504,   box := { reLo := (124176462411860818031731239498731104412371840249929 : Rat)/130860964579754897830116875814614864737302480945152,            reHi := (174671766344708792045221968271344417143190466907017 : Rat)/65430482289877448915058437907307432368651240472576,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C252_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C252_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C252_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 65 },   conductor := 252,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, -1, 0, 0, 0, -2, 0, -6, 0, 0, 0, 4, 0, -4, 0, 0, 0, -2, 0, 11, 0, 0, 0, 2, 0, 0,                    0, 0, 0, 4, 0, 2, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/6818049212622923755645751953125,   alphaHi := (5397215081808807583452231630848 : Rat)/13636098425245847415924072265625,   finite := ((2464942070154621 : Rat)/2251799813685248, (2841594291315133 : Rat)/1125899906842624),   tail := (36375120115145538030838916054248809814453125 : Rat)/249597481879720492992624045972089509462933504,   box := { reLo := (124176462411860818031731239498731104412371840249929 : Rat)/130860964579754897830116875814614864737302480945152,            reHi := (174671766344708792045221968271344417143190466907017 : Rat)/65430482289877448915058437907307432368651240472576,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C252_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C252_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C252_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C254_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := -3 },   conductor := 254,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, -3, -1, -3, 1, 1, 0, -2, 3, 0, 1, -1, 3, -7, -1, 0, -1, 9, 0, -4, 2, 0, -3, -6,                    0, -10, -1, 0, 1, 3, -3, 4, 7, 0, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/3422525746697249507904052734375,   alphaHi := (5397215081808807583452231630848 : Rat)/13690102986788997936248779296875,   finite := ((8099930668500749 : Rat)/9007199254740992, (19319187078627695 : Rat)/9007199254740992),   tail := (8023496925117204877326167375850677490234375 : Rat)/53465663820609145697928476960562045136142336,   box := { reLo := (168010096330181983627976607309458261124307301882393 : Rat)/224251247625436222237404202629593228162702344454144,            reHi := (514640657770306233398183363188278500306780338912115 : Rat)/224251247625436222237404202629593228162702344454144,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 127] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C254_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C254_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C254_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -24432, a6 := -1471934 },   conductor := 254,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -1, 1, 1, -3, -3, -2, -4, -1, 6, 1, 3, 1, -7, -3, 2, -3, 3, -2, 4, -4, 4, -1, 6,                    6, -4, 1, 6, 3, 3, 1, 2, -7, 8, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/3422525746697249507904052734375,   alphaHi := (5397215081808807583452231630848 : Rat)/13690102986788997936248779296875,   finite := ((10762069978013527 : Rat)/9007199254740992, (26147823030021401 : Rat)/9007199254740992),   tail := (8023496925117204877326167375850677490234375 : Rat)/53465663820609145697928476960562045136142336,   box := { reLo := (234289085461762438507402052368728594459688234974139 : Rat)/224251247625436222237404202629593228162702344454144,            reHi := (684652454819641148600493731753989609056969660775157 : Rat)/224251247625436222237404202629593228162702344454144,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 127] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C254_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C254_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C254_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -302, a6 := -2036 },   conductor := 254,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -1, 1, 1, -3, -3, -2, -4, -1, 6, 1, 3, 1, -7, -3, 2, -3, 3, -2, 4, -4, 4, -1, 6,                    6, -4, 1, 6, 3, 3, 1, 2, -7, 8, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/3422525746697249507904052734375,   alphaHi := (5397215081808807583452231630848 : Rat)/13690102986788997936248779296875,   finite := ((10762069978013527 : Rat)/9007199254740992, (26147823030021401 : Rat)/9007199254740992),   tail := (8023496925117204877326167375850677490234375 : Rat)/53465663820609145697928476960562045136142336,   box := { reLo := (234289085461762438507402052368728594459688234974139 : Rat)/224251247625436222237404202629593228162702344454144,            reHi := (684652454819641148600493731753989609056969660775157 : Rat)/224251247625436222237404202629593228162702344454144,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 127, 127, 127] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C254_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C254_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C254_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C254_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -22, a6 := 36 },   conductor := 254,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, -1, 1, 1, -3, -3, -2, -4, -1, 6, 1, 3, 1, -7, -3, 2, -3, 3, -2, 4, -4, 4, -1, 6,                    6, -4, 1, 6, 3, 3, 1, 2, -7, 8, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/3422525746697249507904052734375,   alphaHi := (5397215081808807583452231630848 : Rat)/13690102986788997936248779296875,   finite := ((10762069978013527 : Rat)/9007199254740992, (26147823030021401 : Rat)/9007199254740992),   tail := (8023496925117204877326167375850677490234375 : Rat)/53465663820609145697928476960562045136142336,   box := { reLo := (234289085461762438507402052368728594459688234974139 : Rat)/224251247625436222237404202629593228162702344454144,            reHi := (684652454819641148600493731753989609056969660775157 : Rat)/224251247625436222237404202629593228162702344454144,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 127] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C254_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C254_b3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C254_b3
