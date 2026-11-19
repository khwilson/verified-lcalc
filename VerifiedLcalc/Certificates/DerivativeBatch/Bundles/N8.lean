module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C256_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := 1 },   conductor := 256,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, 0, 0, 1, 0, -6, 0, 0, 0, 0, 0, -6, 0, -2, 0, 0, 0, 0, 0, -5, 0, 4, 0, 0, 0, 0, 0,                    12, 0, 0, 0, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13743895347200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/800000000000000000000,   finite := ((2262837692442705 : Rat)/2251799813685248, (5218019031009139 : Rat)/2251799813685248),   tail := (903039894005402205920498015499114990234375 : Rat)/5845645005778470372592236587192245532229632,   box := { reLo := (1303185800863810121538254391333101792025933408555 : Rat)/1532400764394791337352819267912924012800804651008,            reHi := (3787706600705545571811117642853541317601838797569 : Rat)/1532400764394791337352819267912924012800804651008,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C256_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C256_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C256_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 0 },   conductor := 256,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -4, 0, 0, 0, -3, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, -4, 0, 0, 0,                    0, 0, 0, 0, 12, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13743895347200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/800000000000000000000,   finite := ((10038181635344351 : Rat)/9007199254740992, (23042166514062867 : Rat)/9007199254740992),   tail := (903039894005402205920498015499114990234375 : Rat)/5845645005778470372592236587192245532229632,   box := { reLo := (5884303953901517754147749348138369844978969717221 : Rat)/6129603057579165349411277071651696051203218604032,            reHi := (16627622054137097187845516887326038915656361394657 : Rat)/6129603057579165349411277071651696051203218604032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C256_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C256_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C258_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 3, a6 := -3 },   conductor := 258,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 1, 1, -5, -1, 1, -1, 1, -1, -3, 5, -1, 1, 0, -1, -7, 1, 5, -1, -4, 1, -4, 3, -1, -5,                    -3, 1, -2, -1, -1, 0, -5, 1, 2, 7, 3, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/13797477988410873889923095703125,   alphaHi := (1349303770452201895863057907712 : Rat)/3449369497102718448638916015625,   finite := ((7544491659231379 : Rat)/9007199254740992, (2334151409667523 : Rat)/1125899906842624),   tail := (118906039694366185355302966114521026611328125 : Rat)/747962256014083422395124990120846104224333824,   box := { reLo := (532249059737524926746748214199911422969808621652063 : Rat)/784295270562223538721390581640956324583135063834624,            reHi := (218829774911083024095389055729358485998100042506831 : Rat)/98036908820277942340173822705119540572891882979328,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 43] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C258_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C258_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C258_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -15, a6 := 22 },   conductor := 258,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -3, -1, -3, -1, 1, 3, -5, 1, -3, 3, -3, 1, 0, -1, 7, -3, -3, 5, -4, -1, 4, 3, 1, -3, 1,                    3, -6, -1, -5, 0, 9, 1, -6, -7, -3, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/13797477988410873889923095703125,   alphaHi := (1349303770452201895863057907712 : Rat)/3449369497102718448638916015625,   finite := ((4296349350578581 : Rat)/4503599627370496, (20978678839433439 : Rat)/9007199254740992),   tail := (118906039694366185355302966114521026611328125 : Rat)/747962256014083422395124990120846104224333824,   box := { reLo := (311760459656797895935573137855680954034831158206057 : Rat)/392147635281111769360695290820478162291567531917312,            reHi := (1951385096769878443862091985214186893425370789713883 : Rat)/784295270562223538721390581640956324583135063834624,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 43] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C258_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C258_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C262_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 2 },   conductor := 262,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -5, -1, -3, 0, 2, 0, -2, 5, 0, 1, -6, 3, 7, 0, 0, -2, -6, 0, -5, 2, 0, -5, -3, 0,                    2, -1, 0, 6, 0, -3, -1, -7, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/13904023802211937427520751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/3476005950552984333038330078125,   finite := ((2079207938181443 : Rat)/2251799813685248, (20122861146319765 : Rat)/9007199254740992),   tail := (12571114805654842674206069801235198974609375 : Rat)/74739096684429680290593667598668560584409088,   box := { reLo := (14795280194560429177718523115612395001696715416277 : Rat)/19592405761243134110097386398985371145839335964672,            reHi := (188266276462341674296040324244160589272184407170835 : Rat)/78369623044972536440389545595941484583357343858688,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 131] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C262_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C262_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C262_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 1, a6 := 25 },   conductor := 262,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -2, -2, -3, 1, 1, -2, -6, -2, 4, -3, 4, 1, -4, 1, 3, -2, 6, -6, -4, -2, -1, 4, 4, -3, 3,                    4, -4, 1, 12, -4, 6, 1, -3, 3, -8, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/13904023802211937427520751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/3476005950552984333038330078125,   finite := ((5580005046698449 : Rat)/4503599627370496, (6748089845527961 : Rat)/2251799813685248),   tail := (12571114805654842674206069801235198974609375 : Rat)/74739096684429680290593667598668560584409088,   box := { reLo := (41959489315098856841736543252610213729178285859511 : Rat)/39184811522486268220194772797970742291678671929344,            reHi := (62009060450052127796787183419159113159249406770479 : Rat)/19592405761243134110097386398985371145839335964672,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 131] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C262_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C262_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C265_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -138, a6 := 656 },   conductor := 265,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 2, 3, -3, 1, 0, 0, -6, -2, 0, -1, -6, 3, -2, 1, 0, 0, -8, 0, 1, 6, 0, -2, 2, 0,                    10, -5, 0, 6, -2, 3, 2, 2, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/13983400415539892864227294921875,   alphaHi := (2698607540904403791726115815424 : Rat)/6991700207769946384429931640625,   finite := ((3813138155545323 : Rat)/4503599627370496, (9529001544419019 : Rat)/4503599627370496),   tail := (3492417528425403174981078860363006591796875 : Rat)/19918751803813879633886061446105658822754304,   box := { reLo := (7011054809475445430688404879079130610866413330551 : Rat)/10443162545717971325490855383455843652864208535552,            reHi := (23927337837065618245721983599085036042974415724503 : Rat)/10443162545717971325490855383455843652864208535552,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 53] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C265_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C265_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C265_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -133, a6 := 702 },   conductor := 265,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, -1, 0, 2, 3, -3, 1, 0, 0, -6, -2, 0, -1, -6, 3, -2, 1, 0, 0, -8, 0, 1, 6, 0, -2, 2, 0,                    10, -5, 0, 6, -2, 3, 2, 2, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/13983400415539892864227294921875,   alphaHi := (2698607540904403791726115815424 : Rat)/6991700207769946384429931640625,   finite := ((3813138155545323 : Rat)/4503599627370496, (9529001544419019 : Rat)/4503599627370496),   tail := (3492417528425403174981078860363006591796875 : Rat)/19918751803813879633886061446105658822754304,   box := { reLo := (7011054809475445430688404879079130610866413330551 : Rat)/10443162545717971325490855383455843652864208535552,            reHi := (23927337837065618245721983599085036042974415724503 : Rat)/10443162545717971325490855383455843652864208535552,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 53, 53] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C265_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C265_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C265_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C269_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := -1 },   conductor := 269,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 1, 0, -4, 0, -3, 0, -3, 0, 2, 0, 0, 4, -4, 0, 2, -2, 0, 0, -1, 0, -4, 0, 0, 8, -2, 0,                    -8, 0, 0, 0, -4, 6, 7, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7044270122466819095611572265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14088540244933638095855712890625,   finite := ((1298052367091653 : Rat)/1125899906842624, (11916546366542979 : Rat)/4503599627370496),   tail := (69086939225109161013674339279460906982421875 : Rat)/373178574098356117522901697276234972285370368,   box := { reLo := (94673678516099824269468936393437278112504437931099 : Rat)/97826524128439466071923542530781340574776129748992,            reHi := (1107840727780439231786263917755845811983452588964957 : Rat)/391306096513757864287694170123125362299104518995968,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [269] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C269_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C269_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C272_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -48, a6 := -140 },   conductor := 272,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, 0, 0, 1, 0, -2, 0, -6, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -5, 0, 4, 0, 0, 0, 8,                    0, 4, 0, 0, 0, -4, 0, 12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/14166883055985177516937255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7083441527992588710784912109375,   finite := ((9557556660958461 : Rat)/9007199254740992, (21920485643698159 : Rat)/9007199254740992),   tail := (57493017187796825089959265247631072998046875 : Rat)/298360360717719322487877428969734026827923456,   box := { reLo := (271683674233135866665129683471576084049418422620573 : Rat)/312853513599943256297048562959367826915116665798656,            reHi := (821665751902398788605746341588619497650274248699087 : Rat)/312853513599943256297048562959367826915116665798656,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C272_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C272_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C272_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 4 },   conductor := 272,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, 0, 0, 1, 0, -2, 0, -6, 0, 0, 0, -1, 0, -4, 0, 0, 0, -4, 0, -5, 0, 4, 0, 0, 0, 8,                    0, 4, 0, 0, 0, -4, 0, 12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/14166883055985177516937255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/7083441527992588710784912109375,   finite := ((9557556660958461 : Rat)/9007199254740992, (21920485643698159 : Rat)/9007199254740992),   tail := (57493017187796825089959265247631072998046875 : Rat)/298360360717719322487877428969734026827923456,   box := { reLo := (271683674233135866665129683471576084049418422620573 : Rat)/312853513599943256297048562959367826915116665798656,            reHi := (821665751902398788605746341588619497650274248699087 : Rat)/312853513599943256297048562959367826915116665798656,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C272_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C272_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C272_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C273_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -26, a6 := 68 },   conductor := 273,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, -1, 2, 1, 0, 1, 2, -2, -2, 1, -2, 1, -4, -4, -2, 3, -2, -1, 4, -9, 0, -4, -2, -1, 2,                    -1, -2, -5, 8, 2, 8, -1, 2, -8, -6, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/14192901228603977870941162109375,   alphaHi := (2698607540904403791726115815424 : Rat)/7096450614301988887786865234375,   finite := ((4121832535075327 : Rat)/9007199254740992, (7898731964092379 : Rat)/4503599627370496),   tail := (291229202514443905574252278610706329345703125 : Rat)/1491494144130298754912071739443483675736408064,   box := { reLo := (410309251549616675698039702863202533426319264931809 : Rat)/1563944963675572147230680536258690338768979822116864,            reHi := (1524166692795936575125136077226845271831078826466693 : Rat)/781972481837786073615340268129345169384489911058432,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 7, 7, 7, 13] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C273_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C273_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C274_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2846, a6 := 59156 },   conductor := 274,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 2, -1, -3, 3, -1, 0, -2, -2, 0, 1, -7, 3, -1, -3, 0, 1, 0, 0, 4, 2, 0, 2, 1, 0,                    -11, -1, 0, 7, -6, -3, 4, 1, 0, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/14218871792370050334930419921875,   alphaHi := (2698607540904403791726115815424 : Rat)/7109435896185025119781494140625,   finite := ((8590915752619847 : Rat)/9007199254740992, (20140247278141903 : Rat)/9007199254740992),   tail := (18438910195465510870730040606784820556640625 : Rat)/93199046359295374554128092018874970068221952,   box := { reLo := (73875093055701000327866323101563048528698281808857 : Rat)/97726283235244506668469418216783840614255901540352,            reHi := (237852192708995743919911183475258354619866360205393 : Rat)/97726283235244506668469418216783840614255901540352,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 137] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C274_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C274_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C274_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 0 },   conductor := 274,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, -3, 0, -4, 0, 4, 4, 0, 1, 2, 3, -4, 0, 0, 4, -6, 0, -5, -4, 0, -4, -8, 0,                    10, -1, 0, -2, 0, -3, -2, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/14218871792370050334930419921875,   alphaHi := (2698607540904403791726115815424 : Rat)/7109435896185025119781494140625,   finite := ((8603016132901339 : Rat)/9007199254740992, (5233791300134275 : Rat)/2251799813685248),   tail := (18438910195465510870730040606784820556640625 : Rat)/93199046359295374554128092018874970068221952,   box := { reLo := (74006379725086139753398057587684497588143141504709 : Rat)/97726283235244506668469418216783840614255901540352,            reHi := (61619222694868147906592709072542992422014346282525 : Rat)/24431570808811126667117354554195960153563975385088,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 137] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C274_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C274_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C274_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 8, a6 := -6 },   conductor := 274,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -4, -1, -3, 0, -4, 0, 4, 4, 0, 1, 2, 3, -4, 0, 0, 4, -6, 0, -5, -4, 0, -4, -8, 0,                    10, -1, 0, -2, 0, -3, -2, 4, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/14218871792370050334930419921875,   alphaHi := (2698607540904403791726115815424 : Rat)/7109435896185025119781494140625,   finite := ((8603016132901339 : Rat)/9007199254740992, (5233791300134275 : Rat)/2251799813685248),   tail := (18438910195465510870730040606784820556640625 : Rat)/93199046359295374554128092018874970068221952,   box := { reLo := (74006379725086139753398057587684497588143141504709 : Rat)/97726283235244506668469418216783840614255901540352,            reHi := (61619222694868147906592709072542992422014346282525 : Rat)/24431570808811126667117354554195960153563975385088,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 137, 137] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C274_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C274_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C274_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C274_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -7, a6 := 9 },   conductor := 274,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -3, -2, 0, 1, 1, -3, -3, -2, -6, 0, 6, 1, 1, 1, -3, -3, 0, -3, 0, -2, 4, -6, 4, 0, -3,                    6, 7, 1, 6, 1, 0, 1, 10, -3, 12, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/14218871792370050334930419921875,   alphaHi := (2698607540904403791726115815424 : Rat)/7109435896185025119781494140625,   finite := ((11604985216199349 : Rat)/9007199254740992, (27844383803611625 : Rat)/9007199254740992),   tail := (18438910195465510870730040606784820556640625 : Rat)/93199046359295374554128092018874970068221952,   box := { reLo := (106577134806740511433383377880251100787942876431019 : Rat)/97726283235244506668469418216783840614255901540352,            reHi := (321440509884809858759214812619526674788952051760375 : Rat)/97726283235244506668469418216783840614255901540352,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 137] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C274_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C274_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C275_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1480, a6 := 22272 },   conductor := 275,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, -3, 0, -1, 0, -2, 0, 0, -1, -6, 3, -4, 0, 0, 1, -4, 0, 0, 2, 0, 0, 6, 0,                    -8, -5, 0, 6, 0, 3, 2, 4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7122397503839649295806884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/14244795007679298496246337890625,   finite := ((2107936939048723 : Rat)/2251799813685248, (19667514952804295 : Rat)/9007199254740992),   tail := (149422605515333690437175418749141693115234375 : Rat)/745436799647490065715460318403006681137020928,   box := { reLo := (287514173063313050894806638855963504200724565673689 : Rat)/390823568813583271573827259414875566839966428299264,            reHi := (3726866232342263950238835047866977047888981579053685 : Rat)/1563294275254333086295309037659502267359865713197056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C275_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C275_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C275_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -730, a6 := -7228 },   conductor := 275,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, -3, 0, -1, 0, -2, 0, 0, -1, -6, 3, -4, 0, 0, 1, -4, 0, 0, 2, 0, 0, 6, 0,                    -8, -5, 0, 6, 0, 3, 2, 4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7122397503839649295806884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/14244795007679298496246337890625,   finite := ((2107936939048723 : Rat)/2251799813685248, (19667514952804295 : Rat)/9007199254740992),   tail := (149422605515333690437175418749141693115234375 : Rat)/745436799647490065715460318403006681137020928,   box := { reLo := (287514173063313050894806638855963504200724565673689 : Rat)/390823568813583271573827259414875566839966428299264,            reHi := (3726866232342263950238835047866977047888981579053685 : Rat)/1563294275254333086295309037659502267359865713197056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11, 11, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C275_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C275_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C275_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C275_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -105, a6 := 272 },   conductor := 275,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, -3, 0, -1, 0, -2, 0, 0, -1, -6, 3, -4, 0, 0, 1, -4, 0, 0, 2, 0, 0, 6, 0,                    -8, -5, 0, 6, 0, 3, 2, 4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7122397503839649295806884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/14244795007679298496246337890625,   finite := ((2107936939048723 : Rat)/2251799813685248, (19667514952804295 : Rat)/9007199254740992),   tail := (149422605515333690437175418749141693115234375 : Rat)/745436799647490065715460318403006681137020928,   box := { reLo := (287514173063313050894806638855963504200724565673689 : Rat)/390823568813583271573827259414875566839966428299264,            reHi := (3726866232342263950238835047866977047888981579053685 : Rat)/1563294275254333086295309037659502267359865713197056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 11, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C275_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C275_a3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C275_a3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C275_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 20, a6 := 22 },   conductor := 275,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, -3, 0, -1, 0, -2, 0, 0, -1, -6, 3, -4, 0, 0, 1, -4, 0, 0, 2, 0, 0, 6, 0,                    -8, -5, 0, 6, 0, 3, 2, 4, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7122397503839649295806884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/14244795007679298496246337890625,   finite := ((2107936939048723 : Rat)/2251799813685248, (19667514952804295 : Rat)/9007199254740992),   tail := (149422605515333690437175418749141693115234375 : Rat)/745436799647490065715460318403006681137020928,   box := { reLo := (287514173063313050894806638855963504200724565673689 : Rat)/390823568813583271573827259414875566839966428299264,            reHi := (3726866232342263950238835047866977047888981579053685 : Rat)/1563294275254333086295309037659502267359865713197056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C275_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C275_a4.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C275_a4

namespace VerifiedLcalc.Certificates.DerivativeBatch.C277_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 0, a6 := -1 },   conductor := 277,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, -1, 2, -2, -4, -3, 1, 2, 1, 2, -5, -4, -4, -1, 2, 1, -6, -2, 8, 1, 0, 6, -1, -5, 4, 4, 5,                    -4, -3, 5, -2, 2, -8, -1, -4, -6, 10, -6],   alphaLo := (2698607540904403791717525880832 : Rat)/7148250211357703876495361328125,   alphaHi := (5397215081808807583452231630848 : Rat)/14296500422715407657623291015625,   finite := ((11589530773579665 : Rat)/9007199254740992, (27836109509780303 : Rat)/9007199254740992),   tail := (21898467006673488190724948633480072021484375 : Rat)/106446150409334949336672541835888326244040704,   box := { reLo := (241309655875805161162629941484496993125992234215335 : Rat)/223233757223237607671301494456216875159342450475008,            reHi := (735812484144995156865735454857702514927276611288697 : Rat)/223233757223237607671301494456216875159342450475008,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [277] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C277_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C277_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C278_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 9 },   conductor := 278,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -1, -2, -5, 1, 1, -1, -3, -2, 1, -5, 2, 1, 2, 1, -2, -1, 10, -3, -6, -2, -4, 1, 4, -5,                    1, 2, 9, 1, 6, 2, 5, 1, -6, -2, -2, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/14322283131527955341339111328125,   alphaHi := (1349303770452201895863057907712 : Rat)/3580570782881988811492919921875,   finite := ((11909084902911307 : Rat)/9007199254740992, (28562474740609001 : Rat)/9007199254740992),   tail := (38811162518764400219747654136180877685546875 : Rat)/186241220059483625760593823020681955668656128,   box := { reLo := (217508364933954166410523610187203543894101704886313 : Rat)/195288073565093102365540428567734602347216768073728,            reHi := (659968938879185551205439577094672239013622607736659 : Rat)/195288073565093102365540428567734602347216768073728,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 139] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C278_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C278_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C280_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := 3316 },   conductor := 280,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -3, 0, 1, 0, 1, 0, 6, 0, -5, 0, -5, 0, -3, 0, -7, 0, -2, 0, -3, 0, -2, 0, 1, 0, -9, 0, 7, 0, 4,                    0, 15, 0, 1, 0, -6, 0, 15, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7186854903668693447113037109375,   alphaHi := (5397215081808807583452231630848 : Rat)/14373709807337386798858642578125,   finite := ((1958427448643997 : Rat)/2251799813685248, (21961465192002451 : Rat)/9007199254740992),   tail := (1768884573492051471022813351383209228515625 : Rat)/8273843821564461654613651567759338237853696,   box := { reLo := (2845318264543375868732829663949155480715199700047 : Rat)/4337877029520388471974082153157407926047838568448,            reHi := (46016282612325834647247194975627263250213847409601 : Rat)/17351508118081553887896328612629631704191354273792,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 7, 7, 7] }
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C280_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C280_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C280_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 5 },   conductor := 280,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, -1, 0, -2, 0, -5, 0, 1, 0, 1, 0, 3, 0, -6, 0, 1, 0, -6, 0, 1, 0, 5, 0, -9, 0, 0,                    0, 5, 0, 1, 0, 6, 0, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7186854903668693447113037109375,   alphaHi := (5397215081808807583452231630848 : Rat)/14373709807337386798858642578125,   finite := ((10408244733776235 : Rat)/9007199254740992, (11906509850170175 : Rat)/4503599627370496),   tail := (1768884573492051471022813351383209228515625 : Rat)/8273843821564461654613651567759338237853696,   box := { reLo := (16340868447861844555669879711540679938235763118985 : Rat)/17351508118081553887896328612629631704191354273792,            reHi := (24791562665781734563466889601586500784631380733925 : Rat)/8675754059040776943948164306314815852095677136896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C280_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C280_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C282_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -255, a6 := 1461 },   conductor := 282,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, -4, 1, 1, -4, 0, -1, -2, -4, 4, 1, -6, 1, 6, -4, 4, 0, -4, -1, 11, -2, -1, -4,                    4, 4, 2, 1, 0, -6, 16, 1, -6, 6, 2, -4],   alphaLo := (674651885226100947929381470208 : Rat)/1803119142761040210723876953125,   alphaHi := (5397215081808807583452231630848 : Rat)/14424953142088321590423583984375,   finite := ((12450320943233223 : Rat)/9007199254740992, (475375619324783 : Rat)/140737488355328),   tail := (1275106533703724842020443917751312255859375 : Rat)/5815027835894984757693929385146748353118208,   box := { reLo := (56730419612150577939733345667964271785850137945441 : Rat)/48779989024411356298269357591677094408954224574464,            reHi := (2741606673056596525690358868668946403727787619961 : Rat)/762187328506427442160458712369954600139909758976,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 47, 47] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C282_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C282_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C282_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -15, a6 := 21 },   conductor := 282,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, -4, 1, 1, -4, 0, -1, -2, -4, 4, 1, -6, 1, 6, -4, 4, 0, -4, -1, 11, -2, -1, -4,                    4, 4, 2, 1, 0, -6, 16, 1, -6, 6, 2, -4],   alphaLo := (674651885226100947929381470208 : Rat)/1803119142761040210723876953125,   alphaHi := (5397215081808807583452231630848 : Rat)/14424953142088321590423583984375,   finite := ((12450320943233223 : Rat)/9007199254740992, (475375619324783 : Rat)/140737488355328),   tail := (1275106533703724842020443917751312255859375 : Rat)/5815027835894984757693929385146748353118208,   box := { reLo := (56730419612150577939733345667964271785850137945441 : Rat)/48779989024411356298269357591677094408954224574464,            reHi := (2741606673056596525690358868668946403727787619961 : Rat)/762187328506427442160458712369954600139909758976,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 47] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C282_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C282_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C282_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C285_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -76, a6 := -19 },   conductor := 285,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, -1, -1, -2, 3, 1, 1, -6, -1, 0, 2, -1, -1, -6, -1, 1, 1, -2, 6, -8, 3, 1, 0, 1, 2, 4,                    1, 0, -5, -6, 6, 2, -1, 4, -1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/14501478629446339702606201171875,   alphaHi := (2698607540904403791726115815424 : Rat)/7250739314723169803619384765625,   finite := ((9023795649081479 : Rat)/9007199254740992, (10904889938592435 : Rat)/4503599627370496),   tail := (338691494625152514747303983320713043212890625 : Rat)/1487667119566133718375821807040049631947915264,   box := { reLo := (1207662548735699082772904044147775483288274304692793 : Rat)/1559932037566178229879645727138827082869417195864064,            reHi := (2066159748136870772029028516281464766489248292773645 : Rat)/779966018783089114939822863569413541434708597932032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C285_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C285_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C285_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 19, a6 := 0 },   conductor := 285,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, -1, -1, -2, 3, 1, 1, -6, -1, 0, 2, -1, -1, -6, -1, 1, 1, -2, 6, -8, 3, 1, 0, 1, 2, 4,                    1, 0, -5, -6, 6, 2, -1, 4, -1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/14501478629446339702606201171875,   alphaHi := (2698607540904403791726115815424 : Rat)/7250739314723169803619384765625,   finite := ((9023795649081479 : Rat)/9007199254740992, (10904889938592435 : Rat)/4503599627370496),   tail := (338691494625152514747303983320713043212890625 : Rat)/1487667119566133718375821807040049631947915264,   box := { reLo := (1207662548735699082772904044147775483288274304692793 : Rat)/1559932037566178229879645727138827082869417195864064,            reHi := (2066159748136870772029028516281464766489248292773645 : Rat)/779966018783089114939822863569413541434708597932032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 19, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C285_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C285_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C285_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C285_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -93, a6 := -378 },   conductor := 285,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -1, -1, -2, -3, 1, -1, -2, 1, -4, -2, 1, -1, 2, 1, -1, 1, 2, -2, -4, 3, 1, -4, -1, 2,                    4, 1, 0, 5, 2, 2, 2, -1, 0, -1, 4, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/14501478629446339702606201171875,   alphaHi := (2698607540904403791726115815424 : Rat)/7250739314723169803619384765625,   finite := ((12429438165713999 : Rat)/9007199254740992, (14976861979279519 : Rat)/4503599627370496),   tail := (338691494625152514747303983320713043212890625 : Rat)/1487667119566133718375821807040049631947915264,   box := { reLo := (1797476398739769017314943466471075980743440994027633 : Rat)/1559932037566178229879645727138827082869417195864064,            reHi := (2771373373670701345265081165149630957523791987773473 : Rat)/779966018783089114939822863569413541434708597932032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C285_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C285_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C285_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := -17 },   conductor := 285,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, -1, -1, -2, -3, 1, -1, -2, 1, -4, -2, 1, -1, 2, 1, -1, 1, 2, -2, -4, 3, 1, -4, -1, 2,                    4, 1, 0, 5, 2, 2, 2, -1, 0, -1, 4, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/14501478629446339702606201171875,   alphaHi := (2698607540904403791726115815424 : Rat)/7250739314723169803619384765625,   finite := ((12429438165713999 : Rat)/9007199254740992, (14976861979279519 : Rat)/4503599627370496),   tail := (338691494625152514747303983320713043212890625 : Rat)/1487667119566133718375821807040049631947915264,   box := { reLo := (1797476398739769017314943466471075980743440994027633 : Rat)/1559932037566178229879645727138827082869417195864064,            reHi := (2771373373670701345265081165149630957523791987773473 : Rat)/779966018783089114939822863569413541434708597932032,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 5, 5, 5, 19, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C285_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C285_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C285_b2
