module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.DerivativeBatch.C160_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6, a6 := 4 },   conductor := 160,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, -1, 0, -2, 0, 1, 0, -4, 0, -6, 0, 2, 0, 2, 0, 8, 0, 4, 0, -6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5432751652517836475372314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/10865503305035672855377197265625,   finite := ((1016554854156945 : Rat)/2251799813685248, (15816454661043071 : Rat)/9007199254740992),   tail := (43243430616500991753946802639007568359375 : Rat)/1893606165838476057726909987938412871548928,   box := { reLo := (425516392742115062161732035630371248846439520135 : Rat)/992794989475122935353526183756254607598644363264,            reHi := (7063997505204112887544630011847665191965860299753 : Rat)/3971179957900491741414104735025018430394577453056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C160_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C160_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C160_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 15 },   conductor := 160,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, -1, 0, -2, 0, 1, 0, -4, 0, -6, 0, 2, 0, 2, 0, 8, 0, 4, 0, -6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5432751652517836475372314453125,   alphaHi := (5397215081808807583452231630848 : Rat)/10865503305035672855377197265625,   finite := ((1016554854156945 : Rat)/2251799813685248, (15816454661043071 : Rat)/9007199254740992),   tail := (43243430616500991753946802639007568359375 : Rat)/1893606165838476057726909987938412871548928,   box := { reLo := (425516392742115062161732035630371248846439520135 : Rat)/992794989475122935353526183756254607598644363264,            reHi := (7063997505204112887544630011847665191965860299753 : Rat)/3971179957900491741414104735025018430394577453056,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
def localData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C160_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C160_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C160_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C162_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 8 },   conductor := 162,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, -4, -1, 0, 3, 0, 0, -1, 4, 0, 1, -3, 0, -4, -3, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10933201799913778972625732421875,   alphaHi := (2698607540904403791726115815424 : Rat)/5466600899956889438629150390625,   finite := ((1733852739150191 : Rat)/4503599627370496, (14792273889745267 : Rat)/9007199254740992),   tail := (36566228401831713626456353755474090576171875 : Rat)/1514668226335665988325255522137012870834028544,   box := { reLo := (286560040029117626820879711968360074648064759734787 : Rat)/794122375049073649687071567190170204023831157276672,            reHi := (2646672837583058734830847041778610629314511927694519 : Rat)/1588244750098147299374143134380340408047662314553344,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C162_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C162_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C162_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 39, a6 := -19 },   conductor := 162,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, -4, -1, 0, 3, 0, 0, -1, 4, 0, 1, -3, 0, -4, -3, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/10933201799913778972625732421875,   alphaHi := (2698607540904403791726115815424 : Rat)/5466600899956889438629150390625,   finite := ((1733852739150191 : Rat)/4503599627370496, (14792273889745267 : Rat)/9007199254740992),   tail := (36566228401831713626456353755474090576171875 : Rat)/1514668226335665988325255522137012870834028544,   box := { reLo := (286560040029117626820879711968360074648064759734787 : Rat)/794122375049073649687071567190170204023831157276672,            reHi := (2646672837583058734830847041778610629314511927694519 : Rat)/1588244750098147299374143134380340408047662314553344,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C162_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C162_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C162_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C163_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := 1 },   conductor := 163,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -4, 0, 2, 0, -3, 0, -6, 0, 4, 0, 0, 4, 0, 0, -6, 8, 0, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5483447167626088237762451171875,   alphaHi := (5397215081808807583452231630848 : Rat)/10966894335252176380157470703125,   finite := ((538353305015989 : Rat)/1125899906842624, (17090169824311415 : Rat)/9007199254740992),   tail := (9394959667442188607788852570438385009765625 : Rat)/378639345417740383885550334364093580232884224,   box := { reLo := (44997771922584584886645075989970240363432882336691 : Rat)/99258032565188135193293706851540947496569202016256,            reHi := (1526352248403756021049426446974485244774481994048385 : Rat)/794064260521505081546349654812327579972553616130048,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [163] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C163_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C163_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C166_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -6, a6 := 4 },   conductor := 166,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -2, 1, 1, -1, -2, 2, -5, -1, -2, -1, 2, 1, -3, 2, -2, -2, -1, 5, 4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/11067356533943931102752685546875,   alphaHi := (2698607540904403791726115815424 : Rat)/5533678266971965503692626953125,   finite := ((3139640770457471 : Rat)/9007199254740992, (14710693743521483 : Rat)/9007199254740992),   tail := (20367002547355187489021349731922149658203125 : Rat)/757107401926771949689953829663246262024011776,   box := { reLo := (255368139657492157727258413103603409701325583926413 : Rat)/793884651082766823918093026892968112448090172030976,            reHi := (1317940742110811922949110909622334638976846728406449 : Rat)/793884651082766823918093026892968112448090172030976,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 83] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C166_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C166_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C170_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 6 },   conductor := 170,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -2, 1, 1, 2, -2, -1, 1, -1, -2, -2, -6, 2, -2, 1, 1, -1, -8, 1, 4, 2, -2, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/11199904450539966678619384765625,   alphaHi := (674651885226100947931528953856 : Rat)/1399988056317495822906494140625,   finite := ((2105220876479215 : Rat)/9007199254740992, (14963486541486859 : Rat)/9007199254740992),   tail := (45209699853155693147424258320522308349609375 : Rat)/1513734369910389737206615843220651252983529472,   box := { reLo := (323580161453580372659862830936107607410180838640565 : Rat)/1587265530663156829081164414420937608248457399631872,            reHi := (2684299443658047274818276960658731978010245645107369 : Rat)/1587265530663156829081164414420937608248457399631872,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C170_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C170_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C170_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 12, a6 := 38 },   conductor := 170,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -2, 1, 1, 2, -2, -1, 1, -1, -2, -2, -6, 2, -2, 1, 1, -1, -8, 1, 4, 2, -2, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/11199904450539966678619384765625,   alphaHi := (674651885226100947931528953856 : Rat)/1399988056317495822906494140625,   finite := ((2105220876479215 : Rat)/9007199254740992, (14963486541486859 : Rat)/9007199254740992),   tail := (45209699853155693147424258320522308349609375 : Rat)/1513734369910389737206615843220651252983529472,   box := { reLo := (323580161453580372659862830936107607410180838640565 : Rat)/1587265530663156829081164414420937608248457399631872,            reHi := (2684299443658047274818276960658731978010245645107369 : Rat)/1587265530663156829081164414420937608248457399631872,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 5, 5, 17, 17] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C170_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C170_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C170_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C171_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6924, a6 := 221760 },   conductor := 171,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, -1, 0, 0, 0, -3, 0, -4, 0, 0, 4, 3, 0, 1, 6, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11232797045445686054229736328125,   alphaHi := (1349303770452201895863057907712 : Rat)/2808199261361421489715576171875,   finite := ((4189446690283057 : Rat)/9007199254740992, (4558929771741783 : Rat)/2251799813685248),   tail := (23188930915166758042380827337932586669921875 : Rat)/756804998666936406344725983070614933781610496,   box := { reLo := (344790387386169717634032940532247747599561271100291 : Rat)/793567558282181509219327392424253124804986007453696,            reHi := (407737408548131279150290210388466431111545262388629 : Rat)/198391889570545377304831848106063281201246501863424,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C171_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C171_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C171_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -84, a6 := 315 },   conductor := 171,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, -1, 0, 0, 0, -3, 0, -4, 0, 0, 4, 3, 0, 1, 6, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11232797045445686054229736328125,   alphaHi := (1349303770452201895863057907712 : Rat)/2808199261361421489715576171875,   finite := ((4189446690283057 : Rat)/9007199254740992, (4558929771741783 : Rat)/2251799813685248),   tail := (23188930915166758042380827337932586669921875 : Rat)/756804998666936406344725983070614933781610496,   box := { reLo := (344790387386169717634032940532247747599561271100291 : Rat)/793567558282181509219327392424253124804986007453696,            reHi := (407737408548131279150290210388466431111545262388629 : Rat)/198391889570545377304831848106063281201246501863424,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19, 19, 19] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C171_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C171_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C171_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C171_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 0 },   conductor := 171,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, -1, 0, 0, 0, -3, 0, -4, 0, 0, 4, 3, 0, 1, 6, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11232797045445686054229736328125,   alphaHi := (1349303770452201895863057907712 : Rat)/2808199261361421489715576171875,   finite := ((4189446690283057 : Rat)/9007199254740992, (4558929771741783 : Rat)/2251799813685248),   tail := (23188930915166758042380827337932586669921875 : Rat)/756804998666936406344725983070614933781610496,   box := { reLo := (344790387386169717634032940532247747599561271100291 : Rat)/793567558282181509219327392424253124804986007453696,            reHi := (407737408548131279150290210388466431111545262388629 : Rat)/198391889570545377304831848106063281201246501863424,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C171_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C171_b3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C171_b3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C172_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := 15 },   conductor := 172,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -4, 0, 1, 0, -3, 0, -1, 0, 0, 0, -3, 0, 2, 0, 8, 0, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5632796801481518840789794921875,   alphaHi := (5397215081808807583452231630848 : Rat)/11265593602963037586212158203125,   finite := ((3816055728132559 : Rat)/9007199254740992, (8729215549328521 : Rat)/4503599627370496),   tail := (110106513253349709591072276592254638671875 : Rat)/3503434972782073127574002383219608027922432,   box := { reLo := (2881873350568876002927361151040013182625497829603 : Rat)/7347235660039870223638074245973767414973584113664,            reHi := (7235937447410418378588884644932805246665004740757 : Rat)/3673617830019935111819037122986883707486792056832,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C172_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C172_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C172_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 67, a6 := 79 },   conductor := 172,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -2, 0, 0, 0, -4, 0, 1, 0, -3, 0, -1, 0, 0, 0, -3, 0, 2, 0, 8, 0, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5632796801481518840789794921875,   alphaHi := (5397215081808807583452231630848 : Rat)/11265593602963037586212158203125,   finite := ((3816055728132559 : Rat)/9007199254740992, (8729215549328521 : Rat)/4503599627370496),   tail := (110106513253349709591072276592254638671875 : Rat)/3503434972782073127574002383219608027922432,   box := { reLo := (2881873350568876002927361151040013182625497829603 : Rat)/7347235660039870223638074245973767414973584113664,            reHi := (7235937447410418378588884644932805246665004740757 : Rat)/3673617830019935111819037122986883707486792056832,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43, 43, 43] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C172_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C172_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C172_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C175_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -148, a6 := 748 },   conductor := 175,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, 0, 2, 1, 0, -2, 0, -3, -2, -1, -2, 0, -4, -7, 4, 0, 0, -1, 6, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11363415354371539592742919921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5681707677185769748687744140625,   finite := ((71682800359717 : Rat)/1125899906842624, (6990372095795321 : Rat)/4503599627370496),   tail := (25625928056876218393302340543270111083984375 : Rat)/756547645348785919078311077308617817317179392,   box := { reLo := (2954530507810213798236118030141249377211553779517 : Rat)/99162212971156067985432389524995154551397337268224,            reHi := (629103564335240369718871430036795131292890968852721 : Rat)/396648851884624271941729558099980618205589349072896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C175_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C175_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C175_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 2, a6 := -2 },   conductor := 175,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, -1, 2, 0, 2, 1, 0, -2, 0, -3, -2, -1, -2, 0, -4, -7, 4, 0, 0, -1, 6, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11363415354371539592742919921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5681707677185769748687744140625,   finite := ((71682800359717 : Rat)/1125899906842624, (6990372095795321 : Rat)/4503599627370496),   tail := (25625928056876218393302340543270111083984375 : Rat)/756547645348785919078311077308617817317179392,   box := { reLo := (2954530507810213798236118030141249377211553779517 : Rat)/99162212971156067985432389524995154551397337268224,            reHi := (629103564335240369718871430036795131292890968852721 : Rat)/396648851884624271941729558099980618205589349072896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C175_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C175_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C175_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C175_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3283, a6 := -74657 },   conductor := 175,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, -1, 0, -2, 0, -3, 2, -5, 0, 0, 4, -3, 0, 2, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11363415354371539592742919921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5681707677185769748687744140625,   finite := ((3827411342779681 : Rat)/9007199254740992, (9123484994771801 : Rat)/4503599627370496),   tail := (25625928056876218393302340543270111083984375 : Rat)/756547645348785919078311077308617817317179392,   box := { reLo := (310223689193984126406511526381440104475491315221081 : Rat)/793297703769248543883459116199961236411178698145792,            reHi := (816974790093670288780694259027770176128506201941201 : Rat)/396648851884624271941729558099980618205589349072896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C175_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C175_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C175_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -33, a6 := 93 },   conductor := 175,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, -1, 0, -2, 0, -3, 2, -5, 0, 0, 4, -3, 0, 2, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11363415354371539592742919921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5681707677185769748687744140625,   finite := ((3827411342779681 : Rat)/9007199254740992, (9123484994771801 : Rat)/4503599627370496),   tail := (25625928056876218393302340543270111083984375 : Rat)/756547645348785919078311077308617817317179392,   box := { reLo := (310223689193984126406511526381440104475491315221081 : Rat)/793297703769248543883459116199961236411178698145792,            reHi := (816974790093670288780694259027770176128506201941201 : Rat)/396648851884624271941729558099980618205589349072896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C175_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C175_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C175_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C175_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 217, a6 := -282 },   conductor := 175,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, -1, 0, -2, 0, -3, 2, -5, 0, 0, 4, -3, 0, 2, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11363415354371539592742919921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5681707677185769748687744140625,   finite := ((3827411342779681 : Rat)/9007199254740992, (9123484994771801 : Rat)/4503599627370496),   tail := (25625928056876218393302340543270111083984375 : Rat)/756547645348785919078311077308617817317179392,   box := { reLo := (310223689193984126406511526381440104475491315221081 : Rat)/793297703769248543883459116199961236411178698145792,            reHi := (816974790093670288780694259027770176128506201941201 : Rat)/396648851884624271941729558099980618205589349072896,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C175_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C175_b3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C175_b3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C176_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 289 },   conductor := 176,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, -2, 0, -2, 0, 1, 0, -4, 0, 3, 0, 6, 0, -8, 0, 2, 0, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5697918003071719455718994140625,   alphaHi := (5397215081808807583452231630848 : Rat)/11395836006143438816070556640625,   finite := ((242430589958715 : Rat)/562949953421312, (18665766680057915 : Rat)/9007199254740992),   tail := (13130352277046801769000203643512725830078125 : Rat)/378240571267449791664892498376312076458000384,   box := { reLo := (19628869750518427181689576798596270467613846817235 : Rat)/49576748157167179093100789547179976485503026331648,            reHi := (1671355672053605814633831487730821411127508641454035 : Rat)/793227970514674865489612632754879623768048421306368,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C176_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C176_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C176_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 1 },   conductor := 176,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -3, 0, -2, 0, -2, 0, 1, 0, -4, 0, 3, 0, 6, 0, -8, 0, 2, 0, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/5697918003071719455718994140625,   alphaHi := (5397215081808807583452231630848 : Rat)/11395836006143438816070556640625,   finite := ((242430589958715 : Rat)/562949953421312, (18665766680057915 : Rat)/9007199254740992),   tail := (13130352277046801769000203643512725830078125 : Rat)/378240571267449791664892498376312076458000384,   box := { reLo := (19628869750518427181689576798596270467613846817235 : Rat)/49576748157167179093100789547179976485503026331648,            reHi := (1671355672053605814633831487730821411127508641454035 : Rat)/793227970514674865489612632754879623768048421306368,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C176_a1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C176_a2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C176_a2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C184_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 1 },   conductor := 184,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -4, 0, 2, 0, -2, 0, -4, 0, -5, 0, 4, 0, -2, 0, 6, 0, -2, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11651954187281303501129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/728247136705081462860107421875,   finite := ((3373823893004911 : Rat)/9007199254740992, (19983114014107855 : Rat)/9007199254740992),   tail := (2537391222905411053203535803028106689453125 : Rat)/60473408046650358864575445596488814785724416,   box := { reLo := (21091178132603465522782029726613206128662110607103 : Rat)/63410964315924446696781062441783855452755765231616,            reHi := (143342394864864352177563071932778863299137596696415 : Rat)/63410964315924446696781062441783855452755765231616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C184_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C184_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C184_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 5 },   conductor := 184,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, -4, 0, -2, 0, -2, 0, 7, 0, 2, 0, -4, 0, -6, 0, 4, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11651954187281303501129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/728247136705081462860107421875,   finite := ((3430385855451037 : Rat)/9007199254740992, (20077380869261147 : Rat)/9007199254740992),   tail := (2537391222905411053203535803028106689453125 : Rat)/60473408046650358864575445596488814785724416,   box := { reLo := (21489376116335434254355395529813405038571848781901 : Rat)/63410964315924446696781062441783855452755765231616,            reHi := (144006036471899246848047662390725984629081328005931 : Rat)/63410964315924446696781062441783855452755765231616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C184_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C184_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C185_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -156, a6 := 700 },   conductor := 185,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 1, 2, -1, -2, -5, 0, -2, 2, 3, 2, -2, 10, -1, -4, -4, 4, -4, -2, -5, -6, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11683574202505442333221435546875,   alphaHi := (2698607540904403791726115815424 : Rat)/5841787101252721118927001953125,   finite := ((126369953232409 : Rat)/1125899906842624, (17128792316432439 : Rat)/9007199254740992),   tail := (67599585507508638578280827312469482421875 : Rat)/1574673307605203234158490379247552787644416,   box := { reLo := (14305234096582088665468709780591200684452001757 : Rat)/206395579774429198307621650988735238982128893952,            reHi := (3210866706027101194742719147480144967054888256947 : Rat)/1651164638195433586460973207909881911857031151616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 37] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C185_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C185_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C185_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -5, a6 := 6 },   conductor := 185,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 1, 0, -3, 0, -2, 0, -5, 2, 4, 0, -1, 4, -4, 0, -8, -2, 3, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11683574202505442333221435546875,   alphaHi := (2698607540904403791726115815424 : Rat)/5841787101252721118927001953125,   finite := ((3254841774183747 : Rat)/9007199254740992, (10003488723949391 : Rat)/4503599627370496),   tail := (67599585507508638578280827312469482421875 : Rat)/1574673307605203234158490379247552787644416,   box := { reLo := (525781596787445842019080297594212719524604773231 : Rat)/1651164638195433586460973207909881911857031151616,            reHi := (1869242189525947584961635488077560274753759449643 : Rat)/825582319097716793230486603954940955928515575808,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 37] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C185_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C185_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C185_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -4, a6 := -3 },   conductor := 185,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, -1, -1, -2, -2, -3, 1, -1, 0, 2, -2, -2, 2, -1, 2, 1, 2, 1, 4, 0, -8, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/11683574202505442333221435546875,   alphaHi := (2698607540904403791726115815424 : Rat)/5841787101252721118927001953125,   finite := ((2056209768041919 : Rat)/4503599627370496, (23076978037764475 : Rat)/9007199254740992),   tail := (67599585507508638578280827312469482421875 : Rat)/1574673307605203234158490379247552787644416,   box := { reLo := (341494703720170122297802989786856875682454096987 : Rat)/825582319097716793230486603954940955928515575808,            reHi := (4301264913806604483548268318513136312005061879175 : Rat)/1651164638195433586460973207909881911857031151616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 37] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C185_c1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C185_c1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C185_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := -9 },   conductor := 185,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, -1, -1, -2, -2, -3, 1, -1, 0, 2, -2, -2, 2, -1, 2, 1, 2, 1, 4, 0, -8, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/11683574202505442333221435546875,   alphaHi := (2698607540904403791726115815424 : Rat)/5841787101252721118927001953125,   finite := ((2056209768041919 : Rat)/4503599627370496, (23076978037764475 : Rat)/9007199254740992),   tail := (67599585507508638578280827312469482421875 : Rat)/1574673307605203234158490379247552787644416,   box := { reLo := (341494703720170122297802989786856875682454096987 : Rat)/825582319097716793230486603954940955928515575808,            reHi := (4301264913806604483548268318513136312005061879175 : Rat)/1651164638195433586460973207909881911857031151616,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [5, 5, 37, 37] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C185_c1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C185_c2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C185_c2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C189_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 0 },   conductor := 189,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, -1, 0, -1, 0, 0, 2, -4, 0, -2, 2, 0, -4, 3, 0, -8, -2, 0, 8, -6, 0, -4, 4, 0, -2, -4, 0,                    6, 8, 0, -6, 1, 0, -3, 16, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11809207644767883014678955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2952301911191970729827880859375,   finite := ((3980809387312947 : Rat)/9007199254740992, (3227879842129201 : Rat)/2251799813685248),   tail := (70959358721591652288099714017581939697265625 : Rat)/1511073271040901264013062543391662819485155328,   box := { reLo := (625866183462003457634240949111022180842443315920523 : Rat)/1584475166254984083813761069499456232604466233212928,            reHi := (586424630871236380846448858199665632902104864994809 : Rat)/396118791563746020953440267374864058151116558303232,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C189_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C189_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C189_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3834, a6 := -91375 },   conductor := 189,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, 1, 0, 0, 0, -6, 0, -4, 0, 0, 4, -3, 0, 2, 6, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11809207644767883014678955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2952301911191970729827880859375,   finite := ((1618867524658455 : Rat)/4503599627370496, (21325385831440643 : Rat)/9007199254740992),   tail := (70959358721591652288099714017581939697265625 : Rat)/1511073271040901264013062543391662819485155328,   box := { reLo := (247575215107124410805364502090821550358616479486095 : Rat)/792237583127492041906880534749728116302233116606464,            reHi := (3825799283515466532873136316918411509355108093741787 : Rat)/1584475166254984083813761069499456232604466233212928,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C189_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C189_b1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C189_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -54, a6 := -88 },   conductor := 189,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, 1, 0, 0, 0, -6, 0, -4, 0, 0, 4, -3, 0, 2, 6, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11809207644767883014678955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2952301911191970729827880859375,   finite := ((1618867524658455 : Rat)/4503599627370496, (21325385831440643 : Rat)/9007199254740992),   tail := (70959358721591652288099714017581939697265625 : Rat)/1511073271040901264013062543391662819485155328,   box := { reLo := (247575215107124410805364502090821550358616479486095 : Rat)/792237583127492041906880534749728116302233116606464,            reHi := (3825799283515466532873136316918411509355108093741787 : Rat)/1584475166254984083813761069499456232604466233212928,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C189_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C189_b2.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C189_b2

namespace VerifiedLcalc.Certificates.DerivativeBatch.C189_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -24, a6 := 45 },   conductor := 189,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -3, 0, 1, 0, 0, 0, -6, 0, -4, 0, 0, 4, -3, 0, 2, 6, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/11809207644767883014678955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/2952301911191970729827880859375,   finite := ((1618867524658455 : Rat)/4503599627370496, (21325385831440643 : Rat)/9007199254740992),   tail := (70959358721591652288099714017581939697265625 : Rat)/1511073271040901264013062543391662819485155328,   box := { reLo := (247575215107124410805364502090821550358616479486095 : Rat)/792237583127492041906880534749728116302233116606464,            reHi := (3825799283515466532873136316918411509355108093741787 : Rat)/1584475166254984083813761069499456232604466233212928,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [3, 3, 3, 7] }
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.DerivativeBatch.C189_b1.payload_correct
  exact ⟨h.1, h.2.1, h.2.2.1, by decide +kernel, h.2.2.2.2⟩
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C189_b3.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C189_b3

namespace VerifiedLcalc.Certificates.DerivativeBatch.C190_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := 2 },   conductor := 190,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, -1, -1, -2, 1, 0, -1, -3, 1, 1, 1, -7, 2, -1, -1, 1, 0, -5, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/11840407719339422893524169921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5920203859669711399078369140625,   finite := ((880214952478467 : Rat)/4503599627370496, (9174191117175619 : Rat)/4503599627370496),   tail := (18132763002088199538471248061275482177734375 : Rat)/377728882246200318483555242391289830842564608,   box := { reLo := (29199280012012661760009087594165302770306518939483 : Rat)/198038720215095872577106210922844562832786513199104,            reHi := (412927435350507529129900646343816382647888360197531 : Rat)/198038720215095872577106210922844562832786513199104,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 5, 5, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C190_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C190_a1

namespace VerifiedLcalc.Certificates.DerivativeBatch.C190_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -48, a6 := 147 },   conductor := 190,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -3, 1, -1, -3, -5, 1, 6, -1, -4, -3, -1, -5, 3, 1, -3, 6, 1, -1, 15, -4, 7, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/11840407719339422893524169921875,   alphaHi := (2698607540904403791726115815424 : Rat)/5920203859669711399078369140625,   finite := ((1713504534534823 : Rat)/4503599627370496, (11807562796211085 : Rat)/4503599627370496),   tail := (18132763002088199538471248061275482177734375 : Rat)/377728882246200318483555242391289830842564608,   box := { reLo := (65841880610006921011907182484176523803810623613727 : Rat)/198038720215095872577106210922844562832786513199104,            reHi := (528725818936251409563992587685637096601022013066165 : Rat)/198038720215095872577106210922844562832786513199104,            imLo := 0,            imHi := 0 } }
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 19] }
def localData : WildData := { atTwo := none, atThree := none }
theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel
theorem analytic_rank_one : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 1 :=
  certifyDerivativeModel result nonsingular minimality (by decide +kernel)
    localData (by decide +kernel) (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)
def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} := ⟨1,analytic_rank_one⟩
/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C190_b1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_one
end VerifiedLcalc.Certificates.DerivativeBatch.C190_b1
