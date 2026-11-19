module
public import VerifiedLcalc.Assumptions.Batch
public import VerifiedLcalc.Assumptions.FastSign
public import VerifiedLcalc.Assumptions.TameCertification
public import VerifiedLcalc.Assumptions.WildCertification

@[expose] public section

namespace VerifiedLcalc.Certificates.Batch.C64_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := -112 },   conductor := 64,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6871947673600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/400000000000000000000,   geometricUpper := (4106725564621885 : Rat)/9007199254740992,   tail := (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,   box := { reLo := (21141622944216898704672059881095401791556758581936223421081239354987578613568839613898545314725970829893509289867434006045100935312256030923255183 : Rat)/34540379261520847962041731669961680772073763941539779493436372092470511783660476395403092850834475929604979313974631708526609423061465163712430080,            reHi := (8588070399176613381288903485682380781370800879234902141773687936143020499668838924764369902054514849945337626900902782489060586536043583123705981 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/13816151704608339184816692667984672308829505576615911797374548836988204713464190558161237140333790371841991725589852683410643769224586065484972032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C64_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C64_a1

namespace VerifiedLcalc.Certificates.Batch.C64_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := 112 },   conductor := 64,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6871947673600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/400000000000000000000,   geometricUpper := (4106725564621885 : Rat)/9007199254740992,   tail := (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,   box := { reLo := (21141622944216898704672059881095401791556758581936223421081239354987578613568839613898545314725970829893509289867434006045100935312256030923255183 : Rat)/34540379261520847962041731669961680772073763941539779493436372092470511783660476395403092850834475929604979313974631708526609423061465163712430080,            reHi := (8588070399176613381288903485682380781370800879234902141773687936143020499668838924764369902054514849945337626900902782489060586536043583123705981 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/13816151704608339184816692667984672308829505576615911797374548836988204713464190558161237140333790371841991725589852683410643769224586065484972032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C64_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C64_a2

namespace VerifiedLcalc.Certificates.Batch.C64_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 0 },   conductor := 64,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6871947673600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/400000000000000000000,   geometricUpper := (4106725564621885 : Rat)/9007199254740992,   tail := (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,   box := { reLo := (21141622944216898704672059881095401791556758581936223421081239354987578613568839613898545314725970829893509289867434006045100935312256030923255183 : Rat)/34540379261520847962041731669961680772073763941539779493436372092470511783660476395403092850834475929604979313974631708526609423061465163712430080,            reHi := (8588070399176613381288903485682380781370800879234902141773687936143020499668838924764369902054514849945337626900902782489060586536043583123705981 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/13816151704608339184816692667984672308829505576615911797374548836988204713464190558161237140333790371841991725589852683410643769224586065484972032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C64_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C64_a3

namespace VerifiedLcalc.Certificates.Batch.C64_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 0 },   conductor := 64,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6871947673600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/400000000000000000000,   geometricUpper := (4106725564621885 : Rat)/9007199254740992,   tail := (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,   box := { reLo := (21141622944216898704672059881095401791556758581936223421081239354987578613568839613898545314725970829893509289867434006045100935312256030923255183 : Rat)/34540379261520847962041731669961680772073763941539779493436372092470511783660476395403092850834475929604979313974631708526609423061465163712430080,            reHi := (8588070399176613381288903485682380781370800879234902141773687936143020499668838924764369902054514849945337626900902782489060586536043583123705981 : Rat)/6908075852304169592408346333992336154414752788307955898687274418494102356732095279080618570166895185920995862794926341705321884612293032742486016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2179872905166615746446564362811863521117131094239892639137674276686006865234983443535119615547497521780970150191426704091241286955510712611328125 : Rat)/13816151704608339184816692667984672308829505576615911797374548836988204713464190558161237140333790371841991725589852683410643769224586065484972032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C64_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C64_a4

namespace VerifiedLcalc.Certificates.Batch.C66_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -81, a6 := -284 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, 1, 1, 0, -1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/6800759856550016533452097215724090164781675386973080002617675196250535846776632860819198396566897014779962669877239232785602922340436326079266816,   box := { reLo := (20940270109606524773317827413650431913955278931849869150915552699256216353876794776085204157285831582486692049311038823695404286109104398407385773 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            reHi := (54936429083213839850295397642641494156807842225764545162852078776529418625924865575835112216635442226766385996398275988662462269091393484416793939 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/13601519713100033066904194431448180329563350773946160005235350392501071693553265721638396793133794029559925339754478465571205844680872652158533632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_a1

namespace VerifiedLcalc.Certificates.Batch.C66_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -41, a6 := -556 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, 1, 1, 0, -1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/6800759856550016533452097215724090164781675386973080002617675196250535846776632860819198396566897014779962669877239232785602922340436326079266816,   box := { reLo := (20940270109606524773317827413650431913955278931849869150915552699256216353876794776085204157285831582486692049311038823695404286109104398407385773 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            reHi := (54936429083213839850295397642641494156807842225764545162852078776529418625924865575835112216635442226766385996398275988662462269091393484416793939 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/13601519713100033066904194431448180329563350773946160005235350392501071693553265721638396793133794029559925339754478465571205844680872652158533632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_a2

namespace VerifiedLcalc.Certificates.Batch.C66_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6, a6 := 4 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, 1, 1, 0, -1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/6800759856550016533452097215724090164781675386973080002617675196250535846776632860819198396566897014779962669877239232785602922340436326079266816,   box := { reLo := (20940270109606524773317827413650431913955278931849869150915552699256216353876794776085204157285831582486692049311038823695404286109104398407385773 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            reHi := (54936429083213839850295397642641494156807842225764545162852078776529418625924865575835112216635442226766385996398275988662462269091393484416793939 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/13601519713100033066904194431448180329563350773946160005235350392501071693553265721638396793133794029559925339754478465571205844680872652158533632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_a3

namespace VerifiedLcalc.Certificates.Batch.C66_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 4, a6 := 20 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, 1, 1, 0, -1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/6800759856550016533452097215724090164781675386973080002617675196250535846776632860819198396566897014779962669877239232785602922340436326079266816,   box := { reLo := (20940270109606524773317827413650431913955278931849869150915552699256216353876794776085204157285831582486692049311038823695404286109104398407385773 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            reHi := (54936429083213839850295397642641494156807842225764545162852078776529418625924865575835112216635442226766385996398275988662462269091393484416793939 : Rat)/47605318995850115734164680510068631153471727708811560018323726373753750927436430025734388775968279103459738689140674629499220456383054282554867712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2428297069543376884384404255459113777452287940060009132270289668498610612185704010115087335482755987769540566286951868855498919988283145666342229 : Rat)/13601519713100033066904194431448180329563350773946160005235350392501071693553265721638396793133794029559925339754478465571205844680872652158533632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_a4

namespace VerifiedLcalc.Certificates.Batch.C66_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -352, a6 := -2689 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (1811669279497711302329759166994049033829399157577233691396535772094952142011972968012080375738857924416925932623 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (516230521752925739280420888256963231245084932551431716171349650425563494530752457282195103991251075518848168289201 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_b1

namespace VerifiedLcalc.Certificates.Batch.C66_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -22, a6 := -49 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (1811669279497711302329759166994049033829399157577233691396535772094952142011972968012080375738857924416925932623 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (516230521752925739280420888256963231245084932551431716171349650425563494530752457282195103991251075518848168289201 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_b2

namespace VerifiedLcalc.Certificates.Batch.C66_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -12, a6 := -81 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (1811669279497711302329759166994049033829399157577233691396535772094952142011972968012080375738857924416925932623 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (516230521752925739280420888256963231245084932551431716171349650425563494530752457282195103991251075518848168289201 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_b3

namespace VerifiedLcalc.Certificates.Batch.C66_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2, a6 := -1 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 2, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (1811669279497711302329759166994049033829399157577233691396535772094952142011972968012080375738857924416925932623 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (516230521752925739280420888256963231245084932551431716171349650425563494530752457282195103991251075518848168289201 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_b4

namespace VerifiedLcalc.Certificates.Batch.C66_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -10065, a6 := -389499 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, 1, -4, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (22231470068418671858718911988741955878865070093336073596671749859721340803691530554382861689154189809744601488463 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (536650322541846720628444308134522331492410263641546496187351411280455517211528067329131246576359668645106925626289 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_c1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_c1

namespace VerifiedLcalc.Certificates.Batch.C66_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -10055, a6 := -390309 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, 1, -4, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (22231470068418671858718911988741955878865070093336073596671749859721340803691530554382861689154189809744601488463 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (536650322541846720628444308134522331492410263641546496187351411280455517211528067329131246576359668645106925626289 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_c2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_c2

namespace VerifiedLcalc.Certificates.Batch.C66_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -45, a6 := 81 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, 1, -4, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (22231470068418671858718911988741955878865070093336073596671749859721340803691530554382861689154189809744601488463 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (536650322541846720628444308134522331492410263641546496187351411280455517211528067329131246576359668645106925626289 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_c3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_c3

namespace VerifiedLcalc.Certificates.Batch.C66_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 115, a6 := 561 },   conductor := 66,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, 1, -4, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1744623962967973232269287109375,   alphaHi := (5397215081808807583452231630848 : Rat)/6978495851871892833709716796875,   geometricUpper := (4156267879329109 : Rat)/9007199254740992,   tail := (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/46818598168768093504098043199163944442118225336553659653924702170540056802142373820536394021779727495235060629504,   box := { reLo := (22231470068418671858718911988741955878865070093336073596671749859721340803691530554382861689154189809744601488463 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            reHi := (536650322541846720628444308134522331492410263641546496187351411280455517211528067329131246576359668645106925626289 : Rat)/234092990843840467520490215995819722210591126682768298269623510852700284010711869102681970108898637476175303147520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (51441885247342783825442844220569204241536238448535652896957337540216963196448900561152410201131120877093512110269 : Rat)/93637196337536187008196086398327888884236450673107319307849404341080113604284747641072788043559454990470121259008, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C66_c4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C66_c4

namespace VerifiedLcalc.Certificates.Batch.C67_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -12, a6 := -21 },   conductor := 67,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 2, -2, 2, 2, -4],   alphaLo := (5397215081808807583435051761664 : Rat)/7031164492283024311065673828125,   alphaHi := (1349303770452201895863057907712 : Rat)/1757791123070756053924560546875,   geometricUpper := (2090208321651179 : Rat)/4503599627370496,   tail := (418522843355333652539111603967979151057921182423417937179469794031983907898672949595998575987506100292708499459 : Rat)/362546457769727368560324858222029776432829886900926304615422074330055067012789220190004528878609458681247432704,   box := { reLo := (661596282818391854060342826899589121726857716517169693481139551840496202159853264165886910052962653815489724371 : Rat)/5438196866545910528404872873330446646492448303513894569231331114950826005191838302850067933179141880218711490560,            reHi := (2643456316695681549920052413631767481515187756171651905160834012867991406474111034938848424522744909220900601865 : Rat)/1087639373309182105680974574666089329298489660702778913846266222990165201038367660570013586635828376043742298112,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (418522843355333652539111603967979151057921182423417937179469794031983907898672949595998575987506100292708499459 : Rat)/725092915539454737120649716444059552865659773801852609230844148660110134025578440380009057757218917362494865408, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C67_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C67_a1

namespace VerifiedLcalc.Certificates.Batch.C69_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -16, a6 := -25 },   conductor := 69,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, -2, -3],   alphaLo := (337325942613050473964690735104 : Rat)/445958472892578983306884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/7135335566281263637542724609375,   geometricUpper := (4227528534347499 : Rat)/9007199254740992,   tail := (943251949755183056032143485332256897619785181075876096632738029888324727629915761447469932904129754132079982508365420454851277747852787986840313 : Rat)/2215466239018576263311591622978088962408189304469213871153114029376192069639427521201931464853048454438399307061797498788572729803440637473718272,   box := { reLo := (36141688234505991851893974029527529817203366060612162316314448495642490760743957715145759129277532546573876645877622924448147190443660864079505811 : Rat)/46524791019390101529543424082539868210571975393853491294215394616900033462427977945240560761914017543206385448297747474560027325872253386948083712,            reHi := (75758270124223710274607412959545048824404147634320923862086987335514733661957227153128501575006089057876682123682823721600475745332140013172053613 : Rat)/46524791019390101529543424082539868210571975393853491294215394616900033462427977945240560761914017543206385448297747474560027325872253386948083712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (943251949755183056032143485332256897619785181075876096632738029888324727629915761447469932904129754132079982508365420454851277747852787986840313 : Rat)/4430932478037152526623183245956177924816378608938427742306228058752384139278855042403862929706096908876798614123594997577145459606881274947436544, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C69_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C69_a1

namespace VerifiedLcalc.Certificates.Batch.C69_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := -1 },   conductor := 69,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, -2, -3],   alphaLo := (337325942613050473964690735104 : Rat)/445958472892578983306884765625,   alphaHi := (5397215081808807583452231630848 : Rat)/7135335566281263637542724609375,   geometricUpper := (4227528534347499 : Rat)/9007199254740992,   tail := (943251949755183056032143485332256897619785181075876096632738029888324727629915761447469932904129754132079982508365420454851277747852787986840313 : Rat)/2215466239018576263311591622978088962408189304469213871153114029376192069639427521201931464853048454438399307061797498788572729803440637473718272,   box := { reLo := (36141688234505991851893974029527529817203366060612162316314448495642490760743957715145759129277532546573876645877622924448147190443660864079505811 : Rat)/46524791019390101529543424082539868210571975393853491294215394616900033462427977945240560761914017543206385448297747474560027325872253386948083712,            reHi := (75758270124223710274607412959545048824404147634320923862086987335514733661957227153128501575006089057876682123682823721600475745332140013172053613 : Rat)/46524791019390101529543424082539868210571975393853491294215394616900033462427977945240560761914017543206385448297747474560027325872253386948083712,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (943251949755183056032143485332256897619785181075876096632738029888324727629915761447469932904129754132079982508365420454851277747852787986840313 : Rat)/4430932478037152526623183245956177924816378608938427742306228058752384139278855042403862929706096908876798614123594997577145459606881274947436544, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C69_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C69_a2

namespace VerifiedLcalc.Certificates.Batch.C70_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -268, a6 := -1619 },   conductor := 70,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/7186854903668693447113037109375,   alphaHi := (2698607540904403791726115815424 : Rat)/3593427451834346675872802734375,   geometricUpper := (2125256945332779 : Rat)/4503599627370496,   tail := (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/1431555778835666616535888624212516351452602291527876035512289563475082772643974805895957392551344574675855589021810791155121812890027454103552,   box := { reLo := (36607861104421821582700270031403657288892070206827339933402127368872487972871597370696833631594260561923655256645016875350892885551961076000999 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            reHi := (81744432371407725410996483053001760255707331007165022878533232539112549109623453543764293824789136443191534102323720050071744881182593112479513 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/2863111557671333233071777248425032702905204583055752071024579126950165545287949611791914785102689149351711178043621582310243625780054908207104, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C70_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C70_a1

namespace VerifiedLcalc.Certificates.Batch.C70_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -88, a6 := 317 },   conductor := 70,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/7186854903668693447113037109375,   alphaHi := (2698607540904403791726115815424 : Rat)/3593427451834346675872802734375,   geometricUpper := (2125256945332779 : Rat)/4503599627370496,   tail := (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/1431555778835666616535888624212516351452602291527876035512289563475082772643974805895957392551344574675855589021810791155121812890027454103552,   box := { reLo := (36607861104421821582700270031403657288892070206827339933402127368872487972871597370696833631594260561923655256645016875350892885551961076000999 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            reHi := (81744432371407725410996483053001760255707331007165022878533232539112549109623453543764293824789136443191534102323720050071744881182593112479513 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/2863111557671333233071777248425032702905204583055752071024579126950165545287949611791914785102689149351711178043621582310243625780054908207104, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C70_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C70_a2

namespace VerifiedLcalc.Certificates.Batch.C70_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -18, a6 := -19 },   conductor := 70,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/7186854903668693447113037109375,   alphaHi := (2698607540904403791726115815424 : Rat)/3593427451834346675872802734375,   geometricUpper := (2125256945332779 : Rat)/4503599627370496,   tail := (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/1431555778835666616535888624212516351452602291527876035512289563475082772643974805895957392551344574675855589021810791155121812890027454103552,   box := { reLo := (36607861104421821582700270031403657288892070206827339933402127368872487972871597370696833631594260561923655256645016875350892885551961076000999 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            reHi := (81744432371407725410996483053001760255707331007165022878533232539112549109623453543764293824789136443191534102323720050071744881182593112479513 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/2863111557671333233071777248425032702905204583055752071024579126950165545287949611791914785102689149351711178043621582310243625780054908207104, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C70_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C70_a3

namespace VerifiedLcalc.Certificates.Batch.C70_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 2, a6 := -3 },   conductor := 70,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/7186854903668693447113037109375,   alphaHi := (2698607540904403791726115815424 : Rat)/3593427451834346675872802734375,   geometricUpper := (2125256945332779 : Rat)/4503599627370496,   tail := (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/1431555778835666616535888624212516351452602291527876035512289563475082772643974805895957392551344574675855589021810791155121812890027454103552,   box := { reLo := (36607861104421821582700270031403657288892070206827339933402127368872487972871597370696833631594260561923655256645016875350892885551961076000999 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            reHi := (81744432371407725410996483053001760255707331007165022878533232539112549109623453543764293824789136443191534102323720050071744881182593112479513 : Rat)/50104452259248331578756101847438072300841080203475661242930134721627897042539118206358508739297060113654945615763377690429263451150960893624320,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (644808160956941130767095207521782426693160385976076132912502081444411989987463332311630035688761495976613219891705663955439118639754910671251 : Rat)/2863111557671333233071777248425032702905204583055752071024579126950165545287949611791914785102689149351711178043621582310243625780054908207104, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C70_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C70_a4

namespace VerifiedLcalc.Certificates.Batch.C72_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3459, a6 := 78302 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a1

namespace VerifiedLcalc.Certificates.Batch.C72_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -579, a6 := -5362 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a2

namespace VerifiedLcalc.Certificates.Batch.C72_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := 1190 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 1, 0],                kodaira := -8 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a3

namespace VerifiedLcalc.Certificates.Batch.C72_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := -70 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a4

namespace VerifiedLcalc.Certificates.Batch.C72_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 6, a6 := -7 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a5

namespace VerifiedLcalc.Certificates.Batch.C72_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 141, a6 := 4718 },   conductor := 72,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7288801199942519283294677734375,   alphaHi := (2698607540904403791726115815424 : Rat)/3644400599971259593963623046875,   geometricUpper := (2147697857509881 : Rat)/4503599627370496,   tail := (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/4231372621030643371946252193573662492633401365094649076573947563754703988741045490516468015848551946706546247905517750260219988328227018899456,   box := { reLo := (9965141892420772725919920402774252095031213100827825095023855434669770429536737031823034721690131106601202384214656502774631123580637465492417 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            reHi := (31227304642189508192913653354627231630943824431651072262743632999443301152000740425577797793349074558825021838341974492330031186515863856792639 : Rat)/21156863105153216859731260967868312463167006825473245382869737818773519943705227452582340079242759733532731239527588751301099941641135094497280,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2126216274976872889011949946044896943158942459119832956410938846788405687075303206704796894778180484627994641656170630715221505335875202407027 : Rat)/8462745242061286743892504387147324985266802730189298153147895127509407977482090981032936031697103893413092495811035500520439976656454037798912, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 0, 2, 0, 2, 0],                kodaira := -12 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C72_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C72_a6

namespace VerifiedLcalc.Certificates.Batch.C73_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1, a6 := 0 },   conductor := 73,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, -1, 2, 0, 2, -3],   alphaLo := (674651885226100947929381470208 : Rat)/917405416576007747650146484375,   alphaHi := (5397215081808807583452231630848 : Rat)/7339243332608061885833740234375,   geometricUpper := (2158655939546911 : Rat)/4503599627370496,   tail := (6677607412813983633982704468009520202194973496891474831187532073159234310279793837556006520055267401648430486756680555944116777585059114586751 : Rat)/12601395872217409956197116803163639796644288113844556227070341937473024656774770038850992653377074558704010980494077799983859540600698980794368,   box := { reLo := (288248184881830602673698110363609380739643621191275997732061013301528449401295077519838131088701453910672104507151937736865880961150088510863523 : Rat)/441048855527609348466899088110727392882550083984559467947461967811555862987116951359784742868197609554640384317292722999435083921024464327802880,            reHi := (151136140755761946462563454049665810507353502697162422649648863256066211086536112982192684094956144385244435851451481175620283052320330540089721 : Rat)/88209771105521869693379817622145478576510016796911893589492393562311172597423390271956948573639521910928076863458544599887016784204892865560576,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6677607412813983633982704468009520202194973496891474831187532073159234310279793837556006520055267401648430486756680555944116777585059114586751 : Rat)/25202791744434819912394233606327279593288576227689112454140683874946049313549540077701985306754149117408021960988155599967719081201397961588736, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C73_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C73_a1

namespace VerifiedLcalc.Certificates.Batch.C73_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 4, a6 := -3 },   conductor := 73,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, -1, 2, 0, 2, -3],   alphaLo := (674651885226100947929381470208 : Rat)/917405416576007747650146484375,   alphaHi := (5397215081808807583452231630848 : Rat)/7339243332608061885833740234375,   geometricUpper := (2158655939546911 : Rat)/4503599627370496,   tail := (6677607412813983633982704468009520202194973496891474831187532073159234310279793837556006520055267401648430486756680555944116777585059114586751 : Rat)/12601395872217409956197116803163639796644288113844556227070341937473024656774770038850992653377074558704010980494077799983859540600698980794368,   box := { reLo := (288248184881830602673698110363609380739643621191275997732061013301528449401295077519838131088701453910672104507151937736865880961150088510863523 : Rat)/441048855527609348466899088110727392882550083984559467947461967811555862987116951359784742868197609554640384317292722999435083921024464327802880,            reHi := (151136140755761946462563454049665810507353502697162422649648863256066211086536112982192684094956144385244435851451481175620283052320330540089721 : Rat)/88209771105521869693379817622145478576510016796911893589492393562311172597423390271956948573639521910928076863458544599887016784204892865560576,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6677607412813983633982704468009520202194973496891474831187532073159234310279793837556006520055267401648430486756680555944116777585059114586751 : Rat)/25202791744434819912394233606327279593288576227689112454140683874946049313549540077701985306754149117408021960988155599967719081201397961588736, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C73_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C73_a2

namespace VerifiedLcalc.Certificates.Batch.C75_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -208, a6 := -1256 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -2, 1, 2, 0, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (1744515691402284736806518925541987776851358986596935736488529875355364361890708673898279432406089024916982041778010529013525981564594295485587359 : Rat)/44513981076833567752202442592489917458193516361030585955705809638904138907816886836139345081662449732250362019944139303091301416795447844627546112,            reHi := (162170154952748138179249192098870096612407195864115977059800209746778985339196301316728670955170676087365217094077343890361842886869367373667754275 : Rat)/133541943230500703256607327777469752374580549083091757867117428916712416723450660508418035244987349196751086059832417909273904250386343533882638336,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_a1

namespace VerifiedLcalc.Certificates.Batch.C75_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 2, a6 := 4 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -2, 1, 2, 0, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (1744515691402284736806518925541987776851358986596935736488529875355364361890708673898279432406089024916982041778010529013525981564594295485587359 : Rat)/44513981076833567752202442592489917458193516361030585955705809638904138907816886836139345081662449732250362019944139303091301416795447844627546112,            reHi := (162170154952748138179249192098870096612407195864115977059800209746778985339196301316728670955170676087365217094077343890361842886869367373667754275 : Rat)/133541943230500703256607327777469752374580549083091757867117428916712416723450660508418035244987349196751086059832417909273904250386343533882638336,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_a2

namespace VerifiedLcalc.Certificates.Batch.C75_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -54001, a6 := -4834477 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b1

namespace VerifiedLcalc.Certificates.Batch.C75_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -3376, a6 := -75727 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b2

namespace VerifiedLcalc.Certificates.Batch.C75_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2751, a6 := -104477 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b3

namespace VerifiedLcalc.Certificates.Batch.C75_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2001, a6 := 34273 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b4

namespace VerifiedLcalc.Certificates.Batch.C75_b5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -251, a6 := -727 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b5

namespace VerifiedLcalc.Certificates.Batch.C75_b6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -126, a6 := 523 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b6

namespace VerifiedLcalc.Certificates.Batch.C75_b7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := 23 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b7.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b7

namespace VerifiedLcalc.Certificates.Batch.C75_b8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 874, a6 := -5227 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 1, -1, 0, 1, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (12687884428169459516766001480798371403398939167621567962739072767789947863992544538348223819885849628938518818932714952759822979970371060362717435 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            reHi := (35107399839389638830918799585837913790212987608243582229138512802191978190066724302868101157430293635973105485195038916787783987205066477750638341 : Rat)/19077420461500100465229618253924250339225792726155965409588204130958916674778665786916862177855335599535869437118916844181986321483763361983234048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_b8.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_b8

namespace VerifiedLcalc.Certificates.Batch.C75_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -8, a6 := -7 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 2, -1, 2, 0, -2, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (108780308561020666534292315919968250156827185252491262203436806697917501704156218751584182098935799689876874770768323753386868264708673750802898653 : Rat)/133541943230500703256607327777469752374580549083091757867117428916712416723450660508418035244987349196751086059832417909273904250386343533882638336,            reHi := (88572305479853983501040650414070794479560101385605477351257142272876797985893464682206004918962736234163715246503878685569377735628086079337963617 : Rat)/44513981076833567752202442592489917458193516361030585955705809638904138907816886836139345081662449732250362019944139303091301416795447844627546112,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_c1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_c1

namespace VerifiedLcalc.Certificates.Batch.C75_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 42, a6 := 443 },   conductor := 75,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 2, -1, 2, 0, -2, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7439101573518717288970947265625,   alphaHi := (674651885226100947931528953856 : Rat)/929887696689839649200439453125,   geometricUpper := (4360141142947895 : Rat)/9007199254740992,   tail := (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/6359140153833366821743206084641416779741930908718655136529401376986305558259555262305620725951778533178623145706305614727328773827921120661078016,   box := { reLo := (108780308561020666534292315919968250156827185252491262203436806697917501704156218751584182098935799689876874770768323753386868264708673750802898653 : Rat)/133541943230500703256607327777469752374580549083091757867117428916712416723450660508418035244987349196751086059832417909273904250386343533882638336,            reHi := (88572305479853983501040650414070794479560101385605477351257142272876797985893464682206004918962736234163715246503878685569377735628086079337963617 : Rat)/44513981076833567752202442592489917458193516361030585955705809638904138907816886836139345081662449732250362019944139303091301416795447844627546112,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3736585901870028032425381421413602458976420007324346540218998684226906037808570075851609871601065861405103553570158485852401592037519641521484375 : Rat)/12718280307666733643486412169282833559483861817437310273058802753972611116519110524611241451903557066357246291412611229454657547655842241322156032, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C75_c2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C75_c2

namespace VerifiedLcalc.Certificates.Batch.C76_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -21, a6 := -31 },   conductor := 76,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 2, 0, -1, 0, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7488531363630457401275634765625,   alphaHi := (674651885226100947931528953856 : Rat)/936066420453807163238525390625,   geometricUpper := (1095267942301351 : Rat)/2251799813685248,   tail := (14881730145583853665541207017526948880653841454731212774328065439194438202806772305554129750036975454112454051417411197524674480577203632711 : Rat)/24085240613828733435055221824957256330376408227009892683432067685557647346026986201964643577668481739062704029308169588179899347008921534464,   box := { reLo := (1244080709920553965645709340763372924797124081432780807678272531341539080841989298434018338553659835954892821064780029219478359129941799786721 : Rat)/2528950264452017010680798291620511914689522863836038731760367106983552971332833551206287575655190582601583923077357806758889431435936761118720,            reHi := (873848808098632904855363468065334529718443853859594495862310135325271836925378847598213566909723747386668750173566233438304132433927924418515 : Rat)/505790052890403402136159658324102382937904572767207746352073421396710594266566710241257515131038116520316784615471561351777886287187352223744,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (14881730145583853665541207017526948880653841454731212774328065439194438202806772305554129750036975454112454051417411197524674480577203632711 : Rat)/48170481227657466870110443649914512660752816454019785366864135371115294692053972403929287155336963478125408058616339176359798694017843068928, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C76_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C76_a1

namespace VerifiedLcalc.Certificates.Batch.C77_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -89, a6 := 295 },   conductor := 77,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, -2, 3, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   geometricUpper := (4401690867433333 : Rat)/9007199254740992,   tail := (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/6269137292989739078739142030334497616375733972113960202178429247189602017354677661756256453500239462492838490668873202439211681201176434878447616,   box := { reLo := (36143139892918528033952980729911690365476630653303662940977073189497381894696065679848228480335086376502424530826057679024814267938909560296839461 : Rat)/94037059394846086181087130455017464245636009581709403032676438707844030260320164926343846802503591937392577360033098036588175218017646523176714240,            reHi := (73840432560561552128653247333222506067334449461127713129867529022560107560016131008674680729449878363011540063478826714016526609191676054265979699 : Rat)/43883961050928173551173994212341483314630137804797721415249004730327214121482743632293795174501676237449869434682112417074481768408235044149133312,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/12538274585979478157478284060668995232751467944227920404356858494379204034709355323512512907000478924985676981337746404878423362402352869756895232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C77_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C77_b1

namespace VerifiedLcalc.Certificates.Batch.C77_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -49, a6 := 600 },   conductor := 77,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, -2, 3, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   geometricUpper := (4401690867433333 : Rat)/9007199254740992,   tail := (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/6269137292989739078739142030334497616375733972113960202178429247189602017354677661756256453500239462492838490668873202439211681201176434878447616,   box := { reLo := (36143139892918528033952980729911690365476630653303662940977073189497381894696065679848228480335086376502424530826057679024814267938909560296839461 : Rat)/94037059394846086181087130455017464245636009581709403032676438707844030260320164926343846802503591937392577360033098036588175218017646523176714240,            reHi := (73840432560561552128653247333222506067334449461127713129867529022560107560016131008674680729449878363011540063478826714016526609191676054265979699 : Rat)/43883961050928173551173994212341483314630137804797721415249004730327214121482743632293795174501676237449869434682112417074481768408235044149133312,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/12538274585979478157478284060668995232751467944227920404356858494379204034709355323512512907000478924985676981337746404878423362402352869756895232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C77_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C77_b2

namespace VerifiedLcalc.Certificates.Batch.C77_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 441, a6 := -15815 },   conductor := 77,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, -2, 3, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   geometricUpper := (4401690867433333 : Rat)/9007199254740992,   tail := (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/6269137292989739078739142030334497616375733972113960202178429247189602017354677661756256453500239462492838490668873202439211681201176434878447616,   box := { reLo := (36143139892918528033952980729911690365476630653303662940977073189497381894696065679848228480335086376502424530826057679024814267938909560296839461 : Rat)/94037059394846086181087130455017464245636009581709403032676438707844030260320164926343846802503591937392577360033098036588175218017646523176714240,            reHi := (73840432560561552128653247333222506067334449461127713129867529022560107560016131008674680729449878363011540063478826714016526609191676054265979699 : Rat)/43883961050928173551173994212341483314630137804797721415249004730327214121482743632293795174501676237449869434682112417074481768408235044149133312,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/12538274585979478157478284060668995232751467944227920404356858494379204034709355323512512907000478924985676981337746404878423362402352869756895232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C77_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C77_b3

namespace VerifiedLcalc.Certificates.Batch.C77_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -51, a6 := 110 },   conductor := 77,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -2, 2, -1, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   geometricUpper := (4401690867433333 : Rat)/9007199254740992,   tail := (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/6269137292989739078739142030334497616375733972113960202178429247189602017354677661756256453500239462492838490668873202439211681201176434878447616,   box := { reLo := (29690957247898287760869602320069306433478575101044516500760861018447745181924459030129098661067120432434823767338363725001799004125548786611330253 : Rat)/43883961050928173551173994212341483314630137804797721415249004730327214121482743632293795174501676237449869434682112417074481768408235044149133312,            reHi := (185709838268066872912482621936002408159452192578502885907502833056299860436917779193130060225038187197184578653889090867596384164886806191553767131 : Rat)/94037059394846086181087130455017464245636009581709403032676438707844030260320164926343846802503591937392577360033098036588175218017646523176714240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/12538274585979478157478284060668995232751467944227920404356858494379204034709355323512512907000478924985676981337746404878423362402352869756895232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C77_c1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C77_c1

namespace VerifiedLcalc.Certificates.Batch.C77_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 4, a6 := 11 },   conductor := 77,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -2, 2, -1, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/1884409253370691967010498046875,   alphaHi := (5397215081808807583452231630848 : Rat)/7537637013482767772674560546875,   geometricUpper := (4401690867433333 : Rat)/9007199254740992,   tail := (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/6269137292989739078739142030334497616375733972113960202178429247189602017354677661756256453500239462492838490668873202439211681201176434878447616,   box := { reLo := (29690957247898287760869602320069306433478575101044516500760861018447745181924459030129098661067120432434823767338363725001799004125548786611330253 : Rat)/43883961050928173551173994212341483314630137804797721415249004730327214121482743632293795174501676237449869434682112417074481768408235044149133312,            reHi := (185709838268066872912482621936002408159452192578502885907502833056299860436917779193130060225038187197184578653889090867596384164886806191553767131 : Rat)/94037059394846086181087130455017464245636009581709403032676438707844030260320164926343846802503591937392577360033098036588175218017646523176714240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4069545281704729335369234229276761314325434715479190826364988384435361531028856548772485083125958104792078745473295287888109840921365071140233333 : Rat)/12538274585979478157478284060668995232751467944227920404356858494379204034709355323512512907000478924985676981337746404878423362402352869756895232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C77_c2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C77_c2

namespace VerifiedLcalc.Certificates.Batch.C78_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -20739, a6 := 1140957 },   conductor := 78,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, -1, 1, 2, 1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/7586424817394146060943603515625,   alphaHi := (674651885226100947931528953856 : Rat)/948303102174268245697021484375,   geometricUpper := (4422006411337489 : Rat)/9007199254740992,   tail := (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/6225130814159556108870154752672974655275861961070314230993675011572071985090900344438230178819427580303515183084237801390880492888863765289762816,   box := { reLo := (5768371176766074872935248917965640734951910008959037974563050915814518179362526343404172082579587198506532466711953904842341239740701111561007355 : Rat)/130727747097350678286273249806132467760793101182476598850867175243013511686908907233202833755207979186373818844768993829208490350666139071085019136,            reHi := (131372554297105388848964125897979916848575743458414704380750485949019032151455013976282070730913459395662338760197433443370037499921144877946246111 : Rat)/93376962212393341633052321290094619829137929416054713464905125173581079776363505166573452682291413704552727746263567020863207393332956479346442240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/12450261628319112217740309505345949310551723922140628461987350023144143970181800688876460357638855160607030366168475602781760985777727530579525632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C78_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C78_a1

namespace VerifiedLcalc.Certificates.Batch.C78_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2339, a6 := -15747 },   conductor := 78,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, -1, 1, 2, 1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/7586424817394146060943603515625,   alphaHi := (674651885226100947931528953856 : Rat)/948303102174268245697021484375,   geometricUpper := (4422006411337489 : Rat)/9007199254740992,   tail := (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/6225130814159556108870154752672974655275861961070314230993675011572071985090900344438230178819427580303515183084237801390880492888863765289762816,   box := { reLo := (5768371176766074872935248917965640734951910008959037974563050915814518179362526343404172082579587198506532466711953904842341239740701111561007355 : Rat)/130727747097350678286273249806132467760793101182476598850867175243013511686908907233202833755207979186373818844768993829208490350666139071085019136,            reHi := (131372554297105388848964125897979916848575743458414704380750485949019032151455013976282070730913459395662338760197433443370037499921144877946246111 : Rat)/93376962212393341633052321290094619829137929416054713464905125173581079776363505166573452682291413704552727746263567020863207393332956479346442240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/12450261628319112217740309505345949310551723922140628461987350023144143970181800688876460357638855160607030366168475602781760985777727530579525632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C78_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C78_a2

namespace VerifiedLcalc.Certificates.Batch.C78_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1299, a6 := 17325 },   conductor := 78,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, -1, 1, 2, 1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/7586424817394146060943603515625,   alphaHi := (674651885226100947931528953856 : Rat)/948303102174268245697021484375,   geometricUpper := (4422006411337489 : Rat)/9007199254740992,   tail := (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/6225130814159556108870154752672974655275861961070314230993675011572071985090900344438230178819427580303515183084237801390880492888863765289762816,   box := { reLo := (5768371176766074872935248917965640734951910008959037974563050915814518179362526343404172082579587198506532466711953904842341239740701111561007355 : Rat)/130727747097350678286273249806132467760793101182476598850867175243013511686908907233202833755207979186373818844768993829208490350666139071085019136,            reHi := (131372554297105388848964125897979916848575743458414704380750485949019032151455013976282070730913459395662338760197433443370037499921144877946246111 : Rat)/93376962212393341633052321290094619829137929416054713464905125173581079776363505166573452682291413704552727746263567020863207393332956479346442240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/12450261628319112217740309505345949310551723922140628461987350023144143970181800688876460357638855160607030366168475602781760985777727530579525632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C78_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C78_a3

namespace VerifiedLcalc.Certificates.Batch.C78_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -19, a6 := 685 },   conductor := 78,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -1, -1, 1, 2, 1, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/7586424817394146060943603515625,   alphaHi := (674651885226100947931528953856 : Rat)/948303102174268245697021484375,   geometricUpper := (4422006411337489 : Rat)/9007199254740992,   tail := (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/6225130814159556108870154752672974655275861961070314230993675011572071985090900344438230178819427580303515183084237801390880492888863765289762816,   box := { reLo := (5768371176766074872935248917965640734951910008959037974563050915814518179362526343404172082579587198506532466711953904842341239740701111561007355 : Rat)/130727747097350678286273249806132467760793101182476598850867175243013511686908907233202833755207979186373818844768993829208490350666139071085019136,            reHi := (131372554297105388848964125897979916848575743458414704380750485949019032151455013976282070730913459395662338760197433443370037499921144877946246111 : Rat)/93376962212393341633052321290094619829137929416054713464905125173581079776363505166573452682291413704552727746263567020863207393332956479346442240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4241742972361460555955550427016090252446306227317123039785515287535586860319590318260026634803601068683055005428059591796591620009549175496236849 : Rat)/12450261628319112217740309505345949310551723922140628461987350023144143970181800688876460357638855160607030366168475602781760985777727530579525632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C78_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C78_a4

namespace VerifiedLcalc.Certificates.Batch.C80_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := 426 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (56316860317537697420379636826992267209498168108723102269423948352381612673329353487320987588064609405916493143719408729694660873566901691514811289 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            reHi := (378143182976986264661684865802771272654942842012310250889100113023461879155311090294814019412135706578712489794297768313846648056262839626984393831 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_a1

namespace VerifiedLcalc.Certificates.Batch.C80_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := 6 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (56316860317537697420379636826992267209498168108723102269423948352381612673329353487320987588064609405916493143719408729694660873566901691514811289 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            reHi := (378143182976986264661684865802771272654942842012310250889100113023461879155311090294814019412135706578712489794297768313846648056262839626984393831 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_a2

namespace VerifiedLcalc.Certificates.Batch.C80_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := -1 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (56316860317537697420379636826992267209498168108723102269423948352381612673329353487320987588064609405916493143719408729694660873566901691514811289 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            reHi := (378143182976986264661684865802771272654942842012310250889100113023461879155311090294814019412135706578712489794297768313846648056262839626984393831 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_a3

namespace VerifiedLcalc.Certificates.Batch.C80_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := 34 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 0, 0, 1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (56316860317537697420379636826992267209498168108723102269423948352381612673329353487320987588064609405916493143719408729694660873566901691514811289 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            reHi := (378143182976986264661684865802771272654942842012310250889100113023461879155311090294814019412135706578712489794297768313846648056262839626984393831 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_a4

namespace VerifiedLcalc.Certificates.Batch.C80_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -41, a6 := 116 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 2, 0, -1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (249949741855147363606983151358539869655799871765326656193135221636197147675626929726698485089972895743967197153707633086582391186456857797358836427 : Rat)/644597572543666848942956933217761677248079750610156233199655840656071398744443433828037399090608239436498861854793009303422365801827828758143303680,            reHi := (405142903277831039952129877027700409587741418476490995141659173703447868820579498276391322933055167427351102728126162437550807979989844899281046631 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_b1

namespace VerifiedLcalc.Certificates.Batch.C80_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := 140 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 2, 0, -1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (249949741855147363606983151358539869655799871765326656193135221636197147675626929726698485089972895743967197153707633086582391186456857797358836427 : Rat)/644597572543666848942956933217761677248079750610156233199655840656071398744443433828037399090608239436498861854793009303422365801827828758143303680,            reHi := (405142903277831039952129877027700409587741418476490995141659173703447868820579498276391322933055167427351102728126162437550807979989844899281046631 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_b2

namespace VerifiedLcalc.Certificates.Batch.C80_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 0 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 2, 0, -1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (249949741855147363606983151358539869655799871765326656193135221636197147675626929726698485089972895743967197153707633086582391186456857797358836427 : Rat)/644597572543666848942956933217761677248079750610156233199655840656071398744443433828037399090608239436498861854793009303422365801827828758143303680,            reHi := (405142903277831039952129877027700409587741418476490995141659173703447868820579498276391322933055167427351102728126162437550807979989844899281046631 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_b3

namespace VerifiedLcalc.Certificates.Batch.C80_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := -4 },   conductor := 80,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 2, 0, -1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/7683071067995568561553955078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1920767766998892116546630859375,   geometricUpper := (4461757299020077 : Rat)/9007199254740992,   tail := (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/6139024500415874751837685078264396926172188101049106982853865149105441892804223179314641896101030851776179636712314374318308245731693607220412416,   box := { reLo := (249949741855147363606983151358539869655799871765326656193135221636197147675626929726698485089972895743967197153707633086582391186456857797358836427 : Rat)/644597572543666848942956933217761677248079750610156233199655840656071398744443433828037399090608239436498861854793009303422365801827828758143303680,            reHi := (405142903277831039952129877027700409587741418476490995141659173703447868820579498276391322933055167427351102728126162437550807979989844899281046631 : Rat)/214865857514555616314318977739253892416026583536718744399885280218690466248147811276012466363536079812166287284931003101140788600609276252714434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (4597518895134978324668492859144018202146494469654865419883068088666807064353198386478551857953616555603770128260398680000716811632677144852178157 : Rat)/12278049000831749503675370156528793852344376202098213965707730298210883785608446358629283792202061703552359273424628748636616491463387214440824832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C80_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C80_b4

namespace VerifiedLcalc.Certificates.Batch.C84_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := -72 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, -1, 0, 4, 0, -1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (1758673847521789765840080460824640894522335347385786989386721932755495769306753133853009318593662466223245780042130978279040748517093273607893587 : Rat)/23232255144318827340503951317634133910130938444182606460692296200054586090058432186936178533397274282322562626566667595954431174800931653775523840,            reHi := (18601108843656549121743793372456760109479440680341063534838057265247307113081605300914788825435334972479247679845505103178359362596569424296922881 : Rat)/9956680776136640288787407707557485961484687904649688483153841228594822610025042365829790800027403263852526839957143255409041932057542137332367360,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_a1

namespace VerifiedLcalc.Certificates.Batch.C84_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := -2 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, -1, 0, 4, 0, -1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (1758673847521789765840080460824640894522335347385786989386721932755495769306753133853009318593662466223245780042130978279040748517093273607893587 : Rat)/23232255144318827340503951317634133910130938444182606460692296200054586090058432186936178533397274282322562626566667595954431174800931653775523840,            reHi := (18601108843656549121743793372456760109479440680341063534838057265247307113081605300914788825435334972479247679845505103178359362596569424296922881 : Rat)/9956680776136640288787407707557485961484687904649688483153841228594822610025042365829790800027403263852526839957143255409041932057542137332367360,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_a2

namespace VerifiedLcalc.Certificates.Batch.C84_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1828, a6 := -30700 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, 0, 0, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (396236747563201987863506640435982569741600015452921411012032432802007772702599474671672814962742160715824094592076335109646197108447043613519923 : Rat)/1991336155227328057757481541511497192296937580929937696630768245718964522005008473165958160005480652770505367991428651081808386411508427466473472,            reHi := (9253335101849502116618429903284148672420799209659431499203513877534679711598958639067974086940514886748842314519122341219137172533047051753246601 : Rat)/4646451028863765468100790263526826782026187688836521292138459240010917218011686437387235706679454856464512525313333519190886234960186330755104768,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_b1

namespace VerifiedLcalc.Certificates.Batch.C84_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -113, a6 := -516 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, 0, 0, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (396236747563201987863506640435982569741600015452921411012032432802007772702599474671672814962742160715824094592076335109646197108447043613519923 : Rat)/1991336155227328057757481541511497192296937580929937696630768245718964522005008473165958160005480652770505367991428651081808386411508427466473472,            reHi := (9253335101849502116618429903284148672420799209659431499203513877534679711598958639067974086940514886748842314519122341219137172533047051753246601 : Rat)/4646451028863765468100790263526826782026187688836521292138459240010917218011686437387235706679454856464512525313333519190886234960186330755104768,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_b2

namespace VerifiedLcalc.Certificates.Batch.C84_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := -28 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, 0, 0, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (396236747563201987863506640435982569741600015452921411012032432802007772702599474671672814962742160715824094592076335109646197108447043613519923 : Rat)/1991336155227328057757481541511497192296937580929937696630768245718964522005008473165958160005480652770505367991428651081808386411508427466473472,            reHi := (9253335101849502116618429903284148672420799209659431499203513877534679711598958639067974086940514886748842314519122341219137172533047051753246601 : Rat)/4646451028863765468100790263526826782026187688836521292138459240010917218011686437387235706679454856464512525313333519190886234960186330755104768,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_b3

namespace VerifiedLcalc.Certificates.Batch.C84_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 7, a6 := 0 },   conductor := 84,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 0, 1, 0, 0, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/7872805096511921977996826171875,   geometricUpper := (4537936775034567 : Rat)/9007199254740992,   tail := (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/663778718409109352585827180503832397432312526976645898876922748572988174001669491055319386668493550923501789330476217027269462137169475822157824,   box := { reLo := (396236747563201987863506640435982569741600015452921411012032432802007772702599474671672814962742160715824094592076335109646197108447043613519923 : Rat)/1991336155227328057757481541511497192296937580929937696630768245718964522005008473165958160005480652770505367991428651081808386411508427466473472,            reHi := (9253335101849502116618429903284148672420799209659431499203513877534679711598958639067974086940514886748842314519122341219137172533047051753246601 : Rat)/4646451028863765468100790263526826782026187688836521292138459240010917218011686437387235706679454856464512525313333519190886234960186330755104768,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (594913049347763898545005459665174261942581693847108324380046872472729343699719921125428974841693703725039002252473684938490759630529146352250863 : Rat)/1327557436818218705171654361007664794864625053953291797753845497145976348003338982110638773336987101847003578660952434054538924274338951644315648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 3, 3, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C84_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C84_b4

namespace VerifiedLcalc.Certificates.Batch.C85_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -8, a6 := -13 },   conductor := 85,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -1, 2, -2, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7919528385618204021453857421875,   alphaHi := (2698607540904403791726115815424 : Rat)/3959764192809101963043212890625,   geometricUpper := (4556328028128923 : Rat)/9007199254740992,   tail := (5552708638569342173282245005661878248483561670436409410576933817131838408465917678089348035756197440823409261737819559333077696164797366792802843 : Rat)/5934170285922900938657499549933128382086842985295074676298777895855953591577902494672938222435390551756465655199500803693796618695073876846575616,   box := { reLo := (287611682348923591006326835785404992970043687309924306477134247654490181839556226682058078975574313378217498896086205434081406637037978253346722541 : Rat)/623087880021904598559037452742978480119118513455982841011371679064875127115679761940658513355716007934428893795947584387848644962982757068890439680,            reHi := (1453680496448486085303144999736888625142441182759809989248288488698260616980375697483511896072821478384045595260153261940961535968368513081837366547 : Rat)/623087880021904598559037452742978480119118513455982841011371679064875127115679761940658513355716007934428893795947584387848644962982757068890439680,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (5552708638569342173282245005661878248483561670436409410576933817131838408465917678089348035756197440823409261737819559333077696164797366792802843 : Rat)/11868340571845801877314999099866256764173685970590149352597555791711907183155804989345876444870781103512931310399001607387593237390147753693151232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C85_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C85_a1

namespace VerifiedLcalc.Certificates.Batch.C85_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3, a6 := -22 },   conductor := 85,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -1, 2, -2, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/7919528385618204021453857421875,   alphaHi := (2698607540904403791726115815424 : Rat)/3959764192809101963043212890625,   geometricUpper := (4556328028128923 : Rat)/9007199254740992,   tail := (5552708638569342173282245005661878248483561670436409410576933817131838408465917678089348035756197440823409261737819559333077696164797366792802843 : Rat)/5934170285922900938657499549933128382086842985295074676298777895855953591577902494672938222435390551756465655199500803693796618695073876846575616,   box := { reLo := (287611682348923591006326835785404992970043687309924306477134247654490181839556226682058078975574313378217498896086205434081406637037978253346722541 : Rat)/623087880021904598559037452742978480119118513455982841011371679064875127115679761940658513355716007934428893795947584387848644962982757068890439680,            reHi := (1453680496448486085303144999736888625142441182759809989248288488698260616980375697483511896072821478384045595260153261940961535968368513081837366547 : Rat)/623087880021904598559037452742978480119118513455982841011371679064875127115679761940658513355716007934428893795947584387848644962982757068890439680,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (5552708638569342173282245005661878248483561670436409410576933817131838408465917678089348035756197440823409261737819559333077696164797366792802843 : Rat)/11868340571845801877314999099866256764173685970590149352597555791711907183155804989345876444870781103512931310399001607387593237390147753693151232, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C85_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C85_a2

namespace VerifiedLcalc.Certificates.Batch.C89_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1, a6 := 0 },   conductor := 89,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -2, 2, 2, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/4051864043326417064666748046875,   alphaHi := (5397215081808807583452231630848 : Rat)/8103728086652834033966064453125,   geometricUpper := (1156864702436709 : Rat)/2251799813685248,   tail := (8116932158126401920154803537134097757208483677298252168354707474010777765253910904810715992434098070717610251944548204747866518122054487543 : Rat)/7349765105515917026460276464549851741126127628194628895919638215073579127073225528250950977585317279424439776575811044840893523271182450688,   box := { reLo := (245728199641777223426229190383800458242782899223865335151979487129173438863160233568233503960057304119845444704158719970277737239011990652337 : Rat)/771725336079171287778329028777734432818243400960436034071562012582725808342688680466349852646458314339566176540460159708293819943474157322240,            reHi := (1950283952848322451010457913086953804033052080198242060805176515084614172203078023606217812174382682005405327191413339112100613126189157497423 : Rat)/771725336079171287778329028777734432818243400960436034071562012582725808342688680466349852646458314339566176540460159708293819943474157322240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (8116932158126401920154803537134097757208483677298252168354707474010777765253910904810715992434098070717610251944548204747866518122054487543 : Rat)/14699530211031834052920552929099703482252255256389257791839276430147158254146451056501901955170634558848879553151622089681787046542364901376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C89_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C89_b1

namespace VerifiedLcalc.Certificates.Batch.C89_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 4, a6 := 5 },   conductor := 89,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 2, -1, -2, 2, 2, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/4051864043326417064666748046875,   alphaHi := (5397215081808807583452231630848 : Rat)/8103728086652834033966064453125,   geometricUpper := (1156864702436709 : Rat)/2251799813685248,   tail := (8116932158126401920154803537134097757208483677298252168354707474010777765253910904810715992434098070717610251944548204747866518122054487543 : Rat)/7349765105515917026460276464549851741126127628194628895919638215073579127073225528250950977585317279424439776575811044840893523271182450688,   box := { reLo := (245728199641777223426229190383800458242782899223865335151979487129173438863160233568233503960057304119845444704158719970277737239011990652337 : Rat)/771725336079171287778329028777734432818243400960436034071562012582725808342688680466349852646458314339566176540460159708293819943474157322240,            reHi := (1950283952848322451010457913086953804033052080198242060805176515084614172203078023606217812174382682005405327191413339112100613126189157497423 : Rat)/771725336079171287778329028777734432818243400960436034071562012582725808342688680466349852646458314339566176540460159708293819943474157322240,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (8116932158126401920154803537134097757208483677298252168354707474010777765253910904810715992434098070717610251944548204747866518122054487543 : Rat)/14699530211031834052920552929099703482252255256389257791839276430147158254146451056501901955170634558848879553151622089681787046542364901376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C89_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C89_b2

namespace VerifiedLcalc.Certificates.Batch.C90_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1149, a6 := -14707 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, -1, 0, 1, 1, 0, 2, -1, 0, -1, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/87237173352250009640053078979056134265393941059632878175850898057471808909553012573104262544782574253742332503862715487615199099523513729695000260657181397829323388253171419893301023489509555093499959845060608,   box := { reLo := (2036091307199837968180312659729592943506168485084256002590863582162344111547281894954289958618000911777859291448547876216512534169869702319074361836614643434335424696197392962571049271094355977765124548937587469 : Rat)/3053301067328750337401857764266964699288787937087150736154781432011513311834355440058649189067390098880981637635195042066531968483322980539325009123001348924026318588860999696265535822132834428272498594577121280,            reHi := (4670420157799815600641924711658525184975606469128534470024192745443168841599602412332627389221002812284301508537877738498291541946691121872103587742251773599402002023872540418298037445315003759903919484317034439 : Rat)/4798044534373750530202919343848087384596666758279808299671799393160949490025415691520734439963041583955828287712449351818835950473793255133225014336144976880612786353924428094131556291923025530142497791478333440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/174474346704500019280106157958112268530787882119265756351701796114943617819106025146208525089565148507484665007725430975230398199047027459390000521314362795658646776506342839786602046979019110186999919690121216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_a1

namespace VerifiedLcalc.Certificates.Batch.C90_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -69, a6 := -235 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, -1, 0, 1, 1, 0, 2, -1, 0, -1, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/87237173352250009640053078979056134265393941059632878175850898057471808909553012573104262544782574253742332503862715487615199099523513729695000260657181397829323388253171419893301023489509555093499959845060608,   box := { reLo := (2036091307199837968180312659729592943506168485084256002590863582162344111547281894954289958618000911777859291448547876216512534169869702319074361836614643434335424696197392962571049271094355977765124548937587469 : Rat)/3053301067328750337401857764266964699288787937087150736154781432011513311834355440058649189067390098880981637635195042066531968483322980539325009123001348924026318588860999696265535822132834428272498594577121280,            reHi := (4670420157799815600641924711658525184975606469128534470024192745443168841599602412332627389221002812284301508537877738498291541946691121872103587742251773599402002023872540418298037445315003759903919484317034439 : Rat)/4798044534373750530202919343848087384596666758279808299671799393160949490025415691520734439963041583955828287712449351818835950473793255133225014336144976880612786353924428094131556291923025530142497791478333440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/174474346704500019280106157958112268530787882119265756351701796114943617819106025146208525089565148507484665007725430975230398199047027459390000521314362795658646776506342839786602046979019110186999919690121216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_a2

namespace VerifiedLcalc.Certificates.Batch.C90_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := 18 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, -1, 0, 1, 1, 0, 2, -1, 0, -1, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/87237173352250009640053078979056134265393941059632878175850898057471808909553012573104262544782574253742332503862715487615199099523513729695000260657181397829323388253171419893301023489509555093499959845060608,   box := { reLo := (2036091307199837968180312659729592943506168485084256002590863582162344111547281894954289958618000911777859291448547876216512534169869702319074361836614643434335424696197392962571049271094355977765124548937587469 : Rat)/3053301067328750337401857764266964699288787937087150736154781432011513311834355440058649189067390098880981637635195042066531968483322980539325009123001348924026318588860999696265535822132834428272498594577121280,            reHi := (4670420157799815600641924711658525184975606469128534470024192745443168841599602412332627389221002812284301508537877738498291541946691121872103587742251773599402002023872540418298037445315003759903919484317034439 : Rat)/4798044534373750530202919343848087384596666758279808299671799393160949490025415691520734439963041583955828287712449351818835950473793255133225014336144976880612786353924428094131556291923025530142497791478333440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/174474346704500019280106157958112268530787882119265756351701796114943617819106025146208525089565148507484665007725430975230398199047027459390000521314362795658646776506342839786602046979019110186999919690121216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_a3

namespace VerifiedLcalc.Certificates.Batch.C90_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 6, a6 := 0 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, -1, 0, 1, 1, 0, 2, -1, 0, -1, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/87237173352250009640053078979056134265393941059632878175850898057471808909553012573104262544782574253742332503862715487615199099523513729695000260657181397829323388253171419893301023489509555093499959845060608,   box := { reLo := (2036091307199837968180312659729592943506168485084256002590863582162344111547281894954289958618000911777859291448547876216512534169869702319074361836614643434335424696197392962571049271094355977765124548937587469 : Rat)/3053301067328750337401857764266964699288787937087150736154781432011513311834355440058649189067390098880981637635195042066531968483322980539325009123001348924026318588860999696265535822132834428272498594577121280,            reHi := (4670420157799815600641924711658525184975606469128534470024192745443168841599602412332627389221002812284301508537877738498291541946691121872103587742251773599402002023872540418298037445315003759903919484317034439 : Rat)/4798044534373750530202919343848087384596666758279808299671799393160949490025415691520734439963041583955828287712449351818835950473793255133225014336144976880612786353924428094131556291923025530142497791478333440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (13371346396623971362387073315934097883541748997650629762114527984316113399733835768313019488641163874896197241984932711526659198546151463387379075379587754353038536619255601309282231666196739259568236718877937 : Rat)/174474346704500019280106157958112268530787882119265756351701796114943617819106025146208525089565148507484665007725430975230398199047027459390000521314362795658646776506342839786602046979019110186999919690121216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 3, 3, 3, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_a4

namespace VerifiedLcalc.Certificates.Batch.C90_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -218, a6 := -269 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (35274491215812498415609952002455830009738740088222336682437122538328756049563182215559481320419389493866088404702883450121060483876234672312331101 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            reHi := (71041023883559645561385674196609175635761407801666031884530706998690923068545768960000548491549630898957566887745462765177631153247986694243346309 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_b1

namespace VerifiedLcalc.Certificates.Batch.C90_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -128, a6 := 587 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (35274491215812498415609952002455830009738740088222336682437122538328756049563182215559481320419389493866088404702883450121060483876234672312331101 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            reHi := (71041023883559645561385674196609175635761407801666031884530706998690923068545768960000548491549630898957566887745462765177631153247986694243346309 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_b2

namespace VerifiedLcalc.Certificates.Batch.C90_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -8, a6 := 11 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (35274491215812498415609952002455830009738740088222336682437122538328756049563182215559481320419389493866088404702883450121060483876234672312331101 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            reHi := (71041023883559645561385674196609175635761407801666031884530706998690923068545768960000548491549630898957566887745462765177631153247986694243346309 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_b3

namespace VerifiedLcalc.Certificates.Batch.C90_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 52, a6 := -53 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, -1, 0, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (35274491215812498415609952002455830009738740088222336682437122538328756049563182215559481320419389493866088404702883450121060483876234672312331101 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            reHi := (71041023883559645561385674196609175635761407801666031884530706998690923068545768960000548491549630898957566887745462765177631153247986694243346309 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_b4

namespace VerifiedLcalc.Certificates.Batch.C90_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -48002, a6 := 4059929 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1, 0],                kodaira := -8 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c1

namespace VerifiedLcalc.Certificates.Batch.C90_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -4082, a6 := 14681 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c2

namespace VerifiedLcalc.Certificates.Batch.C90_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3002, a6 := 63929 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c3

namespace VerifiedLcalc.Certificates.Batch.C90_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2597, a6 := -50281 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1],                kodaira := -7 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c4

namespace VerifiedLcalc.Certificates.Batch.C90_c5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -617, a6 := 5231 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1, 0, 1, 2, 2, 1, 0, 2, 2, 1],                kodaira := -16 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c5

namespace VerifiedLcalc.Certificates.Batch.C90_c6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -167, a6 := -709 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2, 0, 2],                kodaira := -10 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c6

namespace VerifiedLcalc.Certificates.Batch.C90_c7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -122, a6 := 1721 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c7.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c7

namespace VerifiedLcalc.Certificates.Batch.C90_c8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 13, a6 := -61 },   conductor := 90,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 1, 0, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8149127478776754665374755859375,   alphaHi := (2698607540904403791726115815424 : Rat)/4074563739388377285003662109375,   geometricUpper := (4644660547044577 : Rat)/9007199254740992,   tail := (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/5742828959201973228611500836835716259292579778105317623011971106055622499669289662777710036352751533003590626966314373853562103947409170330812416,   box := { reLo := (5399524755375394681326457658870557098550228205307026495790245996692443063917115522482263848330101162102763957003280871576266006162201491415636091 : Rat)/28714144796009866143057504184178581296462898890526588115059855530278112498346448313888550181763757665017953134831571869267810519737045851654062080,            reHi := (499809349256732796035016844966211157161352185097940576775620208072689830176473016403809940482830508614089054710047600329391032287527134741043434659 : Rat)/200999013572069063001402529289250069075240292233686116805418988711946787488425138197219851272346303655125671943821003084874673638159320961578434560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (6600181085272926402964699217355499361398955125071109685084089828884902901503945037815115117176970499151957889273160465384635022585468828577718657 : Rat)/11485657918403946457223001673671432518585159556210635246023942212111244999338579325555420072705503066007181253932628747707124207894818340661624832, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 1],                kodaira := -7 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C90_c8.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C90_c8

namespace VerifiedLcalc.Certificates.Batch.C92_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -18, a6 := -43 },   conductor := 92,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 1, 0, 0, 0, 2, 0, -2, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8239175819901596736907958984375,   geometricUpper := (4678403051552249 : Rat)/9007199254740992,   tail := (14690705546713074187641874481374332500610022492181194808658815120396940881127868448567455796528886389367320303213536993416821136847524706200169487301382623583466394931193659767476902753046451283737489352155689 : Rat)/86294240791975130321518015325694454348171164229816973226600741419531768508827210807658462571549310065591354814465818217330659877311971042249009350022809577671391348924470609604024557875185719532576043111022592,   box := { reLo := (1751648492897744981568463444129060640351509153445604018930843697217364038458419138210899915964853404348174325529179819020409410124631509965269242779759421039679817120929390729969297802935795405384440396779254435 : Rat)/1812179056631477736751878321839583541311594448826156437758615569810167138685371426960827714002535511377418451103782182563943857423551391887229196350479001131099218327413882801684515715378900110184096905331474432,            reHi := (263184236206632804525844615770950466610231711075458357245396897637111785237936459566096772581596290638018823525074138063867830488974932292984230528650652169602641564099334714552319478912456031459703706000101301 : Rat)/201353228514608637416875369093287060145732716536239604195401729978907459853930158551203079333615056819713161233753575840438206380394599098581021816719889014566579814157098089076057301708766678909344100592386048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (14690705546713074187641874481374332500610022492181194808658815120396940881127868448567455796528886389367320303213536993416821136847524706200169487301382623583466394931193659767476902753046451283737489352155689 : Rat)/172588481583950260643036030651388908696342328459633946453201482839063537017654421615316925143098620131182709628931636434661319754623942084498018700045619155342782697848941219208049115750371439065152086222045184, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 23, 23, 23] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C92_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C92_b1

namespace VerifiedLcalc.Certificates.Batch.C92_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 1 },   conductor := 92,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 1, 0, 0, 0, 2, 0, -2, 0, 0, 0],   alphaLo := (674651885226100947929381470208 : Rat)/1029896977487699604034423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/8239175819901596736907958984375,   geometricUpper := (4678403051552249 : Rat)/9007199254740992,   tail := (14690705546713074187641874481374332500610022492181194808658815120396940881127868448567455796528886389367320303213536993416821136847524706200169487301382623583466394931193659767476902753046451283737489352155689 : Rat)/86294240791975130321518015325694454348171164229816973226600741419531768508827210807658462571549310065591354814465818217330659877311971042249009350022809577671391348924470609604024557875185719532576043111022592,   box := { reLo := (1751648492897744981568463444129060640351509153445604018930843697217364038458419138210899915964853404348174325529179819020409410124631509965269242779759421039679817120929390729969297802935795405384440396779254435 : Rat)/1812179056631477736751878321839583541311594448826156437758615569810167138685371426960827714002535511377418451103782182563943857423551391887229196350479001131099218327413882801684515715378900110184096905331474432,            reHi := (263184236206632804525844615770950466610231711075458357245396897637111785237936459566096772581596290638018823525074138063867830488974932292984230528650652169602641564099334714552319478912456031459703706000101301 : Rat)/201353228514608637416875369093287060145732716536239604195401729978907459853930158551203079333615056819713161233753575840438206380394599098581021816719889014566579814157098089076057301708766678909344100592386048,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (14690705546713074187641874481374332500610022492181194808658815120396940881127868448567455796528886389367320303213536993416821136847524706200169487301382623583466394931193659767476902753046451283737489352155689 : Rat)/172588481583950260643036030651388908696342328459633946453201482839063537017654421615316925143098620131182709628931636434661319754623942084498018700045619155342782697848941219208049115750371439065152086222045184, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 23] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C92_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C92_b2

namespace VerifiedLcalc.Certificates.Batch.C94_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -10, a6 := -9 },   conductor := 94,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 0, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8328250579632430553436279296875,   alphaHi := (2698607540904403791726115815424 : Rat)/4164125289816215229034423828125,   geometricUpper := (2355648149233061 : Rat)/4503599627370496,   tail := (14654258286288308753706659423667710514920051043227431452541260092191431774836199304773285199427712389437572147278401557338887256313292053976101 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,   box := { reLo := (200703722248486209299099391329113677913465327748162775771340968584488626059595174684967109066650849297564269155076470996763915975824742640603 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,            reHi := (29509220294825108269130468761777480638383420086221016680527996651559818075297720996922381628929548008946780491285710993556360994928662123025445 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (14654258286288308753706659423667710514920051043227431452541260092191431774836199304773285199427712389437572147278401557338887256313292053976101 : Rat)/21869086118368652049299911494809898469865593356102852007419713005635182654847016002625838609910911945276134245558487126113673363646985048948736, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C94_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C94_a1

namespace VerifiedLcalc.Certificates.Batch.C94_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := -1 },   conductor := 94,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, 1, 0, 1, 0, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/8328250579632430553436279296875,   alphaHi := (2698607540904403791726115815424 : Rat)/4164125289816215229034423828125,   geometricUpper := (2355648149233061 : Rat)/4503599627370496,   tail := (14654258286288308753706659423667710514920051043227431452541260092191431774836199304773285199427712389437572147278401557338887256313292053976101 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,   box := { reLo := (200703722248486209299099391329113677913465327748162775771340968584488626059595174684967109066650849297564269155076470996763915975824742640603 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,            reHi := (29509220294825108269130468761777480638383420086221016680527996651559818075297720996922381628929548008946780491285710993556360994928662123025445 : Rat)/10934543059184326024649955747404949234932796678051426003709856502817591327423508001312919304955455972638067122779243563056836681823492524474368,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (14654258286288308753706659423667710514920051043227431452541260092191431774836199304773285199427712389437572147278401557338887256313292053976101 : Rat)/21869086118368652049299911494809898469865593356102852007419713005635182654847016002625838609910911945276134245558487126113673363646985048948736, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C94_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C94_a2
