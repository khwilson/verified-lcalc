module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := -20 }
def label : String := "432.a1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := -20 },   conductor := 432,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -4, 0, 3, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 1, 0, 0, 0, 4, 0, 11, 0, 0, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   geometricUpper := (3328684231278565 : Rat)/4503599627370496,   tail := (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/433247702151533218870818065155732691259338009058562456152865413484712622538154710703138067591485867543382334460172641356236758382226223397426339277045580389746848870544397303240005944677017731254664705377739569548387683343407710080461556269702593281642215409530598417730835898310378165699699131902678654021075841630664602946119651595322193927400749481941964537589947487511341963348233800479775630849582329233774286893455030046131850780088819656519700359290164410413668990135226447201750859977080519863395960679649247232,   box := { reLo := (1976162260131982488672053079293700951977762916776281730272682362390682255956214580446748285618365553752273107988688729093310264882372763367166348291240335585790963639273562953506486144810706978282377951404450876451237117410207338917233485598647400112715609991061273228055960224997057263139432907125112077136741236286619614844738013541876400280347851136014778501951056986697704492679514592815094777361110707056549434417294296679358943028161910853261916036840256898983723318144234706299133124573052429051210598360362010823773884697 : Rat)/2496907226758843618037581502922184578684965460808151324115957515299398702254310155298555395551996385329569541302178560770791729697174633480652309941837110957412196439638541467335224979555641974917706125269295829313788980534743891901100904082589844192477237179152169307249969258038169074091437134710826158343553624923803195532057451309846426130643791753667356088336743593570022933998800772817713496425924720026229837044326894113967830547661968828872682587930243478185285307847791701992003433079088207766606164372777613256766259200,            reHi := (864886040671258537395784468740425413175913666770189331169840713109190636200649600116177581700664711716619229458273013351324439983802229601129111556938793971434666760843058521765462005141391468894193909009477906756255778882408227979521238456329933175659809164538551767426957664816941866675218689742452822034531294471396263929297013457305997710857889628945356263423585352560556565578491283030667707190843752956747221654793629077016457207014320973051606210643084837608379534142620798017165126927332311544414124283056324361699517179 : Rat)/499381445351768723607516300584436915736993092161630264823191503059879740450862031059711079110399277065913908260435712154158345939434926696130461988367422191482439287927708293467044995911128394983541225053859165862757796106948778380220180816517968838495447435830433861449993851607633814818287426942165231668710724984760639106411490261969285226128758350733471217667348718714004586799760154563542699285184944005245967408865378822793566109532393765774536517586048695637057061569558340398400686615817641553321232874555522651353251840,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/866495404303066437741636130311465382518676018117124912305730826969425245076309421406276135182971735086764668920345282712473516764452446794852678554091160779493697741088794606480011889354035462509329410755479139096775366686815420160923112539405186563284430819061196835461671796620756331399398263805357308042151683261329205892239303190644387854801498963883929075179894975022683926696467600959551261699164658467548573786910060092263701560177639313039400718580328820827337980270452894403501719954161039726791921359298494464, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -459, a6 := 3834 }
def label : String := "432.b1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := -1654 }
def label : String := "432.b2"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0],              kodaira := -17 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 21, a6 := 26 }
def label : String := "432.b3"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 0, 0],              kodaira := -11 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := 34 }
def label : String := "432.c1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := 34 },   conductor := 432,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -3, 0, 0, 0, -5, 0, 4, 0, 0, 0, -8, 0, -2, 0, 0, 0, -2, 0, -4, 0, 0, 0, 6, 0, 7,                    0, 0, 0, 3, 0, -6, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   finite := ((591280484968749 : Rat)/562949953421312, (21697707693942225 : Rat)/4503599627370496),   tail := (1275635764049368061632929494459056854248046875 : Rat)/1422774850378403160660169706366923160250482688,   box := { reLo := (14335372203370791686742621013943378692977760169161 : Rat)/93242972594399029537024881876462676230175633440768,            reHi := (4262652430850568717986168231128485523866343335370525 : Rat)/745943780755192236296199055011701409841405067526144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -4 }
def label : String := "432.d1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -4 },   conductor := 432,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 4, 0, 0,                    0, 0, 0, -1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   finite := ((9707472058959991 : Rat)/9007199254740992, (21859038120201525 : Rat)/4503599627370496),   tail := (1275635764049368061632929494459056854248046875 : Rat)/1422774850378403160660169706366923160250482688,   box := { reLo := (270274654376891737358071606565332800041035039618699 : Rat)/1491887561510384472592398110023402819682810135052288,            reHi := (4289374039801623180428828418443640883621313145298225 : Rat)/745943780755192236296199055011701409841405067526144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 108 }
def label : String := "432.d2"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 108 },   conductor := 432,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 4, 0, 0,                    0, 0, 0, -1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   finite := ((9707472058959991 : Rat)/9007199254740992, (21859038120201525 : Rat)/4503599627370496),   tail := (1275635764049368061632929494459056854248046875 : Rat)/1422774850378403160660169706366923160250482688,   box := { reLo := (270274654376891737358071606565332800041035039618699 : Rat)/1491887561510384472592398110023402819682810135052288,            reHi := (4289374039801623180428828418443640883621313145298225 : Rat)/745943780755192236296199055011701409841405067526144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4320, a6 := 109296 }
def label : String := "432.e1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1.nonsingular
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -480, a6 := -4048 }
def label : String := "432.e2"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2.nonsingular
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -16 }
def label : String := "432.e3"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3.nonsingular
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 432 }
def label : String := "432.e4"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4.nonsingular
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := -918 }
def label : String := "432.f1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := -918 },   conductor := 432,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 1, 0, -3, 0, 0, 0, 5, 0, 4, 0, 0, 0, 8, 0, -2, 0, 0, 0, 2, 0, -4, 0, 0, 0, -6, 0, 7, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   geometricUpper := (3328684231278565 : Rat)/4503599627370496,   tail := (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/433247702151533218870818065155732691259338009058562456152865413484712622538154710703138067591485867543382334460172641356236758382226223397426339277045580389746848870544397303240005944677017731254664705377739569548387683343407710080461556269702593281642215409530598417730835898310378165699699131902678654021075841630664602946119651595322193927400749481941964537589947487511341963348233800479775630849582329233774286893455030046131850780088819656519700359290164410413668990135226447201750859977080519863395960679649247232,   box := { reLo := (15098153694048971652254574455606068286921516341983209539985854838990984128169414160622450686145729237606085883579671197207031907734157145169970392069143986948194927706701706268726659555897616264590317190724971661370018098639758094002745961971070153479805086823924579453912029286229239362481366165328166239194570864344265867819092241021923659574558914344323086059176007385084007491049767925544369965336379771253782889311918697770745464343369710780812202006035104319290357291590796035945585816414753364485612116439705708552503839121 : Rat)/14482061915201292984617972716948670556372799672687277679872553588736512473074998900731621294201579034911503339552635652470592032243612874187783397662655243552990739349903540510544304881422723454522695526561915810019976087101514573026385243679021096316367975639082581982049821696621380629730335381322791718392611024558058534085933217597109271557733992171270665312353112842706133017193044482342738279270363376152133054857095985861013417176439419207461559009995412173474654785517191871553619911858711605046315753362110156889244303360,            reHi := (143590538823749854610724996310825850971461999265603293138706587827643820048923825192891746434428936376334670143392617063760585299881183054892965459914485688239546998669960310099683638680257898908374258827724801138647180983809065355959274305885386522524762995946191700510191253665177415462805178477055290157568791911469592878994003034290190775097130309810452294557177820035871591197105160064920627481080877669878802318977818538582246601642388271073950545970055653423515789362496717316142984337972270178175958255811268095458120601643 : Rat)/72410309576006464923089863584743352781863998363436388399362767943682562365374994503658106471007895174557516697763178262352960161218064370938916988313276217764953696749517702552721524407113617272613477632809579050099880435507572865131926218395105481581839878195412909910249108483106903148651676906613958591963055122790292670429666087985546357788669960856353326561765564213530665085965222411713691396351816880760665274285479929305067085882197096037307795049977060867373273927585959357768099559293558025231578766810550784446221516800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/866495404303066437741636130311465382518676018117124912305730826969425245076309421406276135182971735086764668920345282712473516764452446794852678554091160779493697741088794606480011889354035462509329410755479139096775366686815420160923112539405186563284430819061196835461671796620756331399398263805357308042151683261329205892239303190644387854801498963883929075179894975022683926696467600959551261699164658467548573786910060092263701560177639313039400718580328820827337980270452894403501719954161039726791921359298494464, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1971, a6 := 44658 }
def label : String := "432.g1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1],              kodaira := -17 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -51, a6 := -142 }
def label : String := "432.g2"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 189, a6 := -702 }
def label : String := "432.g3"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0, 0, 0, 1],              kodaira := -11 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := 540 }
def label : String := "432.h1"
def inputConductor : Nat := 432
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 432 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := 540 },   conductor := 432,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, 4, 0, 3, 0, 0, 0, -4, 0, 1, 0, 0, 0, -4, 0, 1, 0, 0, 0, -4, 0, 11, 0, 0, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17853843776444921398162841796875,   alphaHi := (2698607540904403791726115815424 : Rat)/8926921888222460651397705078125,   geometricUpper := (3328684231278565 : Rat)/4503599627370496,   tail := (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/433247702151533218870818065155732691259338009058562456152865413484712622538154710703138067591485867543382334460172641356236758382226223397426339277045580389746848870544397303240005944677017731254664705377739569548387683343407710080461556269702593281642215409530598417730835898310378165699699131902678654021075841630664602946119651595322193927400749481941964537589947487511341963348233800479775630849582329233774286893455030046131850780088819656519700359290164410413668990135226447201750859977080519863395960679649247232,   box := { reLo := (3592564266646419533638271630472630066646856451339452703770330157093117521510282458347149877187222372265281485297089662099633947656168272045386254384390443844201210240516957726562630740332344490493065373207601083838217883867083648385384696214152276668021106497105947278168477609790088318126579762827953666762029240085317190142518031679677629090014801795067753904641310933856996339260568947807689074234215339780370422010205675351623822976109911272087326573097027921923337648100826098360118052906855055303413475828485698513497461017 : Rat)/2496907226758843618037581502922184578684965460808151324115957515299398702254310155298555395551996385329569541302178560770791729697174633480652309941837110957412196439638541467335224979555641974917706125269295829313788980534743891901100904082589844192477237179152169307249969258038169074091437134710826158343553624923803195532057451309846426130643791753667356088336743593570022933998800772817713496425924720026229837044326894113967830547661968828872682587930243478185285307847791701992003433079088207766606164372777613256766259200,            reHi := (1188166441974145946389028178976211236109732373682823525869370272049677689311463175696257900014436075419220904919953199952589176538561331336773092775568815623116716081091737476376690924245718971336331393370107948233651932173783489873151480579430908486720908465747486577449461141775548077672648060883021139959588895231135778988853017084866243472791279760755951343961636141992414934894702154029186566565464679501511419173375904811469433196603921056816688317894439042196302400133939076429362112594092836794854699776681061899644232443 : Rat)/499381445351768723607516300584436915736993092161630264823191503059879740450862031059711079110399277065913908260435712154158345939434926696130461988367422191482439287927708293467044995911128394983541225053859165862757796106948778380220180816517968838495447435830433861449993851607633814818287426942165231668710724984760639106411490261969285226128758350733471217667348718714004586799760154563542699285184944005245967408865378822793566109532393765774536517586048695637057061569558340398400686615817641553321232874555522651353251840,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (203728372350996251535069620606762416231129529720976917532284197197046313236690345955383263329110867994054300286814640082573103318043763927722975913235464078754293176159828799963315931055374370908679126717161025795354223576298050832116478592348358914361729927870135718033408015463868136934742926286596167240221379124658944151735136965987975987801090714888516826602191919555655938543578931396459424079895451201262679493972749108236543798416207939050105110285892963258836893393996008208795113155212369747459888458251953125 : Rat)/866495404303066437741636130311465382518676018117124912305730826969425245076309421406276135182971735086764668920345282712473516764452446794852678554091160779493697741088794606480011889354035462509329410755479139096775366686815420160923112539405186563284430819061196835461671796620756331399398263805357308042151683261329205892239303190644387854801498963883929075179894975022683926696467600959551261699164658467548573786910060092263701560177639313039400718580328820827337980270452894403501719954161039726791921359298494464, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N432.C432_h1
