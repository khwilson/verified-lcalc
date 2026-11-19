module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -8211, a6 := -286610 }
def label : String := "441.a1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0],                kodaira := -17 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -8211, a6 := -286610 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -2, 0, 2, -2, 0, 0, 0, 0, 4, 2, 0, -1, 0, 0, -4, 0, 0, -1, -4, 0, -4, 0, 0, -1, 2, 0, 0, -4, 0,                    -9, 8, 0, 0, 0, 0, 3, 2, 0, 0, -10, 0, 5, 4, 0, 0, -6, 0, 0, 2, 0, -2, -12, 0, -4, 0, 0, 8, -12, 0,                    -10, 18, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((5706426872996239 : Rat)/4503599627370496, (4562095613128971 : Rat)/2251799813685248),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (231814672149759761232254992610383432560441525575241 : Rat)/743373050252898154344289336172574516120300996788224,            reHi := (1108078222785218996139284228176940936828523260616749 : Rat)/371686525126449077172144668086287258060150498394112,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -21, a6 := 40 }
def label : String := "441.a2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -21, a6 := 40 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -2, 0, 2, -2, 0, 0, 0, 0, 4, 2, 0, -1, 0, 0, -4, 0, 0, -1, -4, 0, -4, 0, 0, -1, 2, 0, 0, -4, 0,                    -9, 8, 0, 0, 0, 0, 3, 2, 0, 0, -10, 0, 5, 4, 0, 0, -6, 0, 0, 2, 0, -2, -12, 0, -4, 0, 0, 8, -12, 0,                    -10, 18, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((5706426872996239 : Rat)/4503599627370496, (4562095613128971 : Rat)/2251799813685248),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (231814672149759761232254992610383432560441525575241 : Rat)/743373050252898154344289336172574516120300996788224,            reHi := (1108078222785218996139284228176940936828523260616749 : Rat)/371686525126449077172144668086287258060150498394112,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -402339, a6 := 98307144 }
def label : String := "441.b1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 0, 1, 2, 1, 0, 1, 2, 1, 0, 1, 2],                kodaira := -17 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -402339, a6 := 98307144 },   conductor := 441,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -2, 0, 2, 2, 0, 0, 0, 0, -4, 2, 0, 1, 0, 0, -4, 0, 0, 1, 4, 0, -4, 0, 0, -1, -2, 0, 0, -4, 0, 9,                    8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   geometricUpper := (1669510572815151 : Rat)/2251799813685248,   tail := (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/167899626331939568536405541787707151619642223666747848666523974894631535595281829675395366776133726241826600653383509052585608324790374642503542126690027428712950493264048898600607803516438197726111883867042752996154322719870698937495394867521378794156672923429307613309773549459000214749719854693784319793934354347290415736981437563398556691279821816293059509369829939973722426952998171296847006361711305032001264149138562682761934800015304787575810751438075837446039696217205189579589878037084452834770944,   box := { reLo := (3189815081349804550164062103732573291918720344455493175452744719342066567174620306317858613223568162390914826316440893185203928617048945289313984086552428302188320178963252912555339868718844267489770693961858941720312229483538767465498233493404707124679780565034474349805823612203449337535366578934750839712505751978928878664112318518078741492205928457940528301436504308389174655916979610189435201736851426561624230836779335312106177299816568491533724542908490573565902466690966828958745865330898303670209052966807 : Rat)/10252719324618698678358976436911077438114014040264899010985603254251344502723256934350406029153726136123488592593586292304792823469786191635255735960922681672699118867209508772264210263414804057910988590790322218540140351301748285571107852042374299479189715483218211951025665143955328038600374295937694629880688926116691638552083267697968419966408525287663754389377183106770871169853378306019161283500197114474518594729882946333717374740644580348782163816996739831411499482632742589472084576636396351462832917708800,            reHi := (66953291903314372098140454573584960396332317223722634666694279973632163440949929141715398120366775455219488852562636473356179618424383427773931166958977210417601276104199863536810510247836967277155294096947842279598763176862543171530777464082794618989800034676327949251681230300364749810830446673081623908026530210780265056912255824582164672800523872502387979446382488630463070862488354008658062899918024050128830625685230971700248126686783142295941896391739459131064415446357323359785737751349571797020286626841 : Rat)/49056073323534443437124289171823337024468966699832052684141642364838968912551468585408641287816871464705687045902326757439200112295627711173472420865658763984206310369423486948632584992415330420626739668853216356651389240678221462062716995418058849182725911402957951918783086813183387744499398545156433635792769981419577217952551520085973301274681939175424662150130062711822350094992240698656274083733000547724969352774559551835968300194471676309962506301419807805796648242261926265416672615485150006999200563200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/335799252663879137072811083575414303239284447333495697333047949789263071190563659350790733552267452483653201306767018105171216649580749285007084253380054857425900986528097797201215607032876395452223767734085505992308645439741397874990789735042757588313345846858615226619547098918000429499439709387568639587868708694580831473962875126797113382559643632586119018739659879947444853905996342593694012723422610064002528298277125365523869600030609575151621502876151674892079392434410379159179756074168905669541888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1029, a6 := -13806 }
def label : String := "441.b2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1029, a6 := -13806 },   conductor := 441,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -2, 0, 2, 2, 0, 0, 0, 0, -4, 2, 0, 1, 0, 0, -4, 0, 0, 1, 4, 0, -4, 0, 0, -1, -2, 0, 0, -4, 0, 9,                    8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   geometricUpper := (1669510572815151 : Rat)/2251799813685248,   tail := (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/167899626331939568536405541787707151619642223666747848666523974894631535595281829675395366776133726241826600653383509052585608324790374642503542126690027428712950493264048898600607803516438197726111883867042752996154322719870698937495394867521378794156672923429307613309773549459000214749719854693784319793934354347290415736981437563398556691279821816293059509369829939973722426952998171296847006361711305032001264149138562682761934800015304787575810751438075837446039696217205189579589878037084452834770944,   box := { reLo := (3189815081349804550164062103732573291918720344455493175452744719342066567174620306317858613223568162390914826316440893185203928617048945289313984086552428302188320178963252912555339868718844267489770693961858941720312229483538767465498233493404707124679780565034474349805823612203449337535366578934750839712505751978928878664112318518078741492205928457940528301436504308389174655916979610189435201736851426561624230836779335312106177299816568491533724542908490573565902466690966828958745865330898303670209052966807 : Rat)/10252719324618698678358976436911077438114014040264899010985603254251344502723256934350406029153726136123488592593586292304792823469786191635255735960922681672699118867209508772264210263414804057910988590790322218540140351301748285571107852042374299479189715483218211951025665143955328038600374295937694629880688926116691638552083267697968419966408525287663754389377183106770871169853378306019161283500197114474518594729882946333717374740644580348782163816996739831411499482632742589472084576636396351462832917708800,            reHi := (66953291903314372098140454573584960396332317223722634666694279973632163440949929141715398120366775455219488852562636473356179618424383427773931166958977210417601276104199863536810510247836967277155294096947842279598763176862543171530777464082794618989800034676327949251681230300364749810830446673081623908026530210780265056912255824582164672800523872502387979446382488630463070862488354008658062899918024050128830625685230971700248126686783142295941896391739459131064415446357323359785737751349571797020286626841 : Rat)/49056073323534443437124289171823337024468966699832052684141642364838968912551468585408641287816871464705687045902326757439200112295627711173472420865658763984206310369423486948632584992415330420626739668853216356651389240678221462062716995418058849182725911402957951918783086813183387744499398545156433635792769981419577217952551520085973301274681939175424662150130062711822350094992240698656274083733000547724969352774559551835968300194471676309962506301419807805796648242261926265416672615485150006999200563200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/335799252663879137072811083575414303239284447333495697333047949789263071190563659350790733552267452483653201306767018105171216649580749285007084253380054857425900986528097797201215607032876395452223767734085505992308645439741397874990789735042757588313345846858615226619547098918000429499439709387568639587868708694580831473962875126797113382559643632586119018739659879947444853905996342593694012723422610064002528298277125365523869600030609575151621502876151674892079392434410379159179756074168905669541888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -16400, a6 := -804212 }
def label : String := "441.c1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -16400, a6 := -804212 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, -8, 0, -5, 0, 0, 0, -2, 0, 0,                    -5, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -12, 4, 0, 8, 0, 0, 0, 5, 0, 0, 10, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,                    7],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((206091044341035 : Rat)/140737488355328, (26917235308702913 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (11827188012705528168657886388505212189664467665165 : Rat)/23230407820403067323259041755392953628759406149632,            reHi := (5863210866780831340961128774116755604953911593654247 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -965, a6 := -13940 }
def label : String := "441.c2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -965, a6 := -13940 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, -8, 0, -5, 0, 0, 0, -2, 0, 0,                    -5, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -12, 4, 0, 8, 0, 0, 0, 5, 0, 0, 10, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,                    7],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((206091044341035 : Rat)/140737488355328, (26917235308702913 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (11827188012705528168657886388505212189664467665165 : Rat)/23230407820403067323259041755392953628759406149632,            reHi := (5863210866780831340961128774116755604953911593654247 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -335, a6 := 2440 }
def label : String := "441.c3"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -335, a6 := 2440 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, -8, 0, -5, 0, 0, 0, -2, 0, 0,                    -5, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -12, 4, 0, 8, 0, 0, 0, 5, 0, 0, 10, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,                    7],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((206091044341035 : Rat)/140737488355328, (26917235308702913 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (11827188012705528168657886388505212189664467665165 : Rat)/23230407820403067323259041755392953628759406149632,            reHi := (5863210866780831340961128774116755604953911593654247 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -20, a6 := 46 }
def label : String := "441.c4"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -20, a6 := 46 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 0, 3, 0, 0, -4, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, -8, 0, -5, 0, 0, 0, -2, 0, 0,                    -5, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -12, 4, 0, 8, 0, 0, 0, 5, 0, 0, 10, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,                    7],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((206091044341035 : Rat)/140737488355328, (26917235308702913 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (11827188012705528168657886388505212189664467665165 : Rat)/23230407820403067323259041755392953628759406149632,            reHi := (5863210866780831340961128774116755604953911593654247 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -331 }
def label : String := "441.d1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -331 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 4, 0, 0, -7, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -7, 0,                    0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((8828716483595823 : Rat)/4503599627370496, (33679265624632191 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (747185962594491687007319731634049438922240629242537 : Rat)/743373050252898154344289336172574516120300996788224,            reHi := (6979364947464474966149567155885258178073519434643929 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 12 }
def label : String := "441.d2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 12 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 4, 0, 0, -7, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -7, 0,                    0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((8828716483595823 : Rat)/4503599627370496, (33679265624632191 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (747185962594491687007319731634049438922240629242537 : Rat)/743373050252898154344289336172574516120300996788224,            reHi := (6979364947464474966149567155885258178073519434643929 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -4202 }
def label : String := "441.e1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -4202 },   conductor := 441,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 7, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 7, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   geometricUpper := (1669510572815151 : Rat)/2251799813685248,   tail := (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/167899626331939568536405541787707151619642223666747848666523974894631535595281829675395366776133726241826600653383509052585608324790374642503542126690027428712950493264048898600607803516438197726111883867042752996154322719870698937495394867521378794156672923429307613309773549459000214749719854693784319793934354347290415736981437563398556691279821816293059509369829939973722426952998171296847006361711305032001264149138562682761934800015304787575810751438075837446039696217205189579589878037084452834770944,   box := { reLo := (4385986304115632148409566393472552988950449732781248668677058432259102023025595830912171914375941221016046553804909251429784581164194815021725768088066343652601286771933993788959135548564445493391375024937429158575308092418349928499937669210472709208345023459463091927999196201000316850473827142827053162477324299922381333543008056750031318868777209865028186917244277997172672274707534365566685739291624754876696204311872999873441664968116858214544563539309327757635458916302768288356065445640539785477125728853 : Rat)/6428037194118306381416286167342368299758002533081441386197870378840968340265364849122511617024279709168331406014787644078240014714599493188248110320327700108275309634614112082924269757626836399944193473849731798457768245330249708822011192503055987134288222873491041975564680341037823221693024636951532683310776756186013566490334337114713742925647978236779783316223939251893963115895534988099787638558117313150168397949769872309540673818585943792339914618806733436621629769675700683054598480649778276779205591040,            reHi := (587331169163746181911854218786427887251235290407262838824834374934940322646818239781506046953361245348136528705006095144155941823515001065260857207860212844765637870376540152485254543057859369505771871578291559563344039123000043494125572124550450405118984977342526358405464237833612089461448229975210480765615424868726445870146174460066319331773845303747310528996382704599915705477157884806871826462477113595132738783516950746771022337153332997741939618862852461581307233583842128906117403001105650089969104649 : Rat)/338317747058858230600857166702229910513579080688496915063045809412682544224492886795921664053909458377280600316567770740960000774452604904644637385280405268856595243927058530680224724085622968418115445992091147287250960280539458359053220658055578270225695940710054840819193702159885432720685507207975404384777724009790187710017596690248091732928840959830514911380207329047050690310291315163146717818848279639482547260514203805765298622030839146965258664147722812453769987877668457002873604244725172462063452160,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/335799252663879137072811083575414303239284447333495697333047949789263071190563659350790733552267452483653201306767018105171216649580749285007084253380054857425900986528097797201215607032876395452223767734085505992308645439741397874990789735042757588313345846858615226619547098918000429499439709387568639587868708694580831473962875126797113382559643632586119018739659879947444853905996342593694012723422610064002528298277125365523869600030609575151621502876151674892079392434410379159179756074168905669541888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 113447 }
def label : String := "441.e2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 113447 },   conductor := 441,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 4, 0, 0, 7, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 7, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   geometricUpper := (1669510572815151 : Rat)/2251799813685248,   tail := (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/167899626331939568536405541787707151619642223666747848666523974894631535595281829675395366776133726241826600653383509052585608324790374642503542126690027428712950493264048898600607803516438197726111883867042752996154322719870698937495394867521378794156672923429307613309773549459000214749719854693784319793934354347290415736981437563398556691279821816293059509369829939973722426952998171296847006361711305032001264149138562682761934800015304787575810751438075837446039696217205189579589878037084452834770944,   box := { reLo := (4385986304115632148409566393472552988950449732781248668677058432259102023025595830912171914375941221016046553804909251429784581164194815021725768088066343652601286771933993788959135548564445493391375024937429158575308092418349928499937669210472709208345023459463091927999196201000316850473827142827053162477324299922381333543008056750031318868777209865028186917244277997172672274707534365566685739291624754876696204311872999873441664968116858214544563539309327757635458916302768288356065445640539785477125728853 : Rat)/6428037194118306381416286167342368299758002533081441386197870378840968340265364849122511617024279709168331406014787644078240014714599493188248110320327700108275309634614112082924269757626836399944193473849731798457768245330249708822011192503055987134288222873491041975564680341037823221693024636951532683310776756186013566490334337114713742925647978236779783316223939251893963115895534988099787638558117313150168397949769872309540673818585943792339914618806733436621629769675700683054598480649778276779205591040,            reHi := (587331169163746181911854218786427887251235290407262838824834374934940322646818239781506046953361245348136528705006095144155941823515001065260857207860212844765637870376540152485254543057859369505771871578291559563344039123000043494125572124550450405118984977342526358405464237833612089461448229975210480765615424868726445870146174460066319331773845303747310528996382704599915705477157884806871826462477113595132738783516950746771022337153332997741939618862852461581307233583842128906117403001105650089969104649 : Rat)/338317747058858230600857166702229910513579080688496915063045809412682544224492886795921664053909458377280600316567770740960000774452604904644637385280405268856595243927058530680224724085622968418115445992091147287250960280539458359053220658055578270225695940710054840819193702159885432720685507207975404384777724009790187710017596690248091732928840959830514911380207329047050690310291315163146717818848279639482547260514203805765298622030839146965258664147722812453769987877668457002873604244725172462063452160,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88459003656726387366445976270876201272836456117044445004910601144893815956579445879815088367559441464174211927240528126749470521791260021697039541562737768191294918963122168111558917275882531528895515602094646015293739771642741689562429287320875303343045213727498178335517712260556238334530061135683073895669140951239996019811580630431684000536089796641379265642134394938273643873794260139294989675686839115221603387319311601971639413285302167131160497272455676742707763364549517785038956562652179796344343 : Rat)/335799252663879137072811083575414303239284447333495697333047949789263071190563659350790733552267452483653201306767018105171216649580749285007084253380054857425900986528097797201215607032876395452223767734085505992308645439741397874990789735042757588313345846858615226619547098918000429499439709387568639587868708694580831473962875126797113382559643632586119018739659879947444853905996342593694012723422610064002528298277125365523869600030609575151621502876151674892079392434410379159179756074168905669541888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -345753, a6 := -78165914 }
def label : String := "441.f1"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -345753, a6 := -78165914 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -21618, a6 := -1216265 }
def label : String := "441.f2"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -21618, a6 := -1216265 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -17208, a6 := 867901 }
def label : String := "441.f3"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 2, 1, 0, 2, 0, 2],                kodaira := -12 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -17208, a6 := 867901 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15003, a6 := -1979636 }
def label : String := "441.f4"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15003, a6 := -1979636 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1773, a6 := -5720 }
def label : String := "441.f5"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 1, 0],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1773, a6 := -5720 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 432, a6 := -869 }
def label : String := "441.f6"
def inputConductor : Nat := 441
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 441 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 432, a6 := -869 },   conductor := 441,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, 0, -3, 0, -2, -4, 0, 2, 0, 0, -1, -6, 0, -4, 2, 0, -4, 0, 0, -1, 2, 0, 0, 2, 0,                    0, 5, 0, -6, 0, 0, 6, -4, 0, 6],   alphaLo := (5397215081808807583435051761664 : Rat)/18038862643200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/1050000000000000000000,   finite := ((2896773339010731 : Rat)/2251799813685248, (54218319381287797 : Rat)/9007199254740992),   tail := (1354407156290130148357554864906597137451171875 : Rat)/1417871571069523152054384872765683204880334848,   box := { reLo := (123097419625540720915052670121844910718579452898189 : Rat)/371686525126449077172144668086287258060150498394112,            reHi := (10369581730413254320784515525568182393056642963132243 : Rat)/1486746100505796308688578672345149032240601993576448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N441.C441_f6
