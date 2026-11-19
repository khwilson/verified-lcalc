module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -42, a6 := 110 }
def label : String := "357.a1"
def inputConductor : Nat := 357
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 357 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -42, a6 := 110 },   conductor := 357,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 1, 2, -3, -2, 1, 0, 1, 6, -3, 2, 1, -2, -3, -4, -1, -2, -7, -6, 1, 6, 1, 0, 4, -2, 1, 2, -10,                    6, 4, 8, -3, 2, -3, 2, -10, 14, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16230203491409847354888916015625,   alphaHi := (674651885226100947931528953856 : Rat)/2028775436426230907440185546875,   finite := ((5741608845765521 : Rat)/9007199254740992, (23833287257430523 : Rat)/9007199254740992),   tail := (142958242511643243461297014400844573974609375 : Rat)/291951313284236969324044005591677909673705472,   box := { reLo := (45240957694556659621846013053521855595666597021211 : Rat)/306133140278332064345928767207299255814015389007872,            reHi := (959938961325360759867125871959405155883057462341993 : Rat)/306133140278332064345928767207299255814015389007872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 3565, a6 := 72914 }
def label : String := "357.b1"
def inputConductor : Nat := 357
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 357 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 3565, a6 := 72914 },   conductor := 357,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, -1, -2, 1, 0, -1, 0, 1, 0, 3, 2, 3, 0, -1, 4, 1, 0, 3, -2, 1, 0, 7, 0, -4, 0, -1, 2, -6, 0, 10,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/16230203491409847354888916015625,   alphaHi := (674651885226100947931528953856 : Rat)/2028775436426230907440185546875,   geometricUpper := (6459053206200859 : Rat)/9007199254740992,   tail := (58645611862692819416677775618135363935750686750339787681004325827559236759046400708504190695799823646906222696671048667700323023033005138679015386004969133305463235338474070335461287839463014319798060212639602302369035614051854118582715519462282128155918623040322384833061786153444687320465610389976774682652667776770584533677024236688616767674282252283029644012899123563994523277111827441914082155495300418894672323457151409806556767382899688960640468282479050399843301424104134759861498670702132837401761373851164567954027569 : Rat)/375032763702894729570854535268335097760226595983672033354339953026777024297961298406872741463082514536800135822534278603828694483996742891633437284127207798648636339142929059870447155915787835510432806758008901074258044684837140736125122259955075660259231112851002118200147107182503914632710028395993282714514974810598529783190535387431346736376727186620709448420548100111154662405758853724214204147222977947154584563281673136430459075638629154799681360518690304042635113191121480931854878192533338742673544129642083627976097792,   box := { reLo := (1447983065178325079085361477557355935879332964261182721534706795503624636071164899894559925013042386167692188920838958455968239752455473501773088474122176002248375585546854730684011151217942564480713511632036194830366583164740835834457780302449842739902533773777789836080611476783762041960690922783646286130869501792174728562091163273991526112415172499337177183556845025217392555401382366993538378463556800581861864080389424505830813173399434993836097335369350297743895780329629927338189946849212647018286426057939520290337701275771155871803 : Rat)/1692376985318873414906798778517889811207131504482801930951202901188060482666995836285705666738383554363003416154406026348971738856039319402565902305026299470719899256279282018357332407586536089138945005165901433803007231781943512318463479142912173039563556984132702345977518188229054140786050050068499186461742554797860513669417169280807657721408076859663772971129809329734503447877507814344095974239685680548288856174986848223501312694597279636078464051752709564100566421163085433051445928757333535803408289037567012462780031944487442841600,            reHi := (659090911613440165385270005345584705801729347553763791764508289271482698902111619781582878434721262537870424062207487942881208080512474851920505179230552736916431498865477369614271066995465996112825060714256878061614931812669751831479848862554641073123039099253241477866206252051645560777657518623433475028277155514769588524040263035865750239447537016703264883493436015610534531634183678606618421337879955561395632150322589685213469137167995834408216780282474838971280198811660114177453061022941840961105897188830962807576345432609149911703 : Rat)/564125661772957804968932926172629937069043834827600643650400967062686827555665278761901888912794518121001138718135342116323912952013106467521967435008766490239966418759760672785777469195512029712981668388633811267669077260647837439487826380970724346521185661377567448659172729409684713595350016689499728820580851599286837889805723093602552573802692286554590990376603109911501149292502604781365324746561893516096285391662282741167104231532426545359488017250903188033522140387695144350481976252444511934469429679189004154260010648162480947200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (58645611862692819416677775618135363935750686750339787681004325827559236759046400708504190695799823646906222696671048667700323023033005138679015386004969133305463235338474070335461287839463014319798060212639602302369035614051854118582715519462282128155918623040322384833061786153444687320465610389976774682652667776770584533677024236688616767674282252283029644012899123563994523277111827441914082155495300418894672323457151409806556767382899688960640468282479050399843301424104134759861498670702132837401761373851164567954027569 : Rat)/750065527405789459141709070536670195520453191967344066708679906053554048595922596813745482926165029073600271645068557207657388967993485783266874568254415597297272678285858119740894311831575671020865613516017802148516089369674281472250244519910151320518462225702004236400294214365007829265420056791986565429029949621197059566381070774862693472753454373241418896841096200222309324811517707448428408294445955894309169126563346272860918151277258309599362721037380608085270226382242961863709756385066677485347088259284167255952195584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -5, a6 := -16 }
def label : String := "357.c1"
def inputConductor : Nat := 357
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 7, 7, 7, 7, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 357 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -5, a6 := -16 },   conductor := 357,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 1, 0, 1, 0, 1, 0, -5, 2, -5, 0, -1, 4, 1, 0, -5, -2, -1, 0, -1, 0, -4, 0, -1, -2, -6,                    0, -6, 0, 5, 0, 1, -2, 4, 0, 5, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16230203491409847354888916015625,   alphaHi := (674651885226100947931528953856 : Rat)/2028775436426230907440185546875,   finite := ((10754761014457089 : Rat)/9007199254740992, (29673499666393243 : Rat)/9007199254740992),   tail := (142958242511643243461297014400844573974609375 : Rat)/291951313284236969324044005591677909673705472,   box := { reLo := (215625998892228208646131516432685967919732855544299 : Rat)/306133140278332064345928767207299255814015389007872,            reHi := (1158433800185195857827275483923084047034164621565513 : Rat)/306133140278332064345928767207299255814015389007872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 20, a6 := -17 }
def label : String := "357.d1"
def inputConductor : Nat := 357
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 7, 7, 17, 17, 17] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 357 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 20, a6 := -17 },   conductor := 357,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 1, 2, 1, 2, -1, 0, 1, 2, 1, 2, 1, -2, 1, -4, -1, 2, 1, 2, -1, 2, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16230203491409847354888916015625,   alphaHi := (674651885226100947931528953856 : Rat)/2028775436426230907440185546875,   geometricUpper := (6459053206200859 : Rat)/9007199254740992,   tail := (70142555705680400039410339218491525033265127367241680321218044186097604340286349621572208897800060045980571291988480110585515311816577044470590700023103221383668247154561100743182624045222351035971105280107672943767659561481709315913281462135864180046734360193346969030551185269017839787576757392107406582734234981313361441883745264153351547627094416033006368471422231439392668099031843721070898046875 : Rat)/51355809692039246319129530908847532610420848850508952904545972752588993958046676291675532075337689276098448881923907669737452070172871607915308898077506425395172590455979574111676943338416309608253147814083415097646113469316273521441492824009767799507222951583395874214391362337034884258240284207094208137445007307092051396160868174787065650607032989135369865830086057993953724089995661609057772371968,   box := { reLo := (146400973549206952105100868018603148179997266980093126161991698983132771285330658711351001834254330926320722748692269404818595269346567553685702364807359892853130251854273212273462448879734513756903342920730124469912417778204158613173869740929965329001334664181342410484045330476100247759511529621708620474781824416850348339278894698090188621603926274201692412380239992589822023888999772651809287102214892989 : Rat)/82228097909360179047642652767046682601512290032748157398349261542944104730956645511034819804766564495978650935048055145861772694896942510655557265612309025489353617345639415191040979441588582047706486356780589666520586350828404767488439027699119663341992492812996387019001657849131719755660139856767855888229386224713902632705993273719436231141197835389151783824513141326729035558076103607034806944514703360,            reHi := (453466173428828210031036510518665791374532940110215012335721718699883556551988647256197896782217259438528076358196037072920142451628230195186739721105152608349717389357213995413172215426531073788590963891614491131703167604283370899540438005989619898419320123578051824825740136268338841395328319259939346755451555950257768440006040347226509708024116584852177948830252607051669264981313603383235197709558188057 : Rat)/100501008555884663280452131159723723179626132262247747931315764108042794671169233402375890872492467717307240031725400733831055515985151957467903324637266586709209976755781507455716752650830489169419038880509609592414049984345828049152536589410035144084657491215884473023224248482272101923584615380494046085613694274650325439973991778990422060283686243253407735785516061621557710126537459964153652932184637440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (70142555705680400039410339218491525033265127367241680321218044186097604340286349621572208897800060045980571291988480110585515311816577044470590700023103221383668247154561100743182624045222351035971105280107672943767659561481709315913281462135864180046734360193346969030551185269017839787576757392107406582734234981313361441883745264153351547627094416033006368471422231439392668099031843721070898046875 : Rat)/102711619384078492638259061817695065220841697701017905809091945505177987916093352583351064150675378552196897763847815339474904140345743215830617796155012850790345180911959148223353886676832619216506295628166830195292226938632547042882985648019535599014445903166791748428782724674069768516480568414188416274890014614184102792321736349574131301214065978270739731660172115987907448179991323218115544743936, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N357.C357_d1
