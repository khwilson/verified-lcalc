module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -94, a6 := 3973 }
def label : String := "348.a1"
def inputConductor : Nat := 348
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 348 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -94, a6 := 3973 },   conductor := 348,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, -1, 0, -2, 0, 1, 0, 1, 0, 3, 0, 5, 0, 2, 0, -1, 0, 6, 0, -1, 0, 4, 0, -1, 0, -1, 0, -1, 0, 0,                    0],   alphaLo := (2698607540904403791717525880832 : Rat)/8012157598082381725311279296875,   alphaHi := (5397215081808807583452231630848 : Rat)/16024315196164763355255126953125,   geometricUpper := (6431514766117021 : Rat)/9007199254740992,   tail := (560265273671435208597506354684115567587644757513937480420190040275215549199842853348543925229676484257659271194365273847955846633902477429602876392101381914432046231900084637191299653869892611439594335724103236349131604789950649206347656904651679924252913914544306541713610495828786958029338940983761099910894611204707740727019766183970533225406617780654954349507967708570565943972595043574458771767291207243722418965270521267862996521018430788396807915283677226526894000231538447516306583416476160552773948654846951780401837981 : Rat)/4181431596836509616268733369262152434730946063056974020821379203983281251981456736421766340428710134835247391244932723207257022129512454041112291655386336586182885195530759148517596249869231847639378186971746085290270785902407761562830041816988860668870488531707081902836273309521280047572480121522253351870002728791726421839070830382361823006063215772196873970406220397413621220348898842253412024858910247711625282782615422821975125966490645654999455665570403039754989516599142150201565448307426074283759229511881664278367830016,   box := { reLo := (588070789660185400305376085167784258671322598882898443538639353993917812227595966380040672466159208277639463926508790421736172563831824109202060873615611007935113188948854071055231982570257760601735066678872662651167239678521912706460399718857564145195002778421016112846448391785838157331040541714673646039622164465180935598211080114406859232076842044412437578135007183183258154209292770503765489143270877854462365174869722651856609578068624320056424655457895842473988017103696613093170865526155887304552779626828252064085302204284419153089 : Rat)/608683043109628252827083748145284848299653418852234303352864011693652034355432981496230412639553778281959712281531306500637729466178505409985582537334365684037896287556333021198309282357178047574389722097367546608833018489440706052856154176639768944233105106508503832921295492653389201456059432971747245611108701127270566506148115768343003448537672310751755099453757750238283331179201204247839098736681375032944314397099257661310699273110539083680775114397584564280171222020904958341751000117120562209180069187768332678715006669346884812800,            reHi := (751184289823614224218130029642524069465609509306360880923482502709909909519981569070599953199857618102616719182539762237086297988658613779549045408855959567866821445178933804211725628060053290916768754437831698153331668279112861756825936208591639981640544014195972379660039724055961702720644068594968704314843058923516596217563239432659097718516682693372612206997916345727782893108106606187056646097077489709326151378813577218302361390074169955708153850746421729274681446260891997661279564588898337955824140634906308225167970532180277617471 : Rat)/608683043109628252827083748145284848299653418852234303352864011693652034355432981496230412639553778281959712281531306500637729466178505409985582537334365684037896287556333021198309282357178047574389722097367546608833018489440706052856154176639768944233105106508503832921295492653389201456059432971747245611108701127270566506148115768343003448537672310751755099453757750238283331179201204247839098736681375032944314397099257661310699273110539083680775114397584564280171222020904958341751000117120562209180069187768332678715006669346884812800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (560265273671435208597506354684115567587644757513937480420190040275215549199842853348543925229676484257659271194365273847955846633902477429602876392101381914432046231900084637191299653869892611439594335724103236349131604789950649206347656904651679924252913914544306541713610495828786958029338940983761099910894611204707740727019766183970533225406617780654954349507967708570565943972595043574458771767291207243722418965270521267862996521018430788396807915283677226526894000231538447516306583416476160552773948654846951780401837981 : Rat)/8362863193673019232537466738524304869461892126113948041642758407966562503962913472843532680857420269670494782489865446414514044259024908082224583310772673172365770391061518297035192499738463695278756373943492170580541571804815523125660083633977721337740977063414163805672546619042560095144960243044506703740005457583452843678141660764723646012126431544393747940812440794827242440697797684506824049717820495423250565565230845643950251932981291309998911331140806079509979033198284300403130896614852148567518459023763328556735660032, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := 1 }
def label : String := "348.b1"
def inputConductor : Nat := 348
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 348 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := 1 },   conductor := 348,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -3, 0, 1, 0, -3, 0, -3, 0, 0, 0, 1, 0, -4, 0, 3, 0, -2, 0, -5, 0, -1, 0, 1, 0, -2,                    0, 3, 0, 0, 0, -6, 0, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8012157598082381725311279296875,   alphaHi := (5397215081808807583452231630848 : Rat)/16024315196164763355255126953125,   finite := ((11801703963178589 : Rat)/9007199254740992, (29602760095425391 : Rat)/9007199254740992),   tail := (82386352587898453014472289947986602783203125 : Rat)/182960402663644384139303313011403822888648704,   box := { reLo := (329961584785425769182454545149926916156362070477911 : Rat)/383695774366867147486508221488491549978575406891008,            reHi := (1433818414957458370904398685192679572437836687748109 : Rat)/383695774366867147486508221488491549978575406891008,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -50, a6 := 129 }
def label : String := "348.c1"
def inputConductor : Nat := 348
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 348 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -50, a6 := 129 },   conductor := 348,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -4, 0, -3, 0, 1, 0, -1, 0, -3, 0, -4, 0, -5, 0, 4, 0, -3, 0, -6, 0, 11, 0, 1, 0, -1, 0,                    2, 0, -1, 0, 12, 0, 6, 0, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8012157598082381725311279296875,   alphaHi := (5397215081808807583452231630848 : Rat)/16024315196164763355255126953125,   finite := ((13163947783480575 : Rat)/9007199254740992, (8332715134643899 : Rat)/2251799813685248),   tail := (82386352587898453014472289947986602783203125 : Rat)/182960402663644384139303313011403822888648704,   box := { reLo := (387991520920360329841389832708401051168145415156925 : Rat)/383695774366867147486508221488491549978575406891008,            reHi := (398157744138391776365584336169808202686353717647601 : Rat)/95923943591716786871627055372122887494643851722752,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := -3 }
def label : String := "348.d1"
def inputConductor : Nat := 348
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 29] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 348 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := -3 },   conductor := 348,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, -3, 0, 2, 0, -3, 0, 2, 0, 1, 0, 8, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8012157598082381725311279296875,   alphaHi := (5397215081808807583452231630848 : Rat)/16024315196164763355255126953125,   geometricUpper := (6431514766117021 : Rat)/9007199254740992,   tail := (63036459335324503541676176266748474009248439953462669302175723623363319968577547008541645137911067550310734409412111626196265344804652732888147126185295606317319475241118681243670841757541502225130695022307498834003856718550331950671964674361097156425166335550755925139332747867635370945356079723729405302991730932207224336755533828896155847388270539851905706054780485212296329325587486810720898828125 : Rat)/52112660921673011660015432435794773625249318449126620378382568550860236594124594286200262749237899289754588318196078770197239002014413558992957713198244882676053001917784099471208937879805483822218551480797882923253419086053610326048743340094777965043676659118046711347070855541216958776256884556538881947303254033949381062005166037863512526358746641711693072624871515236186868835432236757808465313792,   box := { reLo := (537613396472731940972062581261956790575852232104673314857090557338678196913645889940598116003609384865484854705986383309111767555800839077172333668514205004919201827800900303586494174506991494902639542724801462722930027697284100496743164314681229958795559257368941242599141923644540423095755873655989350145400986453844653845903558248664095976621914276147676141522946693044037325256221296876002210831903546319 : Rat)/830425934882348383769736219028039055646941065597114766686703798284510796475877205492429857962969518951593764541059745399240893931095093017332374716145237845643853176425282770814106022946965744831236172649567827948042500087176921535703565116795006302453821516761193544891400232574678187576202588069781174301076550198060346846170031872392834127594531278737380009357215693949261173200723956344213245510664847360,            reHi := (53478835209194895632062113230458893401499312967121059099899199802250225522353859301574152307840498974897027149281214436128144639630799163434030985452869674244477270615016936210483324539923113568551855998336207152164160411503226605689872075751441866347436509447440109285754861784015025222059424695542435673559662193431289271670094364102266296272454508657889138780889869966487831533981780361794861795157176088581 : Rat)/17438944632529316059164460599588820168585762377539410100420779763974726725993421315341027017222359897983469055362254653384058772552996953363979869039049994758520916704930938187096226481886280641455959625640924386908892501830715352249774867452695132351530251851985064442719404884068241939100254349465404660322607554159267283769570669320249516679485156853484980196501529572934484637215203083228478155723961794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (63036459335324503541676176266748474009248439953462669302175723623363319968577547008541645137911067550310734409412111626196265344804652732888147126185295606317319475241118681243670841757541502225130695022307498834003856718550331950671964674361097156425166335550755925139332747867635370945356079723729405302991730932207224336755533828896155847388270539851905706054780485212296329325587486810720898828125 : Rat)/104225321843346023320030864871589547250498636898253240756765137101720473188249188572400525498475798579509176636392157540394478004028827117985915426396489765352106003835568198942417875759610967644437102961595765846506838172107220652097486680189555930087353318236093422694141711082433917552513769113077763894606508067898762124010332075727025052717493283423386145249743030472373737670864473515616930627584, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N348.C348_d1
