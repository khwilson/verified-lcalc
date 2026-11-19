module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 131, a6 := -167 }
def label : String := "588.a1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 131, a6 := -167 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, -1, 0, -2, 0, 0, 0, 1, 0, 2, 0, -3, 0, 2, 0, 8, 0, -1, 0, 0, 0, 8, 0, -1, 0, -1, 0, 4, 0, 3, 0,                    -2, 0, 0, 0, -1, 0, 3, 0, 6, 0, 11, 0, -2, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (56776448238957141194380450156624122959977275942550614490305090103037123091663137247613620664971258751215319480270415591336458502559565188277764752826105203790857412002724804558225230139710502665521668145964594056236149365735776100123886807985619822256341026930051401777299046254233814381125756892390774149205196831854868300664689201008939436630049392931696398064873827178186251639491736482698382725053621411446291609434569635219947426580155943474813144767199300154826842419228848539215254228514522061486885278629219083323425254017385974823215258273836841414422631011087843766633681843290053901545674578499491640941643196182949101653581219202511837004972389904512086212397045208252053619906904060819281781399040506231597579058835876081653566619002417440171937401222616704082574646720098522967561209751 : Rat)/57469175949131779472586388984186357370103194497719376327221330227628806740762756938058100763887196822699356605715101986250152450057086313755404180127267296767346779043140090482513600354613552067786441533287436831593865167163432891004057652026706507265652979648776387780324026036671563656504798955490923842201560295236973826847295772337994346256366386065756502320635484188649170921390168478422000420238943786230578446986985939328575701894769283443846462662770199569501699332993088486074043221510223045657482465855665101227208758206570245254918264710322820456139797734530504029523902409929864744951084444414792918687347870623318034049659218614411752232958951283721836269925458046644342895261575245609099023649448243818070258555166726633355435970420945066252786047296285506294812790835189041879161241600,            reHi := (27339969475302661759290877498240712876445515142628125684579838805714100849522156445108975857597812489955755814288510486157808002816454919534514289949930628199114666994303047515822524817489162705967658956395191271947392901948211400714352244378487196762503996427993359460036205928243392994466025497081299077675415928439377896910971597373414987936957467794400443634268264313760264851371802697388661546687293979669604384022026757561532331072649087632428105732679499836871598155589728464662971243270894287175712807062347789923445792632940282252646664136735177010200937984330431017543266481639935328727069942843355068843493949483332083443445049320875119263309844039088118120285562656219686991643224008659521075403597927542017399949747881309654681592253064254131299338741844804992852421339017205878089870473 : Rat)/24032564487818744143081580847932476718406790426319011918656192640644773727955334719551569410352827762219730944208133557886427388205690640297714475325948142284526834872585856019960232875565667228347057368465655402302889069904708299874424109029349993947454882398579216708135501797153562983629279563205295424920652487099098145772505504795888544798116852354770900970447566115253289658035888636431018357554467401514605532376375938264677111701448973076517611658976628910882528811978927912358236256267911455456765394812369042331378207977293011652056728878862270372567551779894574412346359189607034347888635313118913402360163654987932996057130218693299460024691925082283676985605191546778543392563931466345623228071587447414829380850342449319403182314903304300432983256142083029905103530712897235694921973760,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -44, a6 := 120 }
def label : String := "588.b1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -44, a6 := 120 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 96,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, 0, 0, 1, 0, 2, 0, 4, 0, 2, 0, -6, 0, -8, 0, 0, 0, -6, 0, -1, 0, -1, 0, -10, 0,                    -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 6, 0, 4, 0, -2, 0, -8, 0, 0, 0, 6, 0, 2, 0, -4, 0, 8, 0, 4, 0, 8, 0,                    0, 0, -8, 0, -8, 0, 6, 0, -10, 0, -4, 0, 1, 0, 0, 0, 4, 0, 1, 0, -12, 0, 12, 0, 10, 0, 14, 0, 0, 0,                    4, 0, 16, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((10237797328529159 : Rat)/4503599627370496, (39263524744578751 : Rat)/9007199254740992),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (24171572725902565277096438807579922580318513532329 : Rat)/695618929190990472137446101841332766958226795134976,            reHi := (9178867465461778369831862296386763677780039657728881 : Rat)/1391237858381980944274892203682665533916453590269952,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 96 = (List.range 96).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 96

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := -6 }
def label : String := "588.b2"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := -6 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 96,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -2, 0, 0, 0, 1, 0, 2, 0, 4, 0, 2, 0, -6, 0, -8, 0, 0, 0, -6, 0, -1, 0, -1, 0, -10, 0,                    -4, 0, -2, 0, 0, 0, 6, 0, -4, 0, 6, 0, 4, 0, -2, 0, -8, 0, 0, 0, 6, 0, 2, 0, -4, 0, 8, 0, 4, 0, 8, 0,                    0, 0, -8, 0, -8, 0, 6, 0, -10, 0, -4, 0, 1, 0, 0, 0, 4, 0, 1, 0, -12, 0, 12, 0, 10, 0, 14, 0, 0, 0,                    4, 0, 16, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((10237797328529159 : Rat)/4503599627370496, (39263524744578751 : Rat)/9007199254740992),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (24171572725902565277096438807579922580318513532329 : Rat)/695618929190990472137446101841332766958226795134976,            reHi := (9178867465461778369831862296386763677780039657728881 : Rat)/1391237858381980944274892203682665533916453590269952,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 96 = (List.range 96).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 96

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -89588, a6 := 10350936 }
def label : String := "588.c1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -89588, a6 := 10350936 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -6, 0, -2, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, -5, 0, -1, 0, 6, 0, -8,                    0, 6, 0, 0, 0, 2, 0, 2, 0, -12, 0, -4, 0, 0, 0, -12, 0, 0, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 10, 0,                    0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((1387035869755093 : Rat)/562949953421312, (2548403243975433 : Rat)/562949953421312),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (19596566667272400588309790635184341308635388154683 : Rat)/86952366148873809017180762730166595869778349391872,            reHi := (588265181422431559880105233555583127490401938769223 : Rat)/86952366148873809017180762730166595869778349391872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5553, a6 := 165894 }
def label : String := "588.c2"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5553, a6 := 165894 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -6, 0, -2, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, -5, 0, -1, 0, 6, 0, -8,                    0, 6, 0, 0, 0, 2, 0, 2, 0, -12, 0, -4, 0, 0, 0, -12, 0, 0, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 10, 0,                    0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((1387035869755093 : Rat)/562949953421312, (2548403243975433 : Rat)/562949953421312),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (19596566667272400588309790635184341308635388154683 : Rat)/86952366148873809017180762730166595869778349391872,            reHi := (588265181422431559880105233555583127490401938769223 : Rat)/86952366148873809017180762730166595869778349391872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1388, a6 := 6840 }
def label : String := "588.c3"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1388, a6 := 6840 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -6, 0, -2, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, -5, 0, -1, 0, 6, 0, -8,                    0, 6, 0, 0, 0, 2, 0, 2, 0, -12, 0, -4, 0, 0, 0, -12, 0, 0, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 10, 0,                    0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((1387035869755093 : Rat)/562949953421312, (2548403243975433 : Rat)/562949953421312),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (19596566667272400588309790635184341308635388154683 : Rat)/86952366148873809017180762730166595869778349391872,            reHi := (588265181422431559880105233555583127490401938769223 : Rat)/86952366148873809017180762730166595869778349391872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 327, a6 := 666 }
def label : String := "588.c4"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 327, a6 := 666 },   conductor := 588,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -6, 0, -2, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, -5, 0, -1, 0, 6, 0, -8,                    0, 6, 0, 0, 0, 2, 0, 2, 0, -12, 0, -4, 0, 0, 0, -12, 0, 0, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 10, 0,                    0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   finite := ((1387035869755093 : Rat)/562949953421312, (2548403243975433 : Rat)/562949953421312),   tail := (2970013680413494746701630626566219329833984375 : Rat)/1326787813550930923724071696932473691860631552,   box := { reLo := (19596566667272400588309790635184341308635388154683 : Rat)/86952366148873809017180762730166595869778349391872,            reHi := (588265181422431559880105233555583127490401938769223 : Rat)/86952366148873809017180762730166595869778349391872,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1780, a6 := 28244 }
def label : String := "588.d1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1780, a6 := 28244 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, -4, 0, 0, 0, 1, 0, 2, 0, 6, 0, -4, 0, 4, 0, 4, 0, 0, 0, 2, 0, 11, 0, 1, 0, -2, 0, 0, 0,                    2, 0, 0, 0, 2, 0, 6, 0, 0, 0, -4, 0, -4, 0, -12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (12761365505697825549811421689005089212081833521005638315470098013116185177917470693482958172307540216442033151314373541222180815153240791544079137512458132221827370903433069130647103813423310127023144283071369654677718895487453989602623575056820690133238741655789920674355430616393724327761106159223317208222991228713505019368339613555792647062679517190477333158872705400456626936653363977775433195565803009765887916287497185543346648070638436220158731450265426420128373369880072973058084577946393559350336695381491734634056840955456740305353299873716566253246403799216944782290775647376038672507374942774152165343397456996607501001192722745783309831825268768021200404833002666974508040842449127546073101843955263016170416179144200103386133532104617533176632226958010294209202012933222992578026413 : Rat)/9043143343687140750997071437322794236050856726627753946061578320633958574470929494580346304309551034256389709789945237804902037774521843234524654622701384227749296466269093702991911936209842968967181987928786283492346997193301792447530708422770496815995748174473074395015582381852331023840251605899437268639112556292206739079039460635404303108790934078010464566583081697663126816898531625243430435914861335362797552633672059689783745380766212973067893416643619129740629320691280642969951726437485923785599129166902454953140638584826159756871481465038996137866215221798663104567097153411465734846748142315467021036561427320742412911040002929097049918640275575723341663245548079723736096815354090575782694516042209884826161849750861783376150428075679790126323532226008734271410352609785844512849920,            reHi := (1623214005339067759405247894501667378398827994034882010549266117984912979091603254864166466699406318633646263388947696604428931413574785210451707567330268133195867830888060452736731193862117694031805058927197646773653183810238416780966094148685447279272153390808661479679290770049707259750021166775516771738348502530238675919281788949397292208168404487795612061320757600301008443166902139738927254095993976021100243133526823770487342231406624448222810195209815096028455032418011543329137471732344267223217797848327339463519948949360180393984584426134967793077274013910272082496601949957280097284483564002342109349734075224482775635592688429314038842535094752833087987128637266419490520246599690612891904783886777480225499008677224736544115312090992617218547026349904175778527122425507800440458088777 : Rat)/1039961484524021186364663215292121337145848523562191703797081506872905236064156891876739824995598368939484816625843702347563734344070011971970335281610659186191169093620945775844069872664131941431225928611810422601619904677229706131466031468618607133839511040064403555426791973913018067741628934678435285893497943973603774994089537973071494857510957418971203425157054395231259583943331136902994500130209053566721718552872286864325130718788114491902807742914016199920172371879497273941544448540310881235343899854193782319611173437255008372040220368479484555854614750506846257025216172642318559507376036366278707419204564141885377484769600336846160740643631691208184291273238029168229651133765720416215009869344854136755008612721349105088257299228703175864527206205991004441212190550125372118977740800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -65, a6 := 804 }
def label : String := "588.d2"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -65, a6 := 804 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, -4, 0, 0, 0, 1, 0, 2, 0, 6, 0, -4, 0, 4, 0, 4, 0, 0, 0, 2, 0, 11, 0, 1, 0, -2, 0, 0, 0,                    2, 0, 0, 0, 2, 0, 6, 0, 0, 0, -4, 0, -4, 0, -12, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (12761365505697825549811421689005089212081833521005638315470098013116185177917470693482958172307540216442033151314373541222180815153240791544079137512458132221827370903433069130647103813423310127023144283071369654677718895487453989602623575056820690133238741655789920674355430616393724327761106159223317208222991228713505019368339613555792647062679517190477333158872705400456626936653363977775433195565803009765887916287497185543346648070638436220158731450265426420128373369880072973058084577946393559350336695381491734634056840955456740305353299873716566253246403799216944782290775647376038672507374942774152165343397456996607501001192722745783309831825268768021200404833002666974508040842449127546073101843955263016170416179144200103386133532104617533176632226958010294209202012933222992578026413 : Rat)/9043143343687140750997071437322794236050856726627753946061578320633958574470929494580346304309551034256389709789945237804902037774521843234524654622701384227749296466269093702991911936209842968967181987928786283492346997193301792447530708422770496815995748174473074395015582381852331023840251605899437268639112556292206739079039460635404303108790934078010464566583081697663126816898531625243430435914861335362797552633672059689783745380766212973067893416643619129740629320691280642969951726437485923785599129166902454953140638584826159756871481465038996137866215221798663104567097153411465734846748142315467021036561427320742412911040002929097049918640275575723341663245548079723736096815354090575782694516042209884826161849750861783376150428075679790126323532226008734271410352609785844512849920,            reHi := (1623214005339067759405247894501667378398827994034882010549266117984912979091603254864166466699406318633646263388947696604428931413574785210451707567330268133195867830888060452736731193862117694031805058927197646773653183810238416780966094148685447279272153390808661479679290770049707259750021166775516771738348502530238675919281788949397292208168404487795612061320757600301008443166902139738927254095993976021100243133526823770487342231406624448222810195209815096028455032418011543329137471732344267223217797848327339463519948949360180393984584426134967793077274013910272082496601949957280097284483564002342109349734075224482775635592688429314038842535094752833087987128637266419490520246599690612891904783886777480225499008677224736544115312090992617218547026349904175778527122425507800440458088777 : Rat)/1039961484524021186364663215292121337145848523562191703797081506872905236064156891876739824995598368939484816625843702347563734344070011971970335281610659186191169093620945775844069872664131941431225928611810422601619904677229706131466031468618607133839511040064403555426791973913018067741628934678435285893497943973603774994089537973071494857510957418971203425157054395231259583943331136902994500130209053566721718552872286864325130718788114491902807742914016199920172371879497273941544448540310881235343899854193782319611173437255008372040220368479484555854614750506846257025216172642318559507376036366278707419204564141885377484769600336846160740643631691208184291273238029168229651133765720416215009869344854136755008612721349105088257299228703175864527206205991004441212190550125372118977740800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2172, a6 := -36828 }
def label : String := "588.e1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2172, a6 := -36828 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 0, -4, 0, 2, 0, 6, 0, 8, 0, 0, 0, -6, 0, -1, 0, 1, 0, -10, 0, 4, 0,                    2, 0, 0, 0, 6, 0, -4, 0, -6, 0, 4, 0, 2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (2688544318935543541028818575156181212521564420100405937063388907130796034785008952319762633141616610270164459652894623933312144813804098358153264329557656821562118273658804168209585458920997641380922752425943221564677394172673936715981635796334719306056279451359639247106541529408269053157032904994276833095989963871477744237675162364565842585101301650538754486999986226854347981795239999564858958605081989553805681070371172395469272594424536831095761145577088775293609794155503837517475828990692075804198729011228270337458305815566164735619564365622038026704088633385723758078023855474532631709578637312546912170153576783011940082247019762307560763429252883963224535070774284343415989251453643426853871456889223696524678386856533958164025858628428151766519934480395255635256782723727259412611342315153 : Rat)/1321791046830030927869486946636286219512373473447545655526090595235462555037543409575336317569405526922085201931447345683753506351312985216374296142927147825648975917992222081097812808156111697559088155265611047126658898844758956493093325996614249667110018531921856918947452598843445964099610375976291248370635886790450398017487802763773869963896426879512399553374616136338930931191973875003706009665495707083303304280700676604557241143579693519208468641243714590098539084658841035179702994094735130050122096714680297328225801438751115640863120088337424870491215347894201592679049755428386889133874942221540237129809001024336314783142162028131470301358055879525602234208285535072819886591016230649009277543937309607815615946768834712567175027319681736523814079087814566644780694189209347963220708556800,            reHi := (25098994178966746461431373248694126914122746351845820172064910622664539163710315391764982626909408106923582860124194632266753471797263123303436856108855563448947175765680516347348819014419667086867666241791685651477498031158602207120842797537620015599116578061462443813010128375722134078571979621920527528078045838749483623390975429994798507011383834756381135554849893342652135275877193805911680813525753638214668619909662022179164246761597234651592903599322827032759122144764345864428099592930165399723250166385009271751263970000489426512495401436983002590839920695548113541924487604139794728465014443670334159171707791435830572544491028940151016998514664489659132731863481323710760198257590542128780169771752185202149982295706404739674052603324900061417753716446701822257134834086048454980303951893 : Rat)/11493835189826355894517277796837271474020638899543875265444266045525761348152551387611620152777439364539871321143020397250030490011417262751080836025453459353469355808628018096502720070922710413557288306657487366318773033432686578200811530405341301453130595929755277556064805207334312731300959791098184768440312059047394765369459154467598869251273277213151300464127096837729834184278033695684400084047788757246115689397397187865715140378953856688769292532554039913900339866598617697214808644302044609131496493171133020245441751641314049050983652942064564091227959546906100805904780481985972948990216888882958583737469574124663606809931843722882350446591790256744367253985091609328868579052315049121819804729889648763614051711033345326671087194084189013250557209459257101258962558167037808375832248320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -457, a6 := 2960 }
def label : String := "588.e2"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -457, a6 := 2960 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 0, -4, 0, 2, 0, 6, 0, 8, 0, 0, 0, -6, 0, -1, 0, 1, 0, -10, 0, 4, 0,                    2, 0, 0, 0, 6, 0, -4, 0, -6, 0, 4, 0, 2, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (2688544318935543541028818575156181212521564420100405937063388907130796034785008952319762633141616610270164459652894623933312144813804098358153264329557656821562118273658804168209585458920997641380922752425943221564677394172673936715981635796334719306056279451359639247106541529408269053157032904994276833095989963871477744237675162364565842585101301650538754486999986226854347981795239999564858958605081989553805681070371172395469272594424536831095761145577088775293609794155503837517475828990692075804198729011228270337458305815566164735619564365622038026704088633385723758078023855474532631709578637312546912170153576783011940082247019762307560763429252883963224535070774284343415989251453643426853871456889223696524678386856533958164025858628428151766519934480395255635256782723727259412611342315153 : Rat)/1321791046830030927869486946636286219512373473447545655526090595235462555037543409575336317569405526922085201931447345683753506351312985216374296142927147825648975917992222081097812808156111697559088155265611047126658898844758956493093325996614249667110018531921856918947452598843445964099610375976291248370635886790450398017487802763773869963896426879512399553374616136338930931191973875003706009665495707083303304280700676604557241143579693519208468641243714590098539084658841035179702994094735130050122096714680297328225801438751115640863120088337424870491215347894201592679049755428386889133874942221540237129809001024336314783142162028131470301358055879525602234208285535072819886591016230649009277543937309607815615946768834712567175027319681736523814079087814566644780694189209347963220708556800,            reHi := (25098994178966746461431373248694126914122746351845820172064910622664539163710315391764982626909408106923582860124194632266753471797263123303436856108855563448947175765680516347348819014419667086867666241791685651477498031158602207120842797537620015599116578061462443813010128375722134078571979621920527528078045838749483623390975429994798507011383834756381135554849893342652135275877193805911680813525753638214668619909662022179164246761597234651592903599322827032759122144764345864428099592930165399723250166385009271751263970000489426512495401436983002590839920695548113541924487604139794728465014443670334159171707791435830572544491028940151016998514664489659132731863481323710760198257590542128780169771752185202149982295706404739674052603324900061417753716446701822257134834086048454980303951893 : Rat)/11493835189826355894517277796837271474020638899543875265444266045525761348152551387611620152777439364539871321143020397250030490011417262751080836025453459353469355808628018096502720070922710413557288306657487366318773033432686578200811530405341301453130595929755277556064805207334312731300959791098184768440312059047394765369459154467598869251273277213151300464127096837729834184278033695684400084047788757246115689397397187865715140378953856688769292532554039913900339866598617697214808644302044609131496493171133020245441751641314049050983652942064564091227959546906100805904780481985972948990216888882958583737469574124663606809931843722882350446591790256744367253985091609328868579052315049121819804729889648763614051711033345326671087194084189013250557209459257101258962558167037808375832248320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 6403, a6 := 44463 }
def label : String := "588.f1"
def inputConductor : Nat := 588
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 588 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 6403, a6 := 44463 },   conductor := 588,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 2, 0, 3, 0, 2, 0, -8, 0, 1, 0, 0, 0, 8, 0, -1, 0, 1, 0, 4, 0, -3, 0, 2,                    0, 0, 0, -1, 0, 3, 0, -6, 0, 11, 0, 2, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20829484405852408313751220703125,   alphaHi := (1349303770452201895863057907712 : Rat)/5207371101463102054595947265625,   geometricUpper := (6951169924537097 : Rat)/9007199254740992,   tail := (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/2006329717359526819584898770042554466000119575120052734198821238605998151047255862899433658734941795520401315795950026926217543855490063288060666046355952906011868160420255888880807650723710407570189687640499297489596763058227943204485759149757493117156448395624349932821636810493633976250291464761671105696411921711762246198279978458853873969480688401838253831613030671480265181703476259829723428882320180385474498423445478127434365550523499325246938389432391391478848864719523364257224289553638947715963241189055011581723905888886619451983979687734427786082386406164825271897279722678328028162893928748577573280927360346957202702018149867097484830847306819178236077014939417428647841786901367741020867392078846649258091354202905635727443798210402707452424551492707620418007752245248,   box := { reLo := (117762172430124606786383844507515633516223097183881466123841921518137993590114752435311548413708543524571233076985006497106065314540518247877221529980456799389520293876907124660068312877639179624838195810174828557794425627748590780720202815627317028575254301318058169966611941683232505352110871962860562607280810460151729492394268155806374946647335022334574708725351503296903923000144542959198198919548654539894256397915233203524087430114484708109752954944629896537381129077796039561749878133803472643263334967157619197285598168520533141287912653336734395848158665046456162421904162223295889854937176179776623510667694393767077111199741033570497936446181533352607993586633328779918890029241873668667551212185243989414125503625639148593584823493788397016313459219704903441023043578606860891138083260311 : Rat)/57469175949131779472586388984186357370103194497719376327221330227628806740762756938058100763887196822699356605715101986250152450057086313755404180127267296767346779043140090482513600354613552067786441533287436831593865167163432891004057652026706507265652979648776387780324026036671563656504798955490923842201560295236973826847295772337994346256366386065756502320635484188649170921390168478422000420238943786230578446986985939328575701894769283443846462662770199569501699332993088486074043221510223045657482465855665101227208758206570245254918264710322820456139797734530504029523902409929864744951084444414792918687347870623318034049659218614411752232958951283721836269925458046644342895261575245609099023649448243818070258555166726633355435970420945066252786047296285506294812790835189041879161241600,            reHi := (581273995507699621075415266494748790199631444279031300044647651372319113637621150759609202077767447346950516502060733514276079366093388189037158364359254249944110593558572195142525953586852703778500275775714182698589392726689272938600928323315166313454545022892758087731237584184071301405657809792055316761577397902998718347976750763175768213386046040991645109015148217597464201624092739463174431508237386167226286251253346747375899658057052281277432289875655241565337298340896091814951953640309009835104509444916466213383899125676820070516721322793415697507396074390329007007220141046066134001598676737151712358018268953203641761790230688622362369325970344291210473244628093648084004391016324291356771211056113225601819852454521747961085279138799212845695293091178811844847533721408296158243390007779 : Rat)/264358209366006185573897389327257243902474694689509131105218119047092511007508681915067263513881105384417040386289469136750701270262597043274859228585429565129795183598444416219562561631222339511817631053122209425331779768951791298618665199322849933422003706384371383789490519768689192819922075195258249674127177358090079603497560552754773992779285375902479910674923227267786186238394775000741201933099141416660660856140135320911448228715938703841693728248742918019707816931768207035940598818947026010024419342936059465645160287750223128172624017667484974098243069578840318535809951085677377826774988444308047425961800204867262956628432405626294060271611175905120446841657107014563977318203246129801855508787461921563123189353766942513435005463936347304762815817562913328956138837841869592644141711360,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (150149411133976492232408063547909392172157249622941889253389771677953544618795529707677812566480380308403343024393717098411195082004169819830250950498605729977867479054808547115091940010687071937433106257390516119269260184107672811289287926479273691784617213105525652637407233767263139068880661238814977192207056079835948178911597859037692494861381808726407457822282439304910791020465663602747654042281412707906930733011003480724747376712697341914831132105981983547509800551791664020847166594090531653227263982511021773364163222687455287865126258589093206783428870097754464858059857470717604905596205852098835856285972251434332275344826193615408149606948616908264304405393454577828653951554267904882572544466113119752091702771590840519715876109983774742128667987440982782175236227631 : Rat)/4012659434719053639169797540085108932000239150240105468397642477211996302094511725798867317469883591040802631591900053852435087710980126576121332092711905812023736320840511777761615301447420815140379375280998594979193526116455886408971518299514986234312896791248699865643273620987267952500582929523342211392823843423524492396559956917707747938961376803676507663226061342960530363406952519659446857764640360770948996846890956254868731101046998650493876778864782782957697729439046728514448579107277895431926482378110023163447811777773238903967959375468855572164772812329650543794559445356656056325787857497155146561854720693914405404036299734194969661694613638356472154029878834857295683573802735482041734784157693298516182708405811271454887596420805414904849102985415240836015504490496, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N588.C588_f1
