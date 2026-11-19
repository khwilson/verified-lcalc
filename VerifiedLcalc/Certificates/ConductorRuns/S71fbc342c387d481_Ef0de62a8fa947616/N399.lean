module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -48, a6 := 90 }
def label : String := "399.a1"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 7, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -48, a6 := 90 },   conductor := 399,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, 1, 3, 1, 0, -2, 1, 0, -1, 0, -1, -4, -1, 1, 0, -1, 2, -6, -3, -5, 0, -1, -1, -6,                    0, 0, -5, 2, 4, 0, -1, -2, -1, 0, 0, -10, 1, 8, 2, 0, 6, 4, 1, 1, 5, 4, 0, -6, 1, 0, 3, -1, 6, -4, 0,                    -2, 0, 1, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   finite := ((4658055310597183 : Rat)/4503599627370496, (23623384534431297 : Rat)/9007199254740992),   tail := (13995793708723047294688320033550262451171875 : Rat)/19999132281707469671922733926813405022257152,   box := { reLo := (14028331730879651734969499159488702834454274135867 : Rat)/41941220262847383437412105300084585969236630831104,            reHi := (278702981261747345315671812680766454916959801443653 : Rat)/83882440525694766874824210600169171938473261662208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -13, a6 := -22 }
def label : String := "399.a2"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 7, 7, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -13, a6 := -22 },   conductor := 399,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, -1, 0, 1, 1, 3, 1, 0, -2, 1, 0, -1, 0, -1, -4, -1, 1, 0, -1, 2, -6, -3, -5, 0, -1, -1, -6,                    0, 0, -5, 2, 4, 0, -1, -2, -1, 0, 0, -10, 1, 8, 2, 0, 6, 4, 1, 1, 5, 4, 0, -6, 1, 0, 3, -1, 6, -4, 0,                    -2, 0, 1, 7],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   finite := ((4658055310597183 : Rat)/4503599627370496, (23623384534431297 : Rat)/9007199254740992),   tail := (13995793708723047294688320033550262451171875 : Rat)/19999132281707469671922733926813405022257152,   box := { reLo := (14028331730879651734969499159488702834454274135867 : Rat)/41941220262847383437412105300084585969236630831104,            reHi := (278702981261747345315671812680766454916959801443653 : Rat)/83882440525694766874824210600169171938473261662208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -466, a6 := 2813 }
def label : String := "399.b1"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 7, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -466, a6 := 2813 },   conductor := 399,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, -1, 4, -1, -1, 3, 1, -4, -2, -1, 4, 1, 4, -1, 0, -1, -1, -4, -1, 2, -6, 3, 11, -4, 1, 1,                    10, -4, 0, -5],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   geometricUpper := (6576294708226881 : Rat)/9007199254740992,   tail := (436956920720391849110761036093101001374837975268711933714480427239083643262095538261064540378405219196006547089136008484897321479926499532021996998660652258854951094836917031132188122666134126532924271449626720262978115550221350558095343185074477822577598494169510301302788251343347324489886219751236539173963659217137716627365425521738689348347996089914088563602790339180504792294403409258645498429467986387447073586615726025720332076857301992017034417965340357176512245854684414104345997906438921047692244353888280151154257 : Rat)/1454038241518699144106915111460951177166220456377853502097170595121721843171180172419790118201893756547442686882673240822299841369652508116274403631445150723566182706884851505248725204556669677512246275711951474512212314792596894918119665036644768240302998121853431055436489555478795671413574061106205660726672588035631586698393289808517935233481910396615688242357601835488885194538769861105925832918325556175937111618352016550293754159065190490009735708983244160863625981742631114748627543670503379557575189224239743717343232,   box := { reLo := (1836667312668060819269335955636800112321167034323625278740622559653092882061425962546054509648175614115271403814373660961603201402917776551319019555129502751070779631256894693767976030346529839357409780473546364758957597703118514891855057498676739737543418007429865880737239263575188856799841065682692827934546050522290628409916647715190711341337753955458769376978006426262508377086357534581761745953128472031230563551903387899266906091136805549892649509288711905125378691740472492596819805954029189150558857886175480345193951787143523 : Rat)/1778668745920833927296590920908245822740660580710877775631275180939635998159020059527960916213555174143452166517658988110330593501130941867887081049786406738934277383216050074738800048286887787300953082953717079047512564874509177868424827961282252751950963884010939528669388666983652602417633228974408102263009972881645841956528951062276645739973266075295382315133281145102565725844378384166500799727399536629138764274938182081734266851842345680186708566270657655016552262730916746413633171001875327494577339757569231017337707456102400,            reHi := (6779948737997766859444583505499288659074801437431898911583662668124680257451994181588395515678339261288389730110116252543169041983926931964223318165343322306075397174082937371230751860667324880316843597937405486189710194213032533253863722072090542262349630729659377275380072246408759498851345590741528982529345056726065641437788290975594543602544157194775328277901669737842317800414211145493886352976108662746044710188428365300422807713935289447000701142903656497382128603414306554508909067713950983646658839283648477006050673409573401 : Rat)/4150227073815279163692045482119240253061541354992048143139642088859150662371046805565242137831628739668055055207870972257438051502638864358403189116168282390846647227504116841057200112669404837035557193558673184444195984707188081692991265242991923087885582396025525566895240222961856072307810867606952238613689936723840297898567552478645506726604287509022558735310989338572653360303549563055168532697265585467990449974855758190713289320965473253768986654631534528371955279705472408298477399004375764154013792767661539040454650730905600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (436956920720391849110761036093101001374837975268711933714480427239083643262095538261064540378405219196006547089136008484897321479926499532021996998660652258854951094836917031132188122666134126532924271449626720262978115550221350558095343185074477822577598494169510301302788251343347324489886219751236539173963659217137716627365425521738689348347996089914088563602790339180504792294403409258645498429467986387447073586615726025720332076857301992017034417965340357176512245854684414104345997906438921047692244353888280151154257 : Rat)/2908076483037398288213830222921902354332440912755707004194341190243443686342360344839580236403787513094885373765346481644599682739305016232548807262890301447132365413769703010497450409113339355024492551423902949024424629585193789836239330073289536480605996243706862110872979110957591342827148122212411321453345176071263173396786579617035870466963820793231376484715203670977770389077539722211851665836651112351874223236704033100587508318130380980019471417966488321727251963485262229497255087341006759115150378448479487434686464, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -431, a6 := 3408 }
def label : String := "399.b2"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 7, 7, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -431, a6 := 3408 },   conductor := 399,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, -1, 4, -1, -1, 3, 1, -4, -2, -1, 4, 1, 4, -1, 0, -1, -1, -4, -1, 2, -6, 3, 11, -4, 1, 1,                    10, -4, 0, -5],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   geometricUpper := (6576294708226881 : Rat)/9007199254740992,   tail := (436956920720391849110761036093101001374837975268711933714480427239083643262095538261064540378405219196006547089136008484897321479926499532021996998660652258854951094836917031132188122666134126532924271449626720262978115550221350558095343185074477822577598494169510301302788251343347324489886219751236539173963659217137716627365425521738689348347996089914088563602790339180504792294403409258645498429467986387447073586615726025720332076857301992017034417965340357176512245854684414104345997906438921047692244353888280151154257 : Rat)/1454038241518699144106915111460951177166220456377853502097170595121721843171180172419790118201893756547442686882673240822299841369652508116274403631445150723566182706884851505248725204556669677512246275711951474512212314792596894918119665036644768240302998121853431055436489555478795671413574061106205660726672588035631586698393289808517935233481910396615688242357601835488885194538769861105925832918325556175937111618352016550293754159065190490009735708983244160863625981742631114748627543670503379557575189224239743717343232,   box := { reLo := (1836667312668060819269335955636800112321167034323625278740622559653092882061425962546054509648175614115271403814373660961603201402917776551319019555129502751070779631256894693767976030346529839357409780473546364758957597703118514891855057498676739737543418007429865880737239263575188856799841065682692827934546050522290628409916647715190711341337753955458769376978006426262508377086357534581761745953128472031230563551903387899266906091136805549892649509288711905125378691740472492596819805954029189150558857886175480345193951787143523 : Rat)/1778668745920833927296590920908245822740660580710877775631275180939635998159020059527960916213555174143452166517658988110330593501130941867887081049786406738934277383216050074738800048286887787300953082953717079047512564874509177868424827961282252751950963884010939528669388666983652602417633228974408102263009972881645841956528951062276645739973266075295382315133281145102565725844378384166500799727399536629138764274938182081734266851842345680186708566270657655016552262730916746413633171001875327494577339757569231017337707456102400,            reHi := (6779948737997766859444583505499288659074801437431898911583662668124680257451994181588395515678339261288389730110116252543169041983926931964223318165343322306075397174082937371230751860667324880316843597937405486189710194213032533253863722072090542262349630729659377275380072246408759498851345590741528982529345056726065641437788290975594543602544157194775328277901669737842317800414211145493886352976108662746044710188428365300422807713935289447000701142903656497382128603414306554508909067713950983646658839283648477006050673409573401 : Rat)/4150227073815279163692045482119240253061541354992048143139642088859150662371046805565242137831628739668055055207870972257438051502638864358403189116168282390846647227504116841057200112669404837035557193558673184444195984707188081692991265242991923087885582396025525566895240222961856072307810867606952238613689936723840297898567552478645506726604287509022558735310989338572653360303549563055168532697265585467990449974855758190713289320965473253768986654631534528371955279705472408298477399004375764154013792767661539040454650730905600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (436956920720391849110761036093101001374837975268711933714480427239083643262095538261064540378405219196006547089136008484897321479926499532021996998660652258854951094836917031132188122666134126532924271449626720262978115550221350558095343185074477822577598494169510301302788251343347324489886219751236539173963659217137716627365425521738689348347996089914088563602790339180504792294403409258645498429467986387447073586615726025720332076857301992017034417965340357176512245854684414104345997906438921047692244353888280151154257 : Rat)/2908076483037398288213830222921902354332440912755707004194341190243443686342360344839580236403787513094885373765346481644599682739305016232548807262890301447132365413769703010497450409113339355024492551423902949024424629585193789836239330073289536480605996243706862110872979110957591342827148122212411321453345176071263173396786579617035870466963820793231376484715203670977770389077539722211851665836651112351874223236704033100587508318130380980019471417966488321727251963485262229497255087341006759115150378448479487434686464, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1925, a6 := 31458 }
def label : String := "399.c1"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1925, a6 := 31458 },   conductor := 399,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, 0, -1, -1, -3, 1, 0, -2, 1, -4, -1, 0, -1, -4, 1, -1, 0, 1, -2, 2, 3, -5, -4, -1, 1,                    -2, 0, 0, 5, 2, -4, 0, -1, 6, -1, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   finite := ((13630321446967741 : Rat)/9007199254740992, (21705895387523749 : Rat)/4503599627370496),   tail := (13995793708723047294688320033550262451171875 : Rat)/19999132281707469671922733926813405022257152,   box := { reLo := (68234139586511683456551949528828198466554329554609 : Rat)/83882440525694766874824210600169171938473261662208,            reHi := (231494439989026134832394686811833538549863147545401 : Rat)/41941220262847383437412105300084585969236630831104,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -210, a6 := -441 }
def label : String := "399.c2"
def inputConductor : Nat := 399
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 399 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -210, a6 := -441 },   conductor := 399,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, 0, -1, -1, -3, 1, 0, -2, 1, -4, -1, 0, -1, -4, 1, -1, 0, 1, -2, 2, 3, -5, -4, -1, 1,                    -2, 0, 0, 5, 2, -4, 0, -1, 6, -1, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/4289595227235930919647216796875,   alphaHi := (5397215081808807583452231630848 : Rat)/17158380908943723583221435546875,   finite := ((13630321446967741 : Rat)/9007199254740992, (21705895387523749 : Rat)/4503599627370496),   tail := (13995793708723047294688320033550262451171875 : Rat)/19999132281707469671922733926813405022257152,   box := { reLo := (68234139586511683456551949528828198466554329554609 : Rat)/83882440525694766874824210600169171938473261662208,            reHi := (231494439989026134832394686811833538549863147545401 : Rat)/41941220262847383437412105300084585969236630831104,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N399.C399_c2
