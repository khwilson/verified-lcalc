module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -47, a6 := 133 }
def label : String := "434.a1"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 7, 7, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -47, a6 := 133 },   conductor := 434,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, -3, 0, -2, 0, -2, 1, 0, 1, 2, 3, -6, 0, 0, 2, 0, 0, -5, 2, 0, -1, 8, 0,                    -1, -1, 0, -2, 0, -3, -8, 6, 0, 0, -10, 0, -6, -2, 0, 0, -4, 0, 1, 5, 0, -2, 4, 0, 0, 1, 0, -8, 6, 0,                    6, 1, 3, 1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   finite := ((14370282920280431 : Rat)/9007199254740992, (7262086215497507 : Rat)/2251799813685248),   tail := (161616374574840444312907365561008453369140625 : Rat)/177711646162757659427651723936857702401048576,   box := { reLo := (1022644103470399910774287675716734223611250784364669 : Rat)/1490753336694078203936074672630516017223055293022208,            reHi := (1540859246708493490997712531250757350649574334047193 : Rat)/372688334173519550984018668157629004305763823255552,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7, a6 := -3 }
def label : String := "434.a2"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7, a6 := -3 },   conductor := 434,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 0, 0, -1, -1, -3, 0, -2, 0, -2, 1, 0, 1, 2, 3, -6, 0, 0, 2, 0, 0, -5, 2, 0, -1, 8, 0,                    -1, -1, 0, -2, 0, -3, -8, 6, 0, 0, -10, 0, -6, -2, 0, 0, -4, 0, 1, 5, 0, -2, 4, 0, 0, 1, 0, -8, 6, 0,                    6, 1, 3, 1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   finite := ((14370282920280431 : Rat)/9007199254740992, (7262086215497507 : Rat)/2251799813685248),   tail := (161616374574840444312907365561008453369140625 : Rat)/177711646162757659427651723936857702401048576,   box := { reLo := (1022644103470399910774287675716734223611250784364669 : Rat)/1490753336694078203936074672630516017223055293022208,            reHi := (1540859246708493490997712531250757350649574334047193 : Rat)/372688334173519550984018668157629004305763823255552,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2364, a6 := -43641 }
def label : String := "434.b1"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2364, a6 := -43641 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -3, 1, -3, -3, -1, 1, 6, -3, 4, -3, 4, -1, 9, 1, 2, 6, 6, -3, 3, 4, -9, -3, 4, 4, -9, -1, 5, 9,                    -1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (118018168193242623333779655830444610728265547546123103104041937336697540151885402543930487926693324190547871408683941601996551449119297219316555035374498988119825761574395450437793199764087103825808361718152024705604799132288236713162416411778031149866677653749023237081962395463825194719755047558450892308328747303345805706572916413460833346707624047088547305562392277200615774084323797308096183174228550460789599607016778660521021028370870792231353462968153510141656491788834877486993858700063821624266428503513279687459426093279 : Rat)/216678979004120978856966627978231886947928607025879050494603654695189784903758240428502941087183779463540060273550533763643608895851078507604174398673666417920370468437198837978877073314032473158168983471574979158583733379068488287811801049064354152321100991968400672783446167298276511887096355024117817054977339522868556431604019711056513293932985210167679695441518823224796639506358991186155508537222258979769607327302683843807190340928022889361683358057645279877010533154340094292607756845074447358043387733520869514568689254400,            reHi := (109024475369161197956906374789295091814536748413484780730057679595081445872754464428747201321098128426250410864191156306293722518162111739890334562810407632247666041299998592739404626350204990584454491386809017338009175821018245997105277153185695705663702215666783554002241041269274896785241514988326847175984892803302975902300293042790285336921350948181178364845332438499881053353913498031496883759059316688314116506653623827434160048760215221264099109775519322099617925079585676322773707645226636985525297273699978371692750060811 : Rat)/72226326334706992952322209326077295649309535675293016831534551565063261634586080142834313695727926487846686757850177921214536298617026169201391466224555472640123489479066279326292357771344157719389661157191659719527911126356162762603933683021451384107033663989466890927815389099425503962365451674705939018325779840956185477201339903685504431310995070055893231813839607741598879835452997062051836179074086326589869109100894614602396780309340963120561119352548426625670177718113364764202585615024815786014462577840289838189563084800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -139, a6 := 465 }
def label : String := "434.c1"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 7, 7, 7, 7, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -139, a6 := 465 },   conductor := 434,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -2, -2, 1, 1, 1, -2, -2, -2, -4, 1, 4, 1, -2, 1, -8, -2, -2, -2, 0, -2, -1, -4, 4, 1, 0,                    4, -1, 1, 4, -2, -2, 1, -8, -8, 8, -2],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   finite := ((5309038899389371 : Rat)/4503599627370496, (48082240731661613 : Rat)/9007199254740992),   tail := (161616374574840444312907365561008453369140625 : Rat)/177711646162757659427651723936857702401048576,   box := { reLo := (200814193152243580187700896646758446123405181629729 : Rat)/745376668347039101968037336315258008611527646511104,            reHi := (9313677475081781279836176324496590083338143837745687 : Rat)/1490753336694078203936074672630516017223055293022208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 21, a6 := 49 }
def label : String := "434.c2"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 21, a6 := 49 },   conductor := 434,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -2, -2, 1, 1, 1, -2, -2, -2, -4, 1, 4, 1, -2, 1, -8, -2, -2, -2, 0, -2, -1, -4, 4, 1, 0,                    4, -1, 1, 4, -2, -2, 1, -8, -8, 8, -2],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   finite := ((5309038899389371 : Rat)/4503599627370496, (48082240731661613 : Rat)/9007199254740992),   tail := (161616374574840444312907365561008453369140625 : Rat)/177711646162757659427651723936857702401048576,   box := { reLo := (200814193152243580187700896646758446123405181629729 : Rat)/745376668347039101968037336315258008611527646511104,            reHi := (9313677475081781279836176324496590083338143837745687 : Rat)/1490753336694078203936074672630516017223055293022208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3374, a6 := -75754 }
def label : String := "434.d1"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3374, a6 := -75754 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, 0, 1, -4, 1, 3, 1, -6, -2, 2, 3, 1, 0, -3, 1, 4, -4, -5, 1, 3, 3, 1,                    1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (15340675518900036903201017724360110012413500454039323332913068351442213546638508078955258559810837311993824052662367991348192192837464388502907996185891672318827666497547103677801551894248979115143375360073299340079312080658659604608952012172432764384397232090630160181106078501370286717552418572639468525697076087211100293430968500640848272935458291743327546014855433711110562592819573746004769430485366761695681357766612996207554338221232522195098753290600106251644817368443817217816808209456352514827408394469059191984866470143 : Rat)/6566029666791544813847473575097935968119048697753910621048595596823932875871461831166755790520720589804244250713652538292230572601547833563762860565868679330920317225369661756935668888304014338126332832471969065411628284214196614782175789365586489464275787635406080993437762645402318542033222879518721728938707258268744134291030900335045857391908642732353930164894509794690807257768454278368348743552189666053624464463717692236581525482667360283687374486595311511424561610737578614927507783184074162364951143440026348926323916800,            reHi := (585243450031043466514769972139155924000214991160544183362638805233372667196991846924739899973520549535181725964134635623493874176170731968853470507603543076096109417764186444764590354866100857543721234776142482617858487787579047224379868748110740921340159603823969228322925254670945960396074156398692461644142275087083833337356206234004611972354217573867446456976460921856864447911774778851285300880087124508730917098656605285246612775640097493028607299605682946847381414121129390493117063195586503971372294028692922434777125203227 : Rat)/177282801003371709973881786527644271139214314839355586768312081114246187648529469441502406344059455924714594769268618533890225460241791506221597235278454341934848565084980867437263059984208387129410986476743164766113963673783308599118746312870835215535446266155964186822819591425862600634897017747005486681345095973256091625857834309046238149581533353773556114452151764456651795959748265515945416075909120983447860540520377690387701188032018727659559111138073410808463163489914622603042710145970002383853680872880711421010745753600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -4, a6 := 16 }
def label : String := "434.d2"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -4, a6 := 16 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, 0, 1, -4, 1, 3, 1, -6, -2, 2, 3, 1, 0, -3, 1, 4, -4, -5, 1, 3, 3, 1,                    1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (15340675518900036903201017724360110012413500454039323332913068351442213546638508078955258559810837311993824052662367991348192192837464388502907996185891672318827666497547103677801551894248979115143375360073299340079312080658659604608952012172432764384397232090630160181106078501370286717552418572639468525697076087211100293430968500640848272935458291743327546014855433711110562592819573746004769430485366761695681357766612996207554338221232522195098753290600106251644817368443817217816808209456352514827408394469059191984866470143 : Rat)/6566029666791544813847473575097935968119048697753910621048595596823932875871461831166755790520720589804244250713652538292230572601547833563762860565868679330920317225369661756935668888304014338126332832471969065411628284214196614782175789365586489464275787635406080993437762645402318542033222879518721728938707258268744134291030900335045857391908642732353930164894509794690807257768454278368348743552189666053624464463717692236581525482667360283687374486595311511424561610737578614927507783184074162364951143440026348926323916800,            reHi := (585243450031043466514769972139155924000214991160544183362638805233372667196991846924739899973520549535181725964134635623493874176170731968853470507603543076096109417764186444764590354866100857543721234776142482617858487787579047224379868748110740921340159603823969228322925254670945960396074156398692461644142275087083833337356206234004611972354217573867446456976460921856864447911774778851285300880087124508730917098656605285246612775640097493028607299605682946847381414121129390493117063195586503971372294028692922434777125203227 : Rat)/177282801003371709973881786527644271139214314839355586768312081114246187648529469441502406344059455924714594769268618533890225460241791506221597235278454341934848565084980867437263059984208387129410986476743164766113963673783308599118746312870835215535446266155964186822819591425862600634897017747005486681345095973256091625857834309046238149581533353773556114452151764456651795959748265515945416075909120983447860540520377690387701188032018727659559111138073410808463163489914622603042710145970002383853680872880711421010745753600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 36, a6 := -424 }
def label : String := "434.d3"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 7, 7, 7, 31, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 36, a6 := -424 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, 0, 1, -4, 1, 3, 1, -6, -2, 2, 3, 1, 0, -3, 1, 4, -4, -5, 1, 3, 3, 1,                    1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (15340675518900036903201017724360110012413500454039323332913068351442213546638508078955258559810837311993824052662367991348192192837464388502907996185891672318827666497547103677801551894248979115143375360073299340079312080658659604608952012172432764384397232090630160181106078501370286717552418572639468525697076087211100293430968500640848272935458291743327546014855433711110562592819573746004769430485366761695681357766612996207554338221232522195098753290600106251644817368443817217816808209456352514827408394469059191984866470143 : Rat)/6566029666791544813847473575097935968119048697753910621048595596823932875871461831166755790520720589804244250713652538292230572601547833563762860565868679330920317225369661756935668888304014338126332832471969065411628284214196614782175789365586489464275787635406080993437762645402318542033222879518721728938707258268744134291030900335045857391908642732353930164894509794690807257768454278368348743552189666053624464463717692236581525482667360283687374486595311511424561610737578614927507783184074162364951143440026348926323916800,            reHi := (585243450031043466514769972139155924000214991160544183362638805233372667196991846924739899973520549535181725964134635623493874176170731968853470507603543076096109417764186444764590354866100857543721234776142482617858487787579047224379868748110740921340159603823969228322925254670945960396074156398692461644142275087083833337356206234004611972354217573867446456976460921856864447911774778851285300880087124508730917098656605285246612775640097493028607299605682946847381414121129390493117063195586503971372294028692922434777125203227 : Rat)/177282801003371709973881786527644271139214314839355586768312081114246187648529469441502406344059455924714594769268618533890225460241791506221597235278454341934848565084980867437263059984208387129410986476743164766113963673783308599118746312870835215535446266155964186822819591425862600634897017747005486681345095973256091625857834309046238149581533353773556114452151764456651795959748265515945416075909120983447860540520377690387701188032018727659559111138073410808463163489914622603042710145970002383853680872880711421010745753600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -522, a6 := 4373 }
def label : String := "434.e1"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 7, 7, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -522, a6 := 4373 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 2, 1, 2, 2, -1, 1, 1, 2, -6, 2, 4, -1, 4, 1, 2, 1, -4, 2, -2, -6, -4, 2, -1, 4, -4, -1, 0, 4,                    -1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (56651844432289919206602598739260672698114566548178458882504052995941221240119909508891312961500461044648346519687761794827059618860023017162224651430020334088916581856683853113567303660691084387596620962717864578416364276848620637002023504152945532037540346488019204423128845665749373672345267839255382494724042766282085408356405813129251729358983517230973511104387002736051575198660693945425552750988583875086637199425304329301018045362322710472732170163331807038928278677968291597946805375467438474455161652925166530696600435841 : Rat)/22415066793529756433479306342575712442889166244056453499441757382261012231423266251224442181432804772090351062781089699687269885777697776648707696414517215646934876045227465997814869653175773085327825876369825430198317246110533271152944936110105601964251826755351793736218569030856190884872036726632877626376966157538126527407312383902397926958584676913897899528432981712909997190312999088222983641781612997907200757996829363152467966302898919589139657730101235849345917222862768375097354156387011795659660800019400294610554060800,            reHi := (234834751270254843352664336531424530774705824684814565529702756113660355805388544946491353291879296043922231923351730469887712960905912733025772554378854111699421130551703376103397815720677588187933557048639754905716993812695999621656898876218797201078135369575594961828388132523172459243379299735127483444672758530691526509917875824085474637333151478579001922707741854881512934486937797549980128323270548520743757114590578855008102056865332424264996287150552253656148260136413356225263942340356139584564110942733531901783488612989 : Rat)/67245200380589269300437919027727137328667498732169360498325272146783036694269798753673326544298414316271053188343269099061809657333093329946123089243551646940804628135682397993444608959527319255983477629109476290594951738331599813458834808330316805892755480266055381208655707092568572654616110179898632879130898472614379582221937151707193780875754030741693698585298945138729991570938997264668950925344838993721602273990488089457403898908696758767418973190303707548037751668588305125292062469161035386978982400058200883831662182400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -32, a6 := 61 }
def label : String := "434.e2"
def inputConductor : Nat := 434
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 7, 7, 7, 7, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 434 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -32, a6 := 61 },   conductor := 434,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 2, 1, 2, 2, -1, 1, 1, 2, -6, 2, 4, -1, 4, 1, 2, 1, -4, 2, -2, -6, -4, 2, -1, 4, -4, -1, 0, 4,                    -1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/2236890549399705410003662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/17895124395197643184661865234375,   geometricUpper := (3331006291646725 : Rat)/4503599627370496,   tail := (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/432146887681962165848974389875723199994811674079107517974041071306968659139182251116894876900615758309804565840189261335733870537985962405175090302166218420619832912725239435430526235349966380057068887203112818118009319763260369706420603369043739487038320775305138954954240502579841819390544496021506241529401550675934332753027002609183368959556072680739772971637818809562153595453738814985325162831406287568528704467227527998078273026861041585273041251233294998882760325361077824551101692792965149218232791987285655552,   box := { reLo := (56651844432289919206602598739260672698114566548178458882504052995941221240119909508891312961500461044648346519687761794827059618860023017162224651430020334088916581856683853113567303660691084387596620962717864578416364276848620637002023504152945532037540346488019204423128845665749373672345267839255382494724042766282085408356405813129251729358983517230973511104387002736051575198660693945425552750988583875086637199425304329301018045362322710472732170163331807038928278677968291597946805375467438474455161652925166530696600435841 : Rat)/22415066793529756433479306342575712442889166244056453499441757382261012231423266251224442181432804772090351062781089699687269885777697776648707696414517215646934876045227465997814869653175773085327825876369825430198317246110533271152944936110105601964251826755351793736218569030856190884872036726632877626376966157538126527407312383902397926958584676913897899528432981712909997190312999088222983641781612997907200757996829363152467966302898919589139657730101235849345917222862768375097354156387011795659660800019400294610554060800,            reHi := (234834751270254843352664336531424530774705824684814565529702756113660355805388544946491353291879296043922231923351730469887712960905912733025772554378854111699421130551703376103397815720677588187933557048639754905716993812695999621656898876218797201078135369575594961828388132523172459243379299735127483444672758530691526509917875824085474637333151478579001922707741854881512934486937797549980128323270548520743757114590578855008102056865332424264996287150552253656148260136413356225263942340356139584564110942733531901783488612989 : Rat)/67245200380589269300437919027727137328667498732169360498325272146783036694269798753673326544298414316271053188343269099061809657333093329946123089243551646940804628135682397993444608959527319255983477629109476290594951738331599813458834808330316805892755480266055381208655707092568572654616110179898632879130898472614379582221937151707193780875754030741693698585298945138729991570938997264668950925344838993721602273990488089457403898908696758767418973190303707548037751668588305125292062469161035386978982400058200883831662182400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (208471028145906771320396305802812901148271733905040211205810793335792600400201709753142449046605048031575350438045866962646391417727169599494951525581347555079841099002057755211422331404536876155537923900180477799227242265394894846978729940189178399531264666549575376841057116406291106836644482637086089989853656925721164166397724268485691272209812885470539638765344114003820159158876539181898106614747999959567522085557656132342387382690445691478999152749820753439820696098429449183431216852113720960915088653564453125 : Rat)/864293775363924331697948779751446399989623348158215035948082142613937318278364502233789753801231516619609131680378522671467741075971924810350180604332436841239665825450478870861052470699932760114137774406225636236018639526520739412841206738087478974076641550610277909908481005159683638781088992043012483058803101351868665506054005218366737919112145361479545943275637619124307190907477629970650325662812575137057408934455055996156546053722083170546082502466589997765520650722155649102203385585930298436465583974571311104, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N434.C434_e2
