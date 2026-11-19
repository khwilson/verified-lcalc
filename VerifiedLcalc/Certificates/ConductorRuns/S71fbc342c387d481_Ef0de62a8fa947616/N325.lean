module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -12708, a6 := -547182 }
def label : String := "325.a1"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -12708, a6 := -547182 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -2, -1, 2, 0, 2, -2, 0, -2, 0, 2, -2, 1, 4, 0, -4, -2, 4, 0, 0, 2, -4, 9, 0, 0, -2, 5, -4, 5, 0,                    2, 8],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (380633746707911480574380347134431832197053867523384102822985377837860409594841212414994574668750442715101183012678691587528777116889643468613968691601246155827428276246371395751650501290696869694352148703513020021984810624756725430653014318221253582885356219820292445359899166737209615300830517041922695343595316780923782097870460118263093305863661367052309691765494599617386365213930758771167617341466640516471802116845705455813883870552182695521174095775991120679799399366459495891484633041033009268773370422422885894775390625 : Rat)/4333938607859441266356112284554359142962929148368806432296904468530438712156148359592622031373087668462056857141386412048450323290965572131491883519849853930612343670989970162774091496736986805145589709054069836895663352807552995800011210584546642922259252119659775505124508756451290004913821456328926265313361266947283622956052965278567737761627760568211025069179849492389494824220219640291516529610112840031503454221597219122534911302534324849272887598048596396233431206278132414132020484604080253831962185971711954158002110464,   box := { reLo := (2128229302858588729001627754234985828222086496752531615191095393834652884711089612518882158087638287281098296370252143954659500146689134360617431164144893071271838498441463191148717889808598510293282392238667123111361112425550042147722031941843909228687946166597955350901889934670972587175380603940632695131149322386325445885251731913728880071409002671640356037411368697808468522682665581597324270052257991798934094275264630577242789792869558777027847326537157617098527953104940652894011087329481425862499542188963343966612452987037062567 : Rat)/5881918543210958417108998368574305778245282927635941182391785260911479353688472132959417936613687441431489924199875673363484216026869990773557089249414741800746366856493057822135660931924299491769985340227003839422098193530118393708571968939084110206774210397305153276226961072048216320080131772356209458955566453857402068142626255262093802427741620222234747643834473640465728632540112041366969670177750376700692899831010528637553002293121239192683667967718213776755005892936101000537010152086127888990630315866928450052617257613615169536,            reHi := (2458869360934248935167525259039056128529704561044942968201165861776786546767437059704673327989367601310118252939357388942269256055210571933792660099207636231201939591944003522835070793758901610938962645163919496176454469205890111682430943671548163684432188586967115803677066369506083010945076255831990973878800655641357427436008994726530487940011892102946606663121068726047387785213992998084474362338686358240147614208157189859781400225710175159458778509918040527919473187466110628258409356000218051389976672916408994909827586059990553271 : Rat)/4574825533608523213306998731113348938635220054827954252971388536264483941757700547857325061810645787780047718822125523727154390243121103934988847193989243622802729777272378306105514058163344049154433042398780763994965261634536528440000420285954307938602163642348452548176525278259723804506769156277051801409885019666868275222042642981628512999354593506182581500760146164806677825308976032174309743471583626322761144313008188940319001783538741594309519530447499604142782361172523000417674562733655024770490245674277683374257867032811798528,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (380633746707911480574380347134431832197053867523384102822985377837860409594841212414994574668750442715101183012678691587528777116889643468613968691601246155827428276246371395751650501290696869694352148703513020021984810624756725430653014318221253582885356219820292445359899166737209615300830517041922695343595316780923782097870460118263093305863661367052309691765494599617386365213930758771167617341466640516471802116845705455813883870552182695521174095775991120679799399366459495891484633041033009268773370422422885894775390625 : Rat)/8667877215718882532712224569108718285925858296737612864593808937060877424312296719185244062746175336924113714282772824096900646581931144262983767039699707861224687341979940325548182993473973610291179418108139673791326705615105991600022421169093285844518504239319551010249017512902580009827642912657852530626722533894567245912105930557135475523255521136422050138359698984778989648440439280583033059220225680063006908443194438245069822605068649698545775196097192792466862412556264828264040969208160507663924371943423908316004220928, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -98, a6 := 378 }
def label : String := "325.a2"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -98, a6 := 378 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -2, -1, 2, 0, 2, -2, 0, -2, 0, 2, -2, 1, 4, 0, -4, -2, 4, 0, 0, 2, -4, 9, 0, 0, -2, 5, -4, 5, 0,                    2, 8],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (380633746707911480574380347134431832197053867523384102822985377837860409594841212414994574668750442715101183012678691587528777116889643468613968691601246155827428276246371395751650501290696869694352148703513020021984810624756725430653014318221253582885356219820292445359899166737209615300830517041922695343595316780923782097870460118263093305863661367052309691765494599617386365213930758771167617341466640516471802116845705455813883870552182695521174095775991120679799399366459495891484633041033009268773370422422885894775390625 : Rat)/4333938607859441266356112284554359142962929148368806432296904468530438712156148359592622031373087668462056857141386412048450323290965572131491883519849853930612343670989970162774091496736986805145589709054069836895663352807552995800011210584546642922259252119659775505124508756451290004913821456328926265313361266947283622956052965278567737761627760568211025069179849492389494824220219640291516529610112840031503454221597219122534911302534324849272887598048596396233431206278132414132020484604080253831962185971711954158002110464,   box := { reLo := (2128229302858588729001627754234985828222086496752531615191095393834652884711089612518882158087638287281098296370252143954659500146689134360617431164144893071271838498441463191148717889808598510293282392238667123111361112425550042147722031941843909228687946166597955350901889934670972587175380603940632695131149322386325445885251731913728880071409002671640356037411368697808468522682665581597324270052257991798934094275264630577242789792869558777027847326537157617098527953104940652894011087329481425862499542188963343966612452987037062567 : Rat)/5881918543210958417108998368574305778245282927635941182391785260911479353688472132959417936613687441431489924199875673363484216026869990773557089249414741800746366856493057822135660931924299491769985340227003839422098193530118393708571968939084110206774210397305153276226961072048216320080131772356209458955566453857402068142626255262093802427741620222234747643834473640465728632540112041366969670177750376700692899831010528637553002293121239192683667967718213776755005892936101000537010152086127888990630315866928450052617257613615169536,            reHi := (2458869360934248935167525259039056128529704561044942968201165861776786546767437059704673327989367601310118252939357388942269256055210571933792660099207636231201939591944003522835070793758901610938962645163919496176454469205890111682430943671548163684432188586967115803677066369506083010945076255831990973878800655641357427436008994726530487940011892102946606663121068726047387785213992998084474362338686358240147614208157189859781400225710175159458778509918040527919473187466110628258409356000218051389976672916408994909827586059990553271 : Rat)/4574825533608523213306998731113348938635220054827954252971388536264483941757700547857325061810645787780047718822125523727154390243121103934988847193989243622802729777272378306105514058163344049154433042398780763994965261634536528440000420285954307938602163642348452548176525278259723804506769156277051801409885019666868275222042642981628512999354593506182581500760146164806677825308976032174309743471583626322761144313008188940319001783538741594309519530447499604142782361172523000417674562733655024770490245674277683374257867032811798528,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (380633746707911480574380347134431832197053867523384102822985377837860409594841212414994574668750442715101183012678691587528777116889643468613968691601246155827428276246371395751650501290696869694352148703513020021984810624756725430653014318221253582885356219820292445359899166737209615300830517041922695343595316780923782097870460118263093305863661367052309691765494599617386365213930758771167617341466640516471802116845705455813883870552182695521174095775991120679799399366459495891484633041033009268773370422422885894775390625 : Rat)/8667877215718882532712224569108718285925858296737612864593808937060877424312296719185244062746175336924113714282772824096900646581931144262983767039699707861224687341979940325548182993473973610291179418108139673791326705615105991600022421169093285844518504239319551010249017512902580009827642912657852530626722533894567245912105930557135475523255521136422050138359698984778989648440439280583033059220225680063006908443194438245069822605068649698545775196097192792466862412556264828264040969208160507663924371943423908316004220928, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -53, a6 := -132 }
def label : String := "325.b1"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -53, a6 := -132 },   conductor := 325,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, 4, 0, -2, 0, -6, 2, -1, 0, 0, 4, -6, 0, -4, 0, -4, 0, -3, 0, 0, 0, 5, -8, -3, 0,                    -4, 0, 6, 0, 0, 4, -2, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   finite := ((10364036997204173 : Rat)/9007199254740992, (26766646002956859 : Rat)/9007199254740992),   tail := (66009715469226599909550971116733551025390625 : Rat)/184146058349911111950051069459326854699679744,   box := { reLo := (611848152078555164549489212286780637188555362062569 : Rat)/772364549121265576496547000837532463974285548978176,            reHi := (2572096426352854611690660756987764199326094130649727 : Rat)/772364549121265576496547000837532463974285548978176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3, a6 := 3 }
def label : String := "325.b2"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3, a6 := 3 },   conductor := 325,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, -2, 0, 0, 4, 0, -2, 0, -6, 2, -1, 0, 0, 4, -6, 0, -4, 0, -4, 0, -3, 0, 0, 0, 5, -8, -3, 0,                    -4, 0, 6, 0, 0, 4, -2, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   finite := ((10364036997204173 : Rat)/9007199254740992, (26766646002956859 : Rat)/9007199254740992),   tail := (66009715469226599909550971116733551025390625 : Rat)/184146058349911111950051069459326854699679744,   box := { reLo := (611848152078555164549489212286780637188555362062569 : Rat)/772364549121265576496547000837532463974285548978176,            reHi := (2572096426352854611690660756987764199326094130649727 : Rat)/772364549121265576496547000837532463974285548978176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1333, a6 := -19131 }
def label : String := "325.c1"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1333, a6 := -19131 },   conductor := 325,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, 0, 0, -4, 0, -2, 0, -6, -2, 1, 0, 0, 4, 6, 0, -4, 0, -4, 0, 3, 0, 0, 0, -5, 8, -3, 0,                    -4, 0, -6, 0, 0, 4, 2, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   finite := ((12620151560189465 : Rat)/9007199254740992, (15190851495823849 : Rat)/4503599627370496),   tail := (66009715469226599909550971116733551025390625 : Rat)/184146058349911111950051069459326854699679744,   box := { reLo := (805309277776297282677050877318071484035238630728645 : Rat)/772364549121265576496547000837532463974285548978176,            reHi := (1441043222288067627224456583666801362476532713082197 : Rat)/386182274560632788248273500418766231987142774489088,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -83, a6 := 244 }
def label : String := "325.c2"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -83, a6 := 244 },   conductor := 325,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, 0, 0, -4, 0, -2, 0, -6, -2, 1, 0, 0, 4, 6, 0, -4, 0, -4, 0, 3, 0, 0, 0, -5, 8, -3, 0,                    -4, 0, -6, 0, 0, 4, 2, 0, 1, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   finite := ((12620151560189465 : Rat)/9007199254740992, (15190851495823849 : Rat)/4503599627370496),   tail := (66009715469226599909550971116733551025390625 : Rat)/184146058349911111950051069459326854699679744,   box := { reLo := (805309277776297282677050877318071484035238630728645 : Rat)/772364549121265576496547000837532463974285548978176,            reHi := (1441043222288067627224456583666801362476532713082197 : Rat)/386182274560632788248273500418766231987142774489088,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -25, a6 := 0 }
def label : String := "325.d1"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -25, a6 := 0 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, -1, 0, 2, 4, -3, 1, 0, 2, -2, 1, 4, 0, -1, -2, 1, -6, 0, 8, 2, 6, -6],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/10834241321428853029064396263206195564275810156173834690431430489921895929029041001882852997970646729756119959685163354830407387161571343304238863420817569753875039003536187161266097813001191217128296990601676857746526707319171598315391770303664909947850191316326724099383935195580983947357795135855941352079898401519938167038884157206143604896981836112593487601418551515583516165282793737991745437696,   box := { reLo := (1116010164269297587119988483181948896829642114978639385084045010303956227422230095086820960141892308378392471746895750399700409257794289092832469986665167882458473719696420380074113895618016455207393955858391346454122250495799250631107913553602174176484461317986222744050027104318026359854909441421413190425563716013534503348143169764196233522813078568958053527174655046591124024326801078559257154711041901007 : Rat)/725112597201046596918650873152783671064667987794790699998172809860654551594521521137316323731612726409222160561134216774383184181322831406249379361826462814845152821798248442799201978440947718614383480153707335102176312700245199367200374563427612883567234853242522021108918200402851907871993830119042558836155501111048610372173220468594927534584119646868437287692964218656312903801299844987981957801502048256,            reHi := (71974076025297465531695946861375690524845099699516678438132917715367447946458642560208718186817687732933394650318581388567505885170116266025531309059331659085132164353000579819459171455419071237093808188819999326110949482936565239277915886999044424896448350985988679765636405727075712499676091046851406859689854242487799189369713864243450353215940431705799639514667805711397470289498504929691441332765850641 : Rat)/21973109006092321118746996156144959729232363266508809090853721510928925805894591549615646173685234133612792744276794447708581338827964588068163010964438267116519782478734801296945514498210536927708590307688101063702312506068036344460617411012957966168704086461894606700270248497056118420363449397546744207156227306395412435520400620260452349532852110511164766293726188444130694054584843787514604781863698432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/21668482642857706058128792526412391128551620312347669380862860979843791858058082003765705995941293459512239919370326709660814774323142686608477726841635139507750078007072374322532195626002382434256593981203353715493053414638343196630783540607329819895700382632653448198767870391161967894715590271711882704159796803039876334077768314412287209793963672225186975202837103031167032330565587475983490875392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 100, a6 := 125 }
def label : String := "325.d2"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 100, a6 := 125 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, -1, 0, 2, 4, -3, 1, 0, 2, -2, 1, 4, 0, -1, -2, 1, -6, 0, 8, 2, 6, -6],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/10834241321428853029064396263206195564275810156173834690431430489921895929029041001882852997970646729756119959685163354830407387161571343304238863420817569753875039003536187161266097813001191217128296990601676857746526707319171598315391770303664909947850191316326724099383935195580983947357795135855941352079898401519938167038884157206143604896981836112593487601418551515583516165282793737991745437696,   box := { reLo := (1116010164269297587119988483181948896829642114978639385084045010303956227422230095086820960141892308378392471746895750399700409257794289092832469986665167882458473719696420380074113895618016455207393955858391346454122250495799250631107913553602174176484461317986222744050027104318026359854909441421413190425563716013534503348143169764196233522813078568958053527174655046591124024326801078559257154711041901007 : Rat)/725112597201046596918650873152783671064667987794790699998172809860654551594521521137316323731612726409222160561134216774383184181322831406249379361826462814845152821798248442799201978440947718614383480153707335102176312700245199367200374563427612883567234853242522021108918200402851907871993830119042558836155501111048610372173220468594927534584119646868437287692964218656312903801299844987981957801502048256,            reHi := (71974076025297465531695946861375690524845099699516678438132917715367447946458642560208718186817687732933394650318581388567505885170116266025531309059331659085132164353000579819459171455419071237093808188819999326110949482936565239277915886999044424896448350985988679765636405727075712499676091046851406859689854242487799189369713864243450353215940431705799639514667805711397470289498504929691441332765850641 : Rat)/21973109006092321118746996156144959729232363266508809090853721510928925805894591549615646173685234133612792744276794447708581338827964588068163010964438267116519782478734801296945514498210536927708590307688101063702312506068036344460617411012957966168704086461894606700270248497056118420363449397546744207156227306395412435520400620260452349532852110511164766293726188444130694054584843787514604781863698432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/21668482642857706058128792526412391128551620312347669380862860979843791858058082003765705995941293459512239919370326709660814774323142686608477726841635139507750078007072374322532195626002382434256593981203353715493053414638343196630783540607329819895700382632653448198767870391161967894715590271711882704159796803039876334077768314412287209793963672225186975202837103031167032330565587475983490875392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2458, a6 := 42369 }
def label : String := "325.e1"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2458, a6 := 42369 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 1, 2, 0, 2, 2, 0, -2, 0, 2, 2, -1, 4, 0, -4, 2, -4, 0, 0, 2, 4, -9, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/10834241321428853029064396263206195564275810156173834690431430489921895929029041001882852997970646729756119959685163354830407387161571343304238863420817569753875039003536187161266097813001191217128296990601676857746526707319171598315391770303664909947850191316326724099383935195580983947357795135855941352079898401519938167038884157206143604896981836112593487601418551515583516165282793737991745437696,   box := { reLo := (81981635963960802562821759216139210454040941915290613755998826435294615634758753455609961945924523984242289937212383891544915999401188611076197221483417068956980356867358998796889603505996181932755798769840692119240717492228255148863824315889092103069475713317179208687002350306524989781091476072572343141351003229664632120824456521995906269512074522121427582504859942533895182977958416139266540891094648533 : Rat)/38163820905318241943086888060672824792877262515515299999903832097929186926027448480911385459558564547853797924270221935493851799016991126644704176938234884991850148515697286463115893602155143084967551587037228163272437510539221019326335503338295414924591308065395895847837800021202731993262833164160134675587131637423611072219643182557627764978111560361496699352261274666121731779015781315156945147447476224,            reHi := (148251864625303897013421037075149094123119233695235603705589648292879667222740613771913485812951055700030597448672162141960551108824321061587681881558651653846510356660286503684404492648128560542255873166928584403345959174251690097773634524829274186074980956035539563531015844271320273359612772294207471423728963853045128429049641318169628750243984832609761438603717722815300507422646243941833600313929759019 : Rat)/38163820905318241943086888060672824792877262515515299999903832097929186926027448480911385459558564547853797924270221935493851799016991126644704176938234884991850148515697286463115893602155143084967551587037228163272437510539221019326335503338295414924591308065395895847837800021202731993262833164160134675587131637423611072219643182557627764978111560361496699352261274666121731779015781315156945147447476224,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/21668482642857706058128792526412391128551620312347669380862860979843791858058082003765705995941293459512239919370326709660814774323142686608477726841635139507750078007072374322532195626002382434256593981203353715493053414638343196630783540607329819895700382632653448198767870391161967894715590271711882704159796803039876334077768314412287209793963672225186975202837103031167032330565587475983490875392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -508, a6 := -4581 }
def label : String := "325.e2"
def inputConductor : Nat := 325
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 325 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -508, a6 := -4581 },   conductor := 325,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 1, 2, 0, 2, 2, 0, -2, 0, 2, 2, -1, 4, 0, -4, 2, -4, 0, 0, 2, 4, -9, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3871431203042230319976806640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15485724812168921184539794921875,   geometricUpper := (6356613471384865 : Rat)/9007199254740992,   tail := (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/10834241321428853029064396263206195564275810156173834690431430489921895929029041001882852997970646729756119959685163354830407387161571343304238863420817569753875039003536187161266097813001191217128296990601676857746526707319171598315391770303664909947850191316326724099383935195580983947357795135855941352079898401519938167038884157206143604896981836112593487601418551515583516165282793737991745437696,   box := { reLo := (81981635963960802562821759216139210454040941915290613755998826435294615634758753455609961945924523984242289937212383891544915999401188611076197221483417068956980356867358998796889603505996181932755798769840692119240717492228255148863824315889092103069475713317179208687002350306524989781091476072572343141351003229664632120824456521995906269512074522121427582504859942533895182977958416139266540891094648533 : Rat)/38163820905318241943086888060672824792877262515515299999903832097929186926027448480911385459558564547853797924270221935493851799016991126644704176938234884991850148515697286463115893602155143084967551587037228163272437510539221019326335503338295414924591308065395895847837800021202731993262833164160134675587131637423611072219643182557627764978111560361496699352261274666121731779015781315156945147447476224,            reHi := (148251864625303897013421037075149094123119233695235603705589648292879667222740613771913485812951055700030597448672162141960551108824321061587681881558651653846510356660286503684404492648128560542255873166928584403345959174251690097773634524829274186074980956035539563531015844271320273359612772294207471423728963853045128429049641318169628750243984832609761438603717722815300507422646243941833600313929759019 : Rat)/38163820905318241943086888060672824792877262515515299999903832097929186926027448480911385459558564547853797924270221935493851799016991126644704176938234884991850148515697286463115893602155143084967551587037228163272437510539221019326335503338295414924591308065395895847837800021202731993262833164160134675587131637423611072219643182557627764978111560361496699352261274666121731779015781315156945147447476224,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (9406653116894901167364993000460737214595625518165065427404883896516713486312078873540333314158038059218194783647454602283999321230195607957531759194932165898838672519954997833553251347652253560941958101528027582097152750399340942646844389959368939264889141080275926452327411770023552045095051243911221267802534961879596304228330715484572538230143637293404675562458510677564509515650570392608642578125 : Rat)/21668482642857706058128792526412391128551620312347669380862860979843791858058082003765705995941293459512239919370326709660814774323142686608477726841635139507750078007072374322532195626002382434256593981203353715493053414638343196630783540607329819895700382632653448198767870391161967894715590271711882704159796803039876334077768314412287209793963672225186975202837103031167032330565587475983490875392, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N325.C325_e2
