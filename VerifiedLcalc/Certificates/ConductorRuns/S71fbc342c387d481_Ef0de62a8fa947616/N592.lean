module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -29973, a6 := 2007325 }
def label : String := "592.a1"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -373, a6 := 2813 }
def label : String := "592.a2"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -53, a6 := -131 }
def label : String := "592.a3"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -1 }
def label : String := "592.b1"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -1 },   conductor := 592,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -4, 0, 3, 0, -2, 0, -5, 0, 0, 0, -4, 0, -6, 0, -2, 0, 3, 0, 6, 0, 11, 0, -5, 0, -6, 0,                    -4, 0, -5, 0, -12, 0, 1, 0, 0, 0, -9, 0, -4, 0, 8, 0, 7, 0, 2, 0, -6, 0, 9, 0, 20, 0, -2, 0, 4, 0,                    -8, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20900212909572050189971923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/5225053227393012523651123046875,   finite := ((25087990761150909 : Rat)/9007199254740992, (11968064399068949 : Rat)/2251799813685248),   tail := (1511101921424923995894277369606876373291015625 : Rat)/662034765082886508305606337763041239638212608,   box := { reLo := (349051082677197719011498081780304579843551349184741 : Rat)/694193765831552803333059471226218730894878423646208,            reHi := (1318516876555342815836656120598926708256423459880701 : Rat)/173548441457888200833264867806554682723719605911552,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := -13 }
def label : String := "592.c1"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := -13 },   conductor := 592,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -2, 0, -1, 0, -2, 0, -1, 0, -6, 0, -2, 0, -4, 0, 8, 0, -1, 0, -6, 0, -1, 0, -5, 0, 2, 0,                    4, 0, -1, 0, 2, 0, -1, 0, -6, 0, 7, 0, -2, 0, 4, 0, -9, 0, -6, 0, -4, 0, -3, 0, 2, 0, 8, 0, 12, 0, 4,                    0, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20900212909572050189971923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/5225053227393012523651123046875,   finite := ((25653485682447677 : Rat)/9007199254740992, (48764781612016455 : Rat)/9007199254740992),   tail := (1511101921424923995894277369606876373291015625 : Rat)/662034765082886508305606337763041239638212608,   box := { reLo := (392634336235954409208000425895854337009177893916773 : Rat)/694193765831552803333059471226218730894878423646208,            reHi := (5342855215925471147749303791405378716023625638655295 : Rat)/694193765831552803333059471226218730894878423646208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -33, a6 := -85 }
def label : String := "592.d1"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -33, a6 := -85 },   conductor := 592,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 1, 0, 0, 0, 3, 0, -2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 2, 0, 3, 0, 6, 0, -5, 0, -5, 0, -2, 0, 4, 0,                    3, 0, 0, 0, 1, 0, 0, 0, 7, 0, -4, 0, 0, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20900212909572050189971923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/5225053227393012523651123046875,   geometricUpper := (1739316966652483 : Rat)/2251799813685248,   tail := (3462121125245718267536937576092909006728007655862573398663625156792296718359827883290739344312339940477961013900849397313633235680621115816167158597937599039808575861545814219406773067073115103299372482166578069120481423274924986661265281015417690051238159681158604313378287276850105407723681288981288738974003930363625806309247222859925664843558261541392733087823422818636272775636346700721423746162834601026268979762577611274776276395892565717708109708861794517255654390939677530063405021351784655836206756006960740669713407262783134357368736685075741167698490226902235130788396934016414695628585057478413599741995056418578599171553351684404059066973195535276629985911057482620508299989716903744908254275802858398999691640747410030944470373289311960003 : Rat)/44156998145850593846693263321305842670903084812992564983383056954155363291374004130477360459076169216647873536867298338235400113641722290751036018908507702129191677752504519703207598464320829764472116373215188541384136960864289741748533266744680810494860981734139218106164537574155247798107854521132315967667257031704960787984066610795205641216804883351982285823679467486852447055479472614394969915109650901615956382823251746640724033570185575835996467274798774911095969072950923996990496906518776465916276906225481825214718149057006827044098419059000575253648195751450967654251604710258173049601225835636262601215249013058401006286767243464888255763413827491136025576106413351431185677871947108978222775601960973755593790390761517780763217693872639442944,   box := { reLo := (34041846872640901559317918700854047168258741315446131900403321427554970332098465057922345579292842813651582884484208021156521977656162940432507261044513052989932886171346088735652786334362097220694888748829525344177534858637710858300614385144528430489177798201606652154213167685490823197899231544766816106040081068788754295436287243445842977635298724899840735364008038437038588884075862182573298317486243259598330768214993471052823149471321477617749386477385074505121649725142411957816582612951337066780357828847850721319129292680651294750036945556560792633259671151352819480293479169455932593679918512048431393020760461665364421275614790028466651140606469096252909317253014214316571303732468885364538583840982542380827538886322622030884531957104355103676513229900253039 : Rat)/17834271121512363859045750513805115408133855322276885319428360939760405325414146171648903102493424534078042230766635635969439308324965138833790895991808927289603392696093847619063886058082668107886172605489836105905907344207474665274163879127618856169118764568812541531376455311799507229289452644238202976176516662258753492772065548321936603871250067618173036525331912050970834346042578503775201109407394907398246875266310710206006649423971016147826274340010785522160598807651528619499929704015107509149523136710156860868253211796511839709768609967659471390857692279171063670781848697080839648811153113919046274053575276186806639832205505998092340767969663099997110427189103194269524877700548083030240723223477166975534052939642597152865044347212652294319402999537991680,            reHi := (41750223172611947493167453942768792134379394212961626227994098255310412285785295135623160803535910386855120557895260647626292063719611611185529747342006871046661662292157937211330539962290104690801285735012334769017948177618297582896918305021124731184512184680984398358814137393596674673970778055214020689923110421914620085095100141923149700296378482133070474625804173519670705193075851275805116088129640930152281380083211229403923676053345336773189388956464926800973043929569279791245388856956237509232681137777564420949515875734362087857206024051363550583671995539892549540390906066114504906367973094551097722765487038828751797659968679502452273725201044808543160812811287922682861384455311472021473017474523143692675655534894547914131350696268829945696132334070674255 : Rat)/20212173937714012373585183915645797462551702698580470028685475731728459368802698994535423516159214471955114528202187054098697882768293824011629682124050117594883845055573027301605737532493690522270995619555147586693361656768471287310719063011301370325001266511320880402226649353372774859861379663469963373000052217226587291808340954764861484387416743300596108062042833657766945592181588970945227923995047561718013125301818804900140869347167151634203110918678890258448678648671732435433253664550455177036126221604844442317353640036046751671071091296680734242972051249727205493552761856691618268652640195774919110594051979678380858476499573464504652870365618179996725150814316953505461528060621160767606152986607455905605259998261610106580383593507672600228656732809723904,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3462121125245718267536937576092909006728007655862573398663625156792296718359827883290739344312339940477961013900849397313633235680621115816167158597937599039808575861545814219406773067073115103299372482166578069120481423274924986661265281015417690051238159681158604313378287276850105407723681288981288738974003930363625806309247222859925664843558261541392733087823422818636272775636346700721423746162834601026268979762577611274776276395892565717708109708861794517255654390939677530063405021351784655836206756006960740669713407262783134357368736685075741167698490226902235130788396934016414695628585057478413599741995056418578599171553351684404059066973195535276629985911057482620508299989716903744908254275802858398999691640747410030944470373289311960003 : Rat)/88313996291701187693386526642611685341806169625985129966766113908310726582748008260954720918152338433295747073734596676470800227283444581502072037817015404258383355505009039406415196928641659528944232746430377082768273921728579483497066533489361620989721963468278436212329075148310495596215709042264631935334514063409921575968133221590411282433609766703964571647358934973704894110958945228789939830219301803231912765646503493281448067140371151671992934549597549822191938145901847993980993813037552931832553812450963650429436298114013654088196838118001150507296391502901935308503209420516346099202451671272525202430498026116802012573534486929776511526827654982272051152212826702862371355743894217956445551203921947511187580781523035561526435387745278885888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -16, a6 := -16 }
def label : String := "592.e1"
def inputConductor : Nat := 592
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1.nonsingular
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 592 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N592.C592_e1
