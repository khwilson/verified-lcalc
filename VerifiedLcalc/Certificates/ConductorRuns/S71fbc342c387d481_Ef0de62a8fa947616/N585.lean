module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 18 }
def label : String := "585.a1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 18 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -2, 0, 2, -1, 0, -3, 0, 0, 2, 5, 0, 1, 6, 0, -4, -5, 0, 2, -2, 0, -10, 1, 0, 1, -2, 0, -6, -10, 0,                    -2, 8, 0, 10, 3, 0, -3, -4, 0, 0, 9, 0, -4, 10, 0, -2, -10, 0, 2, -2, 0, 2, -9, 0, -5, 0, 0, 20, 0,                    0, -11, 4, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((5445222531945245 : Rat)/4503599627370496, (30065987408815349 : Rat)/9007199254740992),   tail := (45910952496948910610732070658206939697265625 : Rat)/758099664288422762346786863870838534551109632,   box := { reLo := (912988750470327671718186131073147105979806489732415 : Rat)/794925113580897186450544382570228387205464333484032,            reHi := (5403194590061397564019702688710502408352927178248583 : Rat)/1589850227161794372901088765140456774410928666968064,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1713, a6 := -28022 }
def label : String := "585.b1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 2, 1, 2, 1, 1],                kodaira := -11 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1713, a6 := -28022 },   conductor := 585,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -2, 0, 2, -1, 0, 3, 0, 0, 2, 1, 0, -1, -6, 0, -4, 1, 0, -2, -2, 0, -2, 3, 0, 1, 2, 0, 6, 2, 0, -6,                    8, 0, -2, -3, 0, 11, 4, 0, 0, 5, 0, 4, 2, 0, -6, 10, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   geometricUpper := (6946559035146117 : Rat)/9007199254740992,   tail := (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/14082414927313998815657530824592819108889404290787435787904808516085922227625456391128326440123569968453419225781947255002193033556886383816104743610572031394351126655779467932343515021591320159539708204510469310677979422692526096454762770828177759532131992274143174060932900575468689502466747230645618410126697100718556424567041907134143825868231531538711713779298724577175537103238348379551611739780815961034128493170926218654510108531394871907109617804018717546496477037349444778172681965020676100642187533916336947768367130304633542169997409665737929569935987284883648664565172059240637422726604681584622071899727804586498738573881022560932892854474234013947922824086342347192627438399969864667183276995950784378022797834710615043022553938243953663401251122508695984330931475316736,   box := { reLo := (4823675958238310106187776693202893680095496080679495805364230770373948401168807932891222626152834026916026154462814761155096241180640153508466882928462837581604850822706725100472580035736780042652480342169196271632509841101190624863368781997679365032145508888750777144703755926135052753199642947479209229601084288379924154104643907354760750763357601375619611254829214982588698469741943088257223600930014652896411074584154813714586317017321798578157946513593285168471160242331528313915918208097634299729441284571695065500182303558328273877176556532602478653843114998693092322762980562320345418223485523345780644409132726315277859982234771828455371463483567824052913010668147273659138959912950307089548395202055928569541409713684835970920798889607533414439148544364663070683161062941071302790306776860533 : Rat)/7215944210814192328406649992630657643927942383114516720924445035263648267687486092397540968584198590543891741553732105554436147139652237127935297591342658795369788302210488864785782027745526587836694035553334769517839569852087825741408943317261271863451883468649064145528924163726204675870705969216368816111855467615236215584585938433829227752686838651128848706896095744694536185639020980445495836980008178815467699654448871994908162811355574643145128814167263301777393653827715241011696826709061655077560925294297399475570503063570365204520864112372103077439196532207667824785266550711284810363775037049077761600956027525769169868568168735828116952535190423968241673494540136966997139372562301433716864467988050080582570950703242855653213000671349633187611580496912529798955923162244958761731804364800,            reHi := (6341996364009213153570753752313667204000114895406546872181861455010648582995551796877213131370174380633594691420629740476377707532224360051883319799830819256951885891232260703438914877570044980042221866842565558423976181540669262373652712800498797301533284715531590479872278960040021786851712526800498528459004578502311764743097739452245939737122567700005341736253584420570733666735335546236582222819996800721994008907884850645220127859525959874114955999066899199813722846905201399333639914941371188172343662367966815492392563307030309496568079102936786389268175787455460318977988602094265824504378340171913708516137161512727596164296977679899341843749309585044530234110200044034374444716052969501609250465954582268383466135977242731490571870398074210134494001078800237003553083639084375355043125319 : Rat)/7801020768447775490169351343384494750192370143907585644242643281366106235337822802591936182253187665452855936814845519518309348259083499597767889287938009508507879245632960934903548138103271986850480038436037588667934670110365217017739398180822996609137171317458447724896134231055356406346709155909587909310114019043498611442795609117653219192093879622841998602049833237507606687177319978859995499437846679800505621248052834589089905742006026641237977096397041407326912058192124584877510082928715302786552351669510702135751895203859854275157690932294165489123455710494776026794882757525713308501378418431435417946979489217047751209262885119814180489227232890776477484858962310234591502024391677225639853478906000087116292919679181465571041081806864468310931438375040572755628025040264820282953302016,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/28164829854627997631315061649185638217778808581574871575809617032171844455250912782256652880247139936906838451563894510004386067113772767632209487221144062788702253311558935864687030043182640319079416409020938621355958845385052192909525541656355519064263984548286348121865801150937379004933494461291236820253394201437112849134083814268287651736463063077423427558597449154351074206476696759103223479561631922068256986341852437309020217062789743814219235608037435092992954074698889556345363930041352201284375067832673895536734260609267084339994819331475859139871974569767297329130344118481274845453209363169244143799455609172997477147762045121865785708948468027895845648172684694385254876799939729334366553991901568756045595669421230086045107876487907326802502245017391968661862950633472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -597, a6 := 8820 }
def label : String := "585.c1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 0],                kodaira := -7 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -597, a6 := 8820 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -2, 0, 2, 1, 0, -1, 0, 0, -2, -5, 0, -1, 2, 0, -4, 7, 0, -6, 2, 0, 10, -3, 0, 1, 2, 0, -2, -2, 0,                    2, 8, 0, -14, -1, 0, 7, 12, 0, 0, -9, 0, -8, -10, 0, 6, -10, 0, -6, -2, 0, -2, -5, 0, -5, 0, 0, 4, 0,                    0, 5, -4, 0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((12813619433843781 : Rat)/9007199254740992, (32739609210683459 : Rat)/9007199254740992),   tail := (45910952496948910610732070658206939697265625 : Rat)/758099664288422762346786863870838534551109632,   box := { reLo := (2165434764232861996609149671262710355313760303387127 : Rat)/1589850227161794372901088765140456774410928666968064,            reHi := (5875112453631183905154262509527904576185790718889953 : Rat)/1589850227161794372901088765140456774410928666968064,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3593, a6 := 83782 }
def label : String := "585.d1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3593, a6 := 83782 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -1, 0, -1, -1, 0, 2, 3, 0, 1, -4, 0, -1, -2, 0, -1, -4, 0, 6, 1, 0, 4, 0, 0, 1, 1, 0, -2, -4, 0,                    -10, -5, 0, 4, -2, 0, -2, -6, 0, -3, -6, 0, -8, 4, 0, 0, -8, 0, -3, -1, 0, 1, -4, 0, 4, 6, 0, 4, 12,                    0, 2, 10, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((16528411828980973 : Rat)/9007199254740992, (17796672899593849 : Rat)/4503599627370496),   tail := (45910952496948910610732070658206939697265625 : Rat)/758099664288422762346786863870838534551109632,   box := { reLo := (2821128433955904091049766685498800043539310619660591 : Rat)/1589850227161794372901088765140456774410928666968064,            reHi := (3189411083979171672456584374461114319025874489708083 : Rat)/794925113580897186450544382570228387205464333484032,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -218, a6 := 1432 }
def label : String := "585.d2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -218, a6 := 1432 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 32,   coefficients := [1, -1, 0, -1, -1, 0, 2, 3, 0, 1, -4, 0, -1, -2, 0, -1, -4, 0, 6, 1, 0, 4, 0, 0, 1, 1, 0, -2, -4, 0,                    -10, -5, 0, 4, -2, 0, -2, -6, 0, -3, -6, 0, -8, 4, 0, 0, -8, 0, -3, -1, 0, 1, -4, 0, 4, 6, 0, 4, 12,                    0, 2, 10, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((16528411828980973 : Rat)/9007199254740992, (17796672899593849 : Rat)/4503599627370496),   tail := (45910952496948910610732070658206939697265625 : Rat)/758099664288422762346786863870838534551109632,   box := { reLo := (2821128433955904091049766685498800043539310619660591 : Rat)/1589850227161794372901088765140456774410928666968064,            reHi := (3189411083979171672456584374461114319025874489708083 : Rat)/794925113580897186450544382570228387205464333484032,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -378, a6 := -2842 }
def label : String := "585.e1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -378, a6 := -2842 },   conductor := 585,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 0, -2, -1, 0, -1, 0, 0, 0, 3, 0, 1, 0, 0, 4, 3, 0, -4, 2, 0, 0, 9, 0, 1, 0, 0, 2, 6, 0, 2, 0,                    0, 0, 1, 0, -1, 0, 0, 0, 3, 0, 2, -6, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   geometricUpper := (6946559035146117 : Rat)/9007199254740992,   tail := (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/14082414927313998815657530824592819108889404290787435787904808516085922227625456391128326440123569968453419225781947255002193033556886383816104743610572031394351126655779467932343515021591320159539708204510469310677979422692526096454762770828177759532131992274143174060932900575468689502466747230645618410126697100718556424567041907134143825868231531538711713779298724577175537103238348379551611739780815961034128493170926218654510108531394871907109617804018717546496477037349444778172681965020676100642187533916336947768367130304633542169997409665737929569935987284883648664565172059240637422726604681584622071899727804586498738573881022560932892854474234013947922824086342347192627438399969864667183276995950784378022797834710615043022553938243953663401251122508695984330931475316736,   box := { reLo := (197005587335523917999820892348383779753484384404694237011284890881447042816195357783507627495206329498820104299004437996310612356842580873476719774650222925103521248873525507342819774136741998417952846394599285521783003467075985638797168131170915261914819386612965432640179634824717856856073402513520139708515440523134770632210920175248124372348544394806516846586737137231449138658232631386663719970661916584465293760549042259325140415008757896728082078810162070381178824130403956185473502431196793766469747150075791430294684476828611113035945342946111128966790053790174697101588070892415251397611359392694608359847345041191200360028626124382595957753250415270562844250477757429392777446495269252108692419704788656583465359611169486873502683224335924305171297571141783329004099983465706371373253861649 : Rat)/195025519211194387254233783584612368754809253597689641106066082034152655883445570064798404556329691636321398420371137987957733706477087489944197232198450237712696981140824023372588703452581799671262000960900939716698366752759130425443484954520574915228429282936461193122403355776383910158667728897739697732752850476087465286069890227941330479802346990571049965051245830937690167179432999471499887485946166995012640531201320864727247643550150666030949427409926035183172801454803114621937752073217882569663808791737767553393797380096496356878942273307354137228086392762369400669872068938142832712534460460785885448674487230426193780231572127995354512230680822269411937121474057755864787550609791930640996336972650002177907322991979536639276027045171611707773285959376014318890700626006620507073832550400,            reHi := (151488680179719864442641173594012040383195348494104850706093453819802493272773372842256611150445266328432767102917431723286719263900160081739844042421589464506459801711957973641298189095843467547144300456929239748316941525600137347432829815496194297598235834482551133158027842599552508934497655623813574186212128780017653716950514412434428364751229994705286107526544279044495655276403997953361741405444381144186731569213276011824537894387217156710241898073084118004317919583336754400090356502709122343482006642622615368621868490646669761866615489622844908338359281534157449820460756754632589285898770695050024524053999096810085990160349385028860709871006564280344797233611407914377201233088483222062636581137736160087857068734259699295761569572544476143319359416244909229878251550023819147677777991757 : Rat)/131198985651167133243757272593284684435053497874809394925899000641157241230681565316318926701530883464434395300976947373717020857084586129598823592569866523552177969131099797541559673231736847051576255191878813991233446724583415013480162605768386761153670608520892075373253166613203721379467381258479433020215553956640658465174289789705985959139760702747797249216292649903537021557073108735372651581454694160281230902808161308998330232933737720784456887530313878214134430069594822563849033212892030092319289550805407263192190964792188458264015711134038237771621755131048505905186664558386996552068637037255959301835564136832166724883057613378693035500639825890331666790809820672127220715864769116976670263054328183283319471830968051920967509103115447876138392372671136905435562239313544704758760079360,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/28164829854627997631315061649185638217778808581574871575809617032171844455250912782256652880247139936906838451563894510004386067113772767632209487221144062788702253311558935864687030043182640319079416409020938621355958845385052192909525541656355519064263984548286348121865801150937379004933494461291236820253394201437112849134083814268287651736463063077423427558597449154351074206476696759103223479561631922068256986341852437309020217062789743814219235608037435092992954074698889556345363930041352201284375067832673895536734260609267084339994819331475859139871974569767297329130344118481274845453209363169244143799455609172997477147762045121865785708948468027895845648172684694385254876799939729334366553991901568756045595669421230086045107876487907326802502245017391968661862950633472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 12, a6 := -21 }
def label : String := "585.e2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 12, a6 := -21 },   conductor := 585,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 0, 0, -2, -1, 0, -1, 0, 0, 0, 3, 0, 1, 0, 0, 4, 3, 0, -4, 2, 0, 0, 9, 0, 1, 0, 0, 2, 6, 0, 2, 0,                    0, 0, 1, 0, -1, 0, 0, 0, 3, 0, 2, -6, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   geometricUpper := (6946559035146117 : Rat)/9007199254740992,   tail := (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/14082414927313998815657530824592819108889404290787435787904808516085922227625456391128326440123569968453419225781947255002193033556886383816104743610572031394351126655779467932343515021591320159539708204510469310677979422692526096454762770828177759532131992274143174060932900575468689502466747230645618410126697100718556424567041907134143825868231531538711713779298724577175537103238348379551611739780815961034128493170926218654510108531394871907109617804018717546496477037349444778172681965020676100642187533916336947768367130304633542169997409665737929569935987284883648664565172059240637422726604681584622071899727804586498738573881022560932892854474234013947922824086342347192627438399969864667183276995950784378022797834710615043022553938243953663401251122508695984330931475316736,   box := { reLo := (197005587335523917999820892348383779753484384404694237011284890881447042816195357783507627495206329498820104299004437996310612356842580873476719774650222925103521248873525507342819774136741998417952846394599285521783003467075985638797168131170915261914819386612965432640179634824717856856073402513520139708515440523134770632210920175248124372348544394806516846586737137231449138658232631386663719970661916584465293760549042259325140415008757896728082078810162070381178824130403956185473502431196793766469747150075791430294684476828611113035945342946111128966790053790174697101588070892415251397611359392694608359847345041191200360028626124382595957753250415270562844250477757429392777446495269252108692419704788656583465359611169486873502683224335924305171297571141783329004099983465706371373253861649 : Rat)/195025519211194387254233783584612368754809253597689641106066082034152655883445570064798404556329691636321398420371137987957733706477087489944197232198450237712696981140824023372588703452581799671262000960900939716698366752759130425443484954520574915228429282936461193122403355776383910158667728897739697732752850476087465286069890227941330479802346990571049965051245830937690167179432999471499887485946166995012640531201320864727247643550150666030949427409926035183172801454803114621937752073217882569663808791737767553393797380096496356878942273307354137228086392762369400669872068938142832712534460460785885448674487230426193780231572127995354512230680822269411937121474057755864787550609791930640996336972650002177907322991979536639276027045171611707773285959376014318890700626006620507073832550400,            reHi := (151488680179719864442641173594012040383195348494104850706093453819802493272773372842256611150445266328432767102917431723286719263900160081739844042421589464506459801711957973641298189095843467547144300456929239748316941525600137347432829815496194297598235834482551133158027842599552508934497655623813574186212128780017653716950514412434428364751229994705286107526544279044495655276403997953361741405444381144186731569213276011824537894387217156710241898073084118004317919583336754400090356502709122343482006642622615368621868490646669761866615489622844908338359281534157449820460756754632589285898770695050024524053999096810085990160349385028860709871006564280344797233611407914377201233088483222062636581137736160087857068734259699295761569572544476143319359416244909229878251550023819147677777991757 : Rat)/131198985651167133243757272593284684435053497874809394925899000641157241230681565316318926701530883464434395300976947373717020857084586129598823592569866523552177969131099797541559673231736847051576255191878813991233446724583415013480162605768386761153670608520892075373253166613203721379467381258479433020215553956640658465174289789705985959139760702747797249216292649903537021557073108735372651581454694160281230902808161308998330232933737720784456887530313878214134430069594822563849033212892030092319289550805407263192190964792188458264015711134038237771621755131048505905186664558386996552068637037255959301835564136832166724883057613378693035500639825890331666790809820672127220715864769116976670263054328183283319471830968051920967509103115447876138392372671136905435562239313544704758760079360,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/28164829854627997631315061649185638217778808581574871575809617032171844455250912782256652880247139936906838451563894510004386067113772767632209487221144062788702253311558935864687030043182640319079416409020938621355958845385052192909525541656355519064263984548286348121865801150937379004933494461291236820253394201437112849134083814268287651736463063077423427558597449154351074206476696759103223479561631922068256986341852437309020217062789743814219235608037435092992954074698889556345363930041352201284375067832673895536734260609267084339994819331475859139871974569767297329130344118481274845453209363169244143799455609172997477147762045121865785708948468027895845648172684694385254876799939729334366553991901568756045595669421230086045107876487907326802502245017391968661862950633472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -42, a6 := 105 }
def label : String := "585.f1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -42, a6 := 105 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 1, 0, -1, 0, 0, 0, -3, 0, 1, 0, 0, 4, -3, 0, -4, -2, 0, 0, -9, 0, 1, 0, 0, 2, -6, 0, 2,                    0, 0, 0, -1, 0, -1, 0, 0, 0, -3, 0, 2, 6, 0, 0, -6, 0, -6, 0, 0, -2, 9, 0, -3, 0, 0, 0, -12, 0, 5, 0,                    0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((11371736595627647 : Rat)/4503599627370496, (41979275704880821 : Rat)/9007199254740992),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (115826829395413428691626821840726877312038475047 : Rat)/362856337637214809857998861508785756963336093696,            reHi := (4983077127563996991665754728028667704436173719021 : Rat)/725712675274429619715997723017571513926672187392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 108, a6 := 560 }
def label : String := "585.f2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 108, a6 := 560 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 1, 0, -1, 0, 0, 0, -3, 0, 1, 0, 0, 4, -3, 0, -4, -2, 0, 0, -9, 0, 1, 0, 0, 2, -6, 0, 2,                    0, 0, 0, -1, 0, -1, 0, 0, 0, -3, 0, 2, 6, 0, 0, -6, 0, -6, 0, 0, -2, 9, 0, -3, 0, 0, 0, -12, 0, 5, 0,                    0, -8],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((11371736595627647 : Rat)/4503599627370496, (41979275704880821 : Rat)/9007199254740992),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (115826829395413428691626821840726877312038475047 : Rat)/362856337637214809857998861508785756963336093696,            reHi := (4983077127563996991665754728028667704436173719021 : Rat)/725712675274429619715997723017571513926672187392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1170000, a6 := 487402461 }
def label : String := "585.g1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1170000, a6 := 487402461 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -73125, a6 := 7629336 }
def label : String := "585.g2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -73125, a6 := 7629336 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -71370, a6 := 8011575 }
def label : String := "585.g3"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -71370, a6 := 8011575 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4680, a6 := 114075 }
def label : String := "585.g4"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0, 1],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4680, a6 := 114075 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1035, a6 := -10584 }
def label : String := "585.g5"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0, 1, 2, 0, 2, 0],                kodaira := -12 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1035, a6 := -10584 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -990, a6 := -11745 }
def label : String := "585.g6"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2, 0, 2],                kodaira := -8 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -990, a6 := -11745 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1890, a6 := -61479 }
def label : String := "585.g7"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 2, 2, 1, 0, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0],                kodaira := -20 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1890, a6 := -61479 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g7

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 5445, a6 := 533250 }
def label : String := "585.g8"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 5445, a6 := 533250 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -1, 0, 0, -3, 0, -1, -4, 0, 1, 0, 0, -1, -2, 0, -4, 1, 0, -4, -8, 0, 1, 1, 0, 0, 2, 0,                    -8, 5, 0, -2, 0, 0, 6, -4, 0, 3, 6, 0, -4, 4, 0, -8, 8, 0, -7, 1, 0, -1, -6, 0, 4, 0, 0, 2, 12, 0,                    -2, -8, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((28438527710156539 : Rat)/9007199254740992, (13872955452353795 : Rat)/2251799813685248),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (690505865104586106835677596708798105838040630339 : Rat)/725712675274429619715997723017571513926672187392,            reHi := (1517946728674169327035228999564246895514152342795 : Rat)/181428168818607404928999430754392878481668046848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_g8

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -9, a6 := 0 }
def label : String := "585.h1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -9, a6 := 0 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 1, 0, -4, -3, 0, 1, -2, 0, -1, -4, 0, -1, -2, 0, -6, -1, 0, -2, 6, 0, 1, -1, 0, 4, -2,                    0, -10, 5, 0, -2, -4, 0, -2, -6, 0, -3, 6, 0, 10, 2, 0, 6, -4, 0, 9, 1, 0, 1, -2, 0, -2, 12, 0, -2,                    -6, 0, 2, -10, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((1803517477454047 : Rat)/562949953421312, (56779118161561223 : Rat)/9007199254740992),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (45260266254554864096029838046487313518167181447 : Rat)/45357042204651851232249857688598219620417011712,            reHi := (6175504757853660167148031244557678484553295267823 : Rat)/725712675274429619715997723017571513926672187392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 36, a6 := -27 }
def label : String := "585.h2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 36, a6 := -27 },   conductor := 585,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 1, 0, -4, -3, 0, 1, -2, 0, -1, -4, 0, -1, -2, 0, -6, -1, 0, -2, 6, 0, 1, -1, 0, 4, -2,                    0, -10, 5, 0, -2, -4, 0, -2, -6, 0, -3, 6, 0, 10, 2, 0, 6, -4, 0, 9, 1, 0, 1, -2, 0, -2, 12, 0, -2,                    -6, 0, 2, -10, 0, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   finite := ((1803517477454047 : Rat)/562949953421312, (56779118161561223 : Rat)/9007199254740992),   tail := (1526636715314561684488140439128875732421875 : Rat)/692093539499692554203031275765964044500992,   box := { reLo := (45260266254554864096029838046487313518167181447 : Rat)/45357042204651851232249857688598219620417011712,            reHi := (6175504757853660167148031244557678484553295267823 : Rat)/725712675274429619715997723017571513926672187392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_h2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -399, a6 := -2970 }
def label : String := "585.i1"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -399, a6 := -2970 },   conductor := 585,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, 0, -1, 1, 0, 2, -3, 0, 1, 4, 0, -1, 2, 0, -1, 4, 0, 6, -1, 0, 4, 0, 0, 1, -1, 0, -2, 4, 0, -10,                    5, 0, 4, 2, 0, -2, 6, 0, -3, 6, 0, -8, -4, 0, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   geometricUpper := (6946559035146117 : Rat)/9007199254740992,   tail := (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/14082414927313998815657530824592819108889404290787435787904808516085922227625456391128326440123569968453419225781947255002193033556886383816104743610572031394351126655779467932343515021591320159539708204510469310677979422692526096454762770828177759532131992274143174060932900575468689502466747230645618410126697100718556424567041907134143825868231531538711713779298724577175537103238348379551611739780815961034128493170926218654510108531394871907109617804018717546496477037349444778172681965020676100642187533916336947768367130304633542169997409665737929569935987284883648664565172059240637422726604681584622071899727804586498738573881022560932892854474234013947922824086342347192627438399969864667183276995950784378022797834710615043022553938243953663401251122508695984330931475316736,   box := { reLo := (17500759935217229939713526131963525078524115374834788245068862316473235210833378011284756269040145214288633470467616136638913501111425339897333633178422571568663290246798090538880513270637541836205364188452220573847710618074722111848348530469702742726672524974722773076466802322148866895333358137491050689871650146199441273562863513236394164116645393171733902929729436639723602533221288166131074354685512892043977494041948354869654352133125007190585718911895330007837866154945759257608753591584505245906131419727187315165661209633112284844250222202270862162811260160087590757346524984847986121540882600041908738957801179033761060649992306891335330325176496568034019234865483720431787502265108668254175066057045309220294082694628261868376636483367239048480944807353714353847424617087733549528996133143 : Rat)/8479370400486712489314512329765755163252576243377810482872438349310985038410676959339061067666508332013973844363962521215553639412047282171486836182541314683160738310470609711851682758807904333533130476560910422465146380554744801106238476283503257183844751432020051874887102425060170006898596908597378162293602194612498490698690879475710020860971608285697824567445470910334355094757956498760864673302007260652723501356579168031619462763050028957867366409127218921007513106730570200953815307531212285637556903988598589277991190438978102472997490143798005966438538815755191333472698649484470987501498280903734149942369010018530164357894440347624109227420905316061388570498872076341947284809121388288738971172723913138169883608346936375620696828050939639468403737364174535603943505478548717698862284800,            reHi := (1041897180996408852541443140049837914283795919578238121659230497555497281924507269603585140222656931435322191546854884426314430661888403801369899060001777295880866705546625033417915429587054748382666920191881877659407433263450610004399304900538902343682802492328592772616613344854373641817837032444365175003541098425255821493229432604328056058321921734804363968176385866907666627038612732456291311345088029541445512288178759772043240471303414833288486833575552242059696430304043900860672720906542527262279419167006739557919605536180976299086831590960489127572665662841555352569187023310286742379862866647734905186947024236018980662561814079275355893956047346596717156182811105620985124288536004308413738357234693160923758704488591245494143499172771148173712958536426629550526302640582962654298285621 : Rat)/471784518523320845270130761205011941414053114293201485513203336728581122437887289466985352637083922232356439460852050052594713771798119459165432990607561869589394462387086555396259040715627759910865906214667196437910400121091064121700486650360331602710159102232694615595222240191317729707139978373087206022350798797988637828348214346768828228354811288076420314278920937868227275948938933013762395356653035555113939173223201830330706950726091836753522642312341503875605992404558041256076941922789254990360308943726538050053645182319082393234446820030866497380790881478108389982691503805902897048955543448779193305064140407046039219912923748664800062277554130367325379110463559134815112087124047167944875087805691407687647659411784429921753056598322957383956298169134523033602871733392936172718653440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/28164829854627997631315061649185638217778808581574871575809617032171844455250912782256652880247139936906838451563894510004386067113772767632209487221144062788702253311558935864687030043182640319079416409020938621355958845385052192909525541656355519064263984548286348121865801150937379004933494461291236820253394201437112849134083814268287651736463063077423427558597449154351074206476696759103223479561631922068256986341852437309020217062789743814219235608037435092992954074698889556345363930041352201284375067832673895536734260609267084339994819331475859139871974569767297329130344118481274845453209363169244143799455609172997477147762045121865785708948468027895845648172684694385254876799939729334366553991901568756045595669421230086045107876487907326802502245017391968661862950633472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := -45 }
def label : String := "585.i2"
def inputConductor : Nat := 585
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 5, 5, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 585 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := -45 },   conductor := 585,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, 0, -1, 1, 0, 2, -3, 0, 1, 4, 0, -1, 2, 0, -1, 4, 0, 6, -1, 0, 4, 0, 0, 1, -1, 0, -2, 4, 0, -10,                    5, 0, 4, 2, 0, -2, 6, 0, -3, 6, 0, -8, -4, 0, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/20776280016518922328948974609375,   alphaHi := (2698607540904403791726115815424 : Rat)/10388140008259461116790771484375,   geometricUpper := (6946559035146117 : Rat)/9007199254740992,   tail := (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/14082414927313998815657530824592819108889404290787435787904808516085922227625456391128326440123569968453419225781947255002193033556886383816104743610572031394351126655779467932343515021591320159539708204510469310677979422692526096454762770828177759532131992274143174060932900575468689502466747230645618410126697100718556424567041907134143825868231531538711713779298724577175537103238348379551611739780815961034128493170926218654510108531394871907109617804018717546496477037349444778172681965020676100642187533916336947768367130304633542169997409665737929569935987284883648664565172059240637422726604681584622071899727804586498738573881022560932892854474234013947922824086342347192627438399969864667183276995950784378022797834710615043022553938243953663401251122508695984330931475316736,   box := { reLo := (17500759935217229939713526131963525078524115374834788245068862316473235210833378011284756269040145214288633470467616136638913501111425339897333633178422571568663290246798090538880513270637541836205364188452220573847710618074722111848348530469702742726672524974722773076466802322148866895333358137491050689871650146199441273562863513236394164116645393171733902929729436639723602533221288166131074354685512892043977494041948354869654352133125007190585718911895330007837866154945759257608753591584505245906131419727187315165661209633112284844250222202270862162811260160087590757346524984847986121540882600041908738957801179033761060649992306891335330325176496568034019234865483720431787502265108668254175066057045309220294082694628261868376636483367239048480944807353714353847424617087733549528996133143 : Rat)/8479370400486712489314512329765755163252576243377810482872438349310985038410676959339061067666508332013973844363962521215553639412047282171486836182541314683160738310470609711851682758807904333533130476560910422465146380554744801106238476283503257183844751432020051874887102425060170006898596908597378162293602194612498490698690879475710020860971608285697824567445470910334355094757956498760864673302007260652723501356579168031619462763050028957867366409127218921007513106730570200953815307531212285637556903988598589277991190438978102472997490143798005966438538815755191333472698649484470987501498280903734149942369010018530164357894440347624109227420905316061388570498872076341947284809121388288738971172723913138169883608346936375620696828050939639468403737364174535603943505478548717698862284800,            reHi := (1041897180996408852541443140049837914283795919578238121659230497555497281924507269603585140222656931435322191546854884426314430661888403801369899060001777295880866705546625033417915429587054748382666920191881877659407433263450610004399304900538902343682802492328592772616613344854373641817837032444365175003541098425255821493229432604328056058321921734804363968176385866907666627038612732456291311345088029541445512288178759772043240471303414833288486833575552242059696430304043900860672720906542527262279419167006739557919605536180976299086831590960489127572665662841555352569187023310286742379862866647734905186947024236018980662561814079275355893956047346596717156182811105620985124288536004308413738357234693160923758704488591245494143499172771148173712958536426629550526302640582962654298285621 : Rat)/471784518523320845270130761205011941414053114293201485513203336728581122437887289466985352637083922232356439460852050052594713771798119459165432990607561869589394462387086555396259040715627759910865906214667196437910400121091064121700486650360331602710159102232694615595222240191317729707139978373087206022350798797988637828348214346768828228354811288076420314278920937868227275948938933013762395356653035555113939173223201830330706950726091836753522642312341503875605992404558041256076941922789254990360308943726538050053645182319082393234446820030866497380790881478108389982691503805902897048955543448779193305064140407046039219912923748664800062277554130367325379110463559134815112087124047167944875087805691407687647659411784429921753056598322957383956298169134523033602871733392936172718653440,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1017422023908953725376629950918976873560869447976942425126341962936866051025639931347933740787254962620334654096700944974171994455247364898869906234274444064048259187809969520329552061944709785558716994250199076198370703257611922948020137793780777759169423017969026513214657155154306096279615839621230160778798732769628222887798101060120969199985249155493282011115688636087708944046001406307285178340485712157291565154203701299361342541706915024344206536258609569922415386357331014053934848322207391762371584081037668741750480004997103315017350011379870768048362747675445922724094781673089735675331235406855107832486005135329312397493168010616856573783709726164338596195971577142300412057963617239158274416677615040381949474139742585123154133273638355469998816215503770146730225067397 : Rat)/28164829854627997631315061649185638217778808581574871575809617032171844455250912782256652880247139936906838451563894510004386067113772767632209487221144062788702253311558935864687030043182640319079416409020938621355958845385052192909525541656355519064263984548286348121865801150937379004933494461291236820253394201437112849134083814268287651736463063077423427558597449154351074206476696759103223479561631922068256986341852437309020217062789743814219235608037435092992954074698889556345363930041352201284375067832673895536734260609267084339994819331475859139871974569767297329130344118481274845453209363169244143799455609172997477147762045121865785708948468027895845648172684694385254876799939729334366553991901568756045595669421230086045107876487907326802502245017391968661862950633472, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N585.C585_i2
