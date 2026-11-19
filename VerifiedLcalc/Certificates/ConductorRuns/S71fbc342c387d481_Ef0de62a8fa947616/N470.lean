module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -97, a6 := 281 }
def label : String := "470.a1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 5, 5, 5, 5, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -97, a6 := 281 },   conductor := 470,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 1, 1, -1, -1, -2, -1, 1, -1, -5, 1, -1, 1, 0, 2, 5, 1, 1, -1, -6, 1, 1, 5, 5, -1, -6,                    1, -11, -1, -1, 0, -1, -2, -8, -5, 5, -1, 2, -1, -2, 1, -2, 6, 1, -1, -6, -1, 0, -5, -6, -5, 1, 1,                    -5, 6, 8, -1, -5, 11, 2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   finite := ((13614521689349967 : Rat)/9007199254740992, (14324316270973375 : Rat)/4503599627370496),   tail := (81228967870568899980243375577983856201171875 : Rat)/70073569543483577457768093269928855851761664,   box := { reLo := (51775163396439107835414392624321756424065897074203 : Rat)/146954926515255671432713272337217839907233677180928,            reHi := (318879895333780495384591569265020937492198150572875 : Rat)/73477463257627835716356636168608919953616838590464,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -44, a6 := 106 }
def label : String := "470.b1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -44, a6 := 106 },   conductor := 470,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, -1, -1, -1, -1, -2, 1, -3, 1, -5, 1, -1, 1, 2, 2, -7, -1, -1, 3, 8, -1, 1, 5, -5, -1,                    -2, 1, -5, -1, -3, -2, 1, -2, -4, 7, -5, 1, 12, 1, 8, -3, 2, -8, -1, 1, -6, -1, 2, -5, -4, 5, 3, 1,                    -7, 2, -10, -1, -11, 5, 2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   finite := ((4137177487775189 : Rat)/2251799813685248, (8392184122650811 : Rat)/2251799813685248),   tail := (81228967870568899980243375577983856201171875 : Rat)/70073569543483577457768093269928855851761664,   box := { reLo := (24911812433637059190972476563072074213186149818201 : Rat)/36738731628813917858178318084304459976808419295232,            reHi := (179508159043519376342068878659427664623771955015799 : Rat)/36738731628813917858178318084304459976808419295232,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6348, a6 := 132618 }
def label : String := "470.c1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6348, a6 := 132618 },   conductor := 470,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, -1, -1, -2, -1, 3, 1, 5, 1, 1, 1, 6, 2, -1, 1, -1, -3, 0, -1, 1, -5, -5, -1, -6,                    -1, 5, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   geometricUpper := (6740960675210605 : Rat)/9007199254740992,   tail := (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/3551366778359133468553486652627270281841559615884982433267874476028082475488978295686787887317226520181362350480028277497005869650141310071706018395896557378186894022563797143001524654781344954464060529834451893131717001985043963428819820562235870895794581552515333598508998209911118588094046131443737351828933741945224920779518185413492664016482211605794872459493485849363439739090907943828148952022254493267341150936405316616981846564329259112121180599659797267237545496798792589483916653437166832718460869652357133853517676544,   box := { reLo := (2993955464261439616116533766282168629959075177389976364843163883267305697389080430363927012146500513399886664643236266253511416861891714178217734299928670661123386092577769608906346319078754466367824399551131394433029825916626569718864846067801736994493945408415890464094221149556077153085254074947251305613724037548601086794904757765630710433492157439978267743088711570780289178132104543030368388840711524865296420404854402137236830237331316845732480465935993660909107315525314718878726450292070170822540364453892785369886651028580142439 : Rat)/4872586466473063218711286125374008375928198479849163495518245897278490736054422913927385370029804997809573826034227583611684646868860668094918653430196328182532290303412786491143596349119816303155389633628965061582268077758567499326495201592266726907685976655318170239979318838366980168654803338335875121781843135298315025480142368794470012688313910628429116538804856218770870631782552721623560778940455261884793658546301177295042120442603371115871946978715526193799308637720630654949799232204961813740763218949775847734244213659585740800,            reHi := (47249059422616984984568134644981097963162819289761209831003983524831493768068080131481970097115459989410539644173508450925306775222252728211084093812384221606932168751054383960641866345238445973472698745828650765703682723462599541053161049600390860885276141022924875252277465168991335756913451079348126842148030126203934852115483271902872016608907790879989492102723729496893822746692901062704397039874745024372608005540971696645556058478130694986679567880910362677128432251895414339285861818957606035285354497331402659286581129676434485673 : Rat)/22476769829214452912119803739628490250249431697368721930939005268091102427605886344890842190782648860863517971706275627628093693620873404437850562597357255809745726238323498975275299287875281656490990890611032380847236616757262980764155284764327159606422408442274140139259438512467037552181834754259036852090437688634162859472914797987393929497706103866624634356422401267233370978867904490069973915757583949984693328132937688812613652364267163534506077998590975668171004361098393021220041619526114173062230332574772458903126533978089062400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/7102733556718266937106973305254540563683119231769964866535748952056164950977956591373575774634453040362724700960056554994011739300282620143412036791793114756373788045127594286003049309562689908928121059668903786263434003970087926857639641124471741791589163105030667197017996419822237176188092262887474703657867483890449841559036370826985328032964423211589744918986971698726879478181815887656297904044508986534682301872810633233963693128658518224242361199319594534475090993597585178967833306874333665436921739304714267707035353088, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5773, a6 := 168328 }
def label : String := "470.c2"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5773, a6 := 168328 },   conductor := 470,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 1, 1, 1, -1, -1, -1, -2, -1, 3, 1, 5, 1, 1, 1, 6, 2, -1, 1, -1, -3, 0, -1, 1, -5, -5, -1, -6,                    -1, 5, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   geometricUpper := (6740960675210605 : Rat)/9007199254740992,   tail := (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/3551366778359133468553486652627270281841559615884982433267874476028082475488978295686787887317226520181362350480028277497005869650141310071706018395896557378186894022563797143001524654781344954464060529834451893131717001985043963428819820562235870895794581552515333598508998209911118588094046131443737351828933741945224920779518185413492664016482211605794872459493485849363439739090907943828148952022254493267341150936405316616981846564329259112121180599659797267237545496798792589483916653437166832718460869652357133853517676544,   box := { reLo := (2993955464261439616116533766282168629959075177389976364843163883267305697389080430363927012146500513399886664643236266253511416861891714178217734299928670661123386092577769608906346319078754466367824399551131394433029825916626569718864846067801736994493945408415890464094221149556077153085254074947251305613724037548601086794904757765630710433492157439978267743088711570780289178132104543030368388840711524865296420404854402137236830237331316845732480465935993660909107315525314718878726450292070170822540364453892785369886651028580142439 : Rat)/4872586466473063218711286125374008375928198479849163495518245897278490736054422913927385370029804997809573826034227583611684646868860668094918653430196328182532290303412786491143596349119816303155389633628965061582268077758567499326495201592266726907685976655318170239979318838366980168654803338335875121781843135298315025480142368794470012688313910628429116538804856218770870631782552721623560778940455261884793658546301177295042120442603371115871946978715526193799308637720630654949799232204961813740763218949775847734244213659585740800,            reHi := (47249059422616984984568134644981097963162819289761209831003983524831493768068080131481970097115459989410539644173508450925306775222252728211084093812384221606932168751054383960641866345238445973472698745828650765703682723462599541053161049600390860885276141022924875252277465168991335756913451079348126842148030126203934852115483271902872016608907790879989492102723729496893822746692901062704397039874745024372608005540971696645556058478130694986679567880910362677128432251895414339285861818957606035285354497331402659286581129676434485673 : Rat)/22476769829214452912119803739628490250249431697368721930939005268091102427605886344890842190782648860863517971706275627628093693620873404437850562597357255809745726238323498975275299287875281656490990890611032380847236616757262980764155284764327159606422408442274140139259438512467037552181834754259036852090437688634162859472914797987393929497706103866624634356422401267233370978867904490069973915757583949984693328132937688812613652364267163534506077998590975668171004361098393021220041619526114173062230332574772458903126533978089062400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/7102733556718266937106973305254540563683119231769964866535748952056164950977956591373575774634453040362724700960056554994011739300282620143412036791793114756373788045127594286003049309562689908928121059668903786263434003970087926857639641124471741791589163105030667197017996419822237176188092262887474703657867483890449841559036370826985328032964423211589744918986971698726879478181815887656297904044508986534682301872810633233963693128658518224242361199319594534475090993597585178967833306874333665436921739304714267707035353088, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -117, a6 := 141 }
def label : String := "470.d1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -117, a6 := 141 },   conductor := 470,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -3, 1, 1, -3, -3, 1, 6, 1, -1, -3, -1, -3, -3, 1, -8, 6, -5, 1, 9, -1, -2, -3, 1, -1, -9, -3,                    -2, -3, -5, 1, 3, -8, -3, 6, -4, -5, 3, 1, 6, 9, 6, -1, 6, -2, -1, -3, 2, 1, 24, -1, 2, -9, -1, -3,                    15, -2, -12, -3, 11, -5, -18, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   finite := ((2399674049004707 : Rat)/1125899906842624, (19784446452011087 : Rat)/4503599627370496),   tail := (81228967870568899980243375577983856201171875 : Rat)/70073569543483577457768093269928855851761664,   box := { reLo := (17857653786481388774160062168218714280360334356863 : Rat)/18369365814406958929089159042152229988404209647616,            reHi := (407963416950756199501718954170502852456795329344283 : Rat)/73477463257627835716356636168608919953616838590464,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -11, a6 := 9 }
def label : String := "470.e1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -11, a6 := 9 },   conductor := 470,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -1, -1, -3, 1, -2, -1, -5, -1, -1, -3, 1, 1, 2, -2, -1, -1, 3, -5, 0, -1, 1, -1, 5, -3,                    2, 1, -7, 1, 5, 2, 3, -2, 0, -1, 1, -1, -8, 3, -4, -5, 2, 0, 1, -1, 2, 1, -2, -1, 12, 5, 5, -3, 1, 2,                    6, 1, -7, -7, 6, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   finite := ((22720961624960937 : Rat)/9007199254740992, (45910880062672477 : Rat)/9007199254740992),   tail := (81228967870568899980243375577983856201171875 : Rat)/70073569543483577457768093269928855851761664,   box := { reLo := (200349228841800631156794137500837211847563792367933 : Rat)/146954926515255671432713272337217839907233677180928,            reHi := (919398094001547820394432252185144255425901746961793 : Rat)/146954926515255671432713272337217839907233677180928,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -176, a6 := -844 }
def label : String := "470.f1"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 5, 47, 47, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -176, a6 := -844 },   conductor := 470,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 5, 1, -2, -1, -3, 1, 5, 5, -1, 1, 0, -2, -7, -1, 5, -3, 6, 1, 1, 5, -5, 5, -6, -1,                    5, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   geometricUpper := (6740960675210605 : Rat)/9007199254740992,   tail := (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/3551366778359133468553486652627270281841559615884982433267874476028082475488978295686787887317226520181362350480028277497005869650141310071706018395896557378186894022563797143001524654781344954464060529834451893131717001985043963428819820562235870895794581552515333598508998209911118588094046131443737351828933741945224920779518185413492664016482211605794872459493485849363439739090907943828148952022254493267341150936405316616981846564329259112121180599659797267237545496798792589483916653437166832718460869652357133853517676544,   box := { reLo := (254798405835632879034083440113311600124893038715811434781741045984579496597192694689132795698900930760442538300839006030164042312350711055633712982194798288798189964491581739324059496768283570234027773234887688318455348151491334733974158361110135874228787987177387487772013993074093789737697441667404907903056844227421701496469379812904065530253374064373252957289374945127043263247153326354882386024133277766591520898320788569006591759511168854480449700819487949754955439970269384900355377408174623316541736260340899345931605341456582204649 : Rat)/134671738556553822910432101397942130659057519329612594426550510555873580091453755999219920017042257460467969023752727079822107592871283507262079421276602717582762208469955082095557045313067864042672911806770303256672938720570827775502879983503909788230077119490264385876403190415033594745425614956190699794457832537782841334488976898865645980940037412242885414253186320197793222755737948751427658839791238288563750781166256908599945665006071324370612047168028282784923748819018102723780585501866549625154371656519434984856548056524180684800,            reHi := (718706892700605791245031730261433811936397549780979139851625520454032061673230149470292752897187772762199377881016402318580008337326128685793569161257932130335745083734855136717965415674078685496987430279541051196919602005031297529687328547963061688239884222134087960669591025706098666535376940034265042219937110854480635339867723047381841890708421663636074767677852655794320001661022388335384341791500262571705826495238591364123478045157939476669093669776463669952474272650900570783349443779816290460920872999607156394417306076180613969 : Rat)/212655576335636535161972639247821997431401451682221556730397828533975876526094358672352682183463975236470963944567807254399899199210237886495501003594906163564027850054068480638145571213957827272436359721947241776835229200089283651820473693780141781549862358771001737228698924634612037721177375297391134347215165297649422364408490478696034709357153594789126528259035470648444069318783135858333772135921197387761393067485630128626126698633543710939382885219083685877389181532399440348852717914068542155668982990217921248363599457628979200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/7102733556718266937106973305254540563683119231769964866535748952056164950977956591373575774634453040362724700960056554994011739300282620143412036791793114756373788045127594286003049309562689908928121059668903786263434003970087926857639641124471741791589163105030667197017996419822237176188092262887474703657867483890449841559036370826985328032964423211589744918986971698726879478181815887656297904044508986534682301872810633233963693128658518224242361199319594534475090993597585178967833306874333665436921739304714267707035353088, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -36, a6 := 80 }
def label : String := "470.f2"
def inputConductor : Nat := 470
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 47] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 470 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -36, a6 := 80 },   conductor := 470,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 5, 1, -2, -1, -3, 1, 5, 5, -1, 1, 0, -2, -7, -1, 5, -3, 6, 1, 1, 5, -5, 5, -6, -1,                    5, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/9311267214855070018768310546875,   alphaHi := (5397215081808807583452231630848 : Rat)/18622534429710139942169189453125,   geometricUpper := (6740960675210605 : Rat)/9007199254740992,   tail := (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/3551366778359133468553486652627270281841559615884982433267874476028082475488978295686787887317226520181362350480028277497005869650141310071706018395896557378186894022563797143001524654781344954464060529834451893131717001985043963428819820562235870895794581552515333598508998209911118588094046131443737351828933741945224920779518185413492664016482211605794872459493485849363439739090907943828148952022254493267341150936405316616981846564329259112121180599659797267237545496798792589483916653437166832718460869652357133853517676544,   box := { reLo := (254798405835632879034083440113311600124893038715811434781741045984579496597192694689132795698900930760442538300839006030164042312350711055633712982194798288798189964491581739324059496768283570234027773234887688318455348151491334733974158361110135874228787987177387487772013993074093789737697441667404907903056844227421701496469379812904065530253374064373252957289374945127043263247153326354882386024133277766591520898320788569006591759511168854480449700819487949754955439970269384900355377408174623316541736260340899345931605341456582204649 : Rat)/134671738556553822910432101397942130659057519329612594426550510555873580091453755999219920017042257460467969023752727079822107592871283507262079421276602717582762208469955082095557045313067864042672911806770303256672938720570827775502879983503909788230077119490264385876403190415033594745425614956190699794457832537782841334488976898865645980940037412242885414253186320197793222755737948751427658839791238288563750781166256908599945665006071324370612047168028282784923748819018102723780585501866549625154371656519434984856548056524180684800,            reHi := (718706892700605791245031730261433811936397549780979139851625520454032061673230149470292752897187772762199377881016402318580008337326128685793569161257932130335745083734855136717965415674078685496987430279541051196919602005031297529687328547963061688239884222134087960669591025706098666535376940034265042219937110854480635339867723047381841890708421663636074767677852655794320001661022388335384341791500262571705826495238591364123478045157939476669093669776463669952474272650900570783349443779816290460920872999607156394417306076180613969 : Rat)/212655576335636535161972639247821997431401451682221556730397828533975876526094358672352682183463975236470963944567807254399899199210237886495501003594906163564027850054068480638145571213957827272436359721947241776835229200089283651820473693780141781549862358771001737228698924634612037721177375297391134347215165297649422364408490478696034709357153594789126528259035470648444069318783135858333772135921197387761393067485630128626126698633543710939382885219083685877389181532399440348852717914068542155668982990217921248363599457628979200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2641648005869990719826046572343596393722836124756416289634829057189101818728116981286703461586056955669746063662401578277934836266103135735675770056049572225702160584002601591646947706094143560616961089921529825073790698737777895921171561416363396960353641958461370077481178757095229097007747691045339844358751880410372216587269446046816962544559337954716015358245079972444115340694071323399154907721094699973562462320701148112655339475396611320700734658329166021068437225331306080207763765495746194833689485676586627960205078125 : Rat)/7102733556718266937106973305254540563683119231769964866535748952056164950977956591373575774634453040362724700960056554994011739300282620143412036791793114756373788045127594286003049309562689908928121059668903786263434003970087926857639641124471741791589163105030667197017996419822237176188092262887474703657867483890449841559036370826985328032964423211589744918986971698726879478181815887656297904044508986534682301872810633233963693128658518224242361199319594534475090993597585178967833306874333665436921739304714267707035353088, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N470.C470_f2
