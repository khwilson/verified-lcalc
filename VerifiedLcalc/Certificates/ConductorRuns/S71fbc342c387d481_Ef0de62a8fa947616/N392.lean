module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := 7 }
def label : String := "392.a1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := 7 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -3, 0, 1, 0, 0, 0, 6, 0, -1, 0, -2, 0, -3, 0, -3, 0, -5, 0, 0, 0, -3, 0, -4, 0, -9, 0, -6, 0,                    1, 0, 3, 0, 0, 0, -5, 0, 6, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((206522958953099 : Rat)/281474976710656, (31607604410422679 : Rat)/9007199254740992),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (212851493746619204718100389201362909598590170269 : Rat)/2956092476866578361913624242544707692652329435136,            reHi := (394542484663232442407320584063354785055123462291249 : Rat)/94594959259730507581235975761430646164874541924352,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1976, a6 := 32752 }
def label : String := "392.b1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1976, a6 := 32752 },   conductor := 392,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, -2, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8, 0, 2, 0, 2, 0, 0, 0, 8, 0, 11, 0, 4, 0, 2, 0, -4, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   geometricUpper := (6557932551624643 : Rat)/9007199254740992,   tail := (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/3924031525491300136655458366938936403852593478855257948421937809420266808949417934054130839301181742736915896127839081851452458244239521152629976889442378293017895248354486002493260235722845523754956830347097400149517582317806824102294872345862949215200943738068884916577209001918742824657491068593706630657336178515212055113216771852747396708291308958102541185921569150895404861557667619070212602563894403414965311528952427725523309178077009352454106202298941431559205589915813275053926749635163994814643631042631349675113840640,   box := { reLo := (3550519205542923036169816640535984942853840265212144882097077047471740958211667381658373892536756757451310936782664469956878526836804827372425894310816796541257751611990427340831275655100047293539175428292836946152247903879674741261790069708561230324566144758874457382156086290313726909100675465177747080827350006266854979106110631098953504733095289641894082640795679306193749200822708728536695442227271910335201053978568956688037499401840196613284087926220962080266452458711028105153807256811855774053641952876647223273937155060927042309 : Rat)/3537987599571908441621874316242628499719371586172662801782087394563119471141057433111376868997272474077777611362581507764769448501859309941754114051595517440342096129290091956942284752289669878992575574027295710974787130037166644664103202646977274601234765785669754788782019377977243028032239521897732899651646379814549924530230747069685641677356684333220153674037198941948268205089468289941642242798030971885227021935441332323056545452273662347410142419768899918403148406115165665804887342553205097575715957187181437433415700939433574400,            reHi := (1094207792912517246398492174999485879308298050161504542787920241433017941692427770182118868417372971764062780512931535578889128466830342216450840384276057086364698176870017510680709750195375588816516351803605191731508782790845649143185418926075289239522223306322275582809028820633655352958826254141848903057098496576231741714410361375021738160576919431259212262276577906840191982064439407704546414624483853640939868748001496578636056974559087750803535159703241415841682686378493509167341333808184326700571160411230572052510965991146309887 : Rat)/707597519914381688324374863248525699943874317234532560356417478912623894228211486622275373799454494815555522272516301552953889700371861988350822810319103488068419225858018391388456950457933975798515114805459142194957426007433328932820640529395454920246953157133950957756403875595448605606447904379546579930329275962909984906046149413937128335471336866644030734807439788389653641017893657988328448559606194377045404387088266464611309090454732469482028483953779983680629681223033133160977468510641019515143191437436287486683140187886714880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/7848063050982600273310916733877872807705186957710515896843875618840533617898835868108261678602363485473831792255678163702904916488479042305259953778884756586035790496708972004986520471445691047509913660694194800299035164635613648204589744691725898430401887476137769833154418003837485649314982137187413261314672357030424110226433543705494793416582617916205082371843138301790809723115335238140425205127788806829930623057904855451046618356154018704908212404597882863118411179831626550107853499270327989629287262085262699350227681280, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := 1392 }
def label : String := "392.b2"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := 1392 },   conductor := 392,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, -2, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, -8, 0, 2, 0, 2, 0, 0, 0, 8, 0, 11, 0, 4, 0, 2, 0, -4, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   geometricUpper := (6557932551624643 : Rat)/9007199254740992,   tail := (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/3924031525491300136655458366938936403852593478855257948421937809420266808949417934054130839301181742736915896127839081851452458244239521152629976889442378293017895248354486002493260235722845523754956830347097400149517582317806824102294872345862949215200943738068884916577209001918742824657491068593706630657336178515212055113216771852747396708291308958102541185921569150895404861557667619070212602563894403414965311528952427725523309178077009352454106202298941431559205589915813275053926749635163994814643631042631349675113840640,   box := { reLo := (3550519205542923036169816640535984942853840265212144882097077047471740958211667381658373892536756757451310936782664469956878526836804827372425894310816796541257751611990427340831275655100047293539175428292836946152247903879674741261790069708561230324566144758874457382156086290313726909100675465177747080827350006266854979106110631098953504733095289641894082640795679306193749200822708728536695442227271910335201053978568956688037499401840196613284087926220962080266452458711028105153807256811855774053641952876647223273937155060927042309 : Rat)/3537987599571908441621874316242628499719371586172662801782087394563119471141057433111376868997272474077777611362581507764769448501859309941754114051595517440342096129290091956942284752289669878992575574027295710974787130037166644664103202646977274601234765785669754788782019377977243028032239521897732899651646379814549924530230747069685641677356684333220153674037198941948268205089468289941642242798030971885227021935441332323056545452273662347410142419768899918403148406115165665804887342553205097575715957187181437433415700939433574400,            reHi := (1094207792912517246398492174999485879308298050161504542787920241433017941692427770182118868417372971764062780512931535578889128466830342216450840384276057086364698176870017510680709750195375588816516351803605191731508782790845649143185418926075289239522223306322275582809028820633655352958826254141848903057098496576231741714410361375021738160576919431259212262276577906840191982064439407704546414624483853640939868748001496578636056974559087750803535159703241415841682686378493509167341333808184326700571160411230572052510965991146309887 : Rat)/707597519914381688324374863248525699943874317234532560356417478912623894228211486622275373799454494815555522272516301552953889700371861988350822810319103488068419225858018391388456950457933975798515114805459142194957426007433328932820640529395454920246953157133950957756403875595448605606447904379546579930329275962909984906046149413937128335471336866644030734807439788389653641017893657988328448559606194377045404387088266464611309090454732469482028483953779983680629681223033133160977468510641019515143191437436287486683140187886714880,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/7848063050982600273310916733877872807705186957710515896843875618840533617898835868108261678602363485473831792255678163702904916488479042305259953778884756586035790496708972004986520471445691047509913660694194800299035164635613648204589744691725898430401887476137769833154418003837485649314982137187413261314672357030424110226433543705494793416582617916205082371843138301790809723115335238140425205127788806829930623057904855451046618356154018704908212404597882863118411179831626550107853499270327989629287262085262699350227681280, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 29 }
def label : String := "392.c1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 29 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, -1, 0, 0, 0, -2, 0, 3, 0, -6, 0, 1, 0, -5, 0, 1, 0, 0, 0, -7, 0, -4, 0, 5, 0, 2, 0, -5,                    0, -3, 0, 0, 0, 3, 0, 6, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((10841635979262523 : Rat)/9007199254740992, (4300943040148361 : Rat)/1125899906842624),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (51265812866680075829091665219233282941405912821613 : Rat)/94594959259730507581235975761430646164874541924352,            reHi := (52993484262058858987287277425694968385856681442991 : Rat)/11824369907466313447654496970178830770609317740544,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -14651, a6 := -682570 }
def label : String := "392.d1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -14651, a6 := -682570 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 0, 0, -3, 0, -4, 0, -2, 0, 0, 0, 6, 0, -8, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, -8,                    0, 0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((46665385055705 : Rat)/35184372088832, (2283924015250355 : Rat)/562949953421312),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (245576427428812892612999041263890209053006565855 : Rat)/369511559608322295239203030318088461581541179392,            reHi := (27898280277046897440349947120691561518166299070005 : Rat)/5912184953733156723827248485089415385304658870272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2891, a6 := 47334 }
def label : String := "392.d2"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2891, a6 := 47334 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 0, 0, -3, 0, -4, 0, -2, 0, 0, 0, 6, 0, -8, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, -8,                    0, 0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((46665385055705 : Rat)/35184372088832, (2283924015250355 : Rat)/562949953421312),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (245576427428812892612999041263890209053006565855 : Rat)/369511559608322295239203030318088461581541179392,            reHi := (27898280277046897440349947120691561518166299070005 : Rat)/5912184953733156723827248485089415385304658870272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -931, a6 := -10290 }
def label : String := "392.d3"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -931, a6 := -10290 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 0, 0, -3, 0, -4, 0, -2, 0, 0, 0, 6, 0, -8, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, -8,                    0, 0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((46665385055705 : Rat)/35184372088832, (2283924015250355 : Rat)/562949953421312),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (245576427428812892612999041263890209053006565855 : Rat)/369511559608322295239203030318088461581541179392,            reHi := (27898280277046897440349947120691561518166299070005 : Rat)/5912184953733156723827248485089415385304658870272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 49, a6 := -686 }
def label : String := "392.d4"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 49, a6 := -686 },   conductor := 392,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, 0, 0, -3, 0, -4, 0, -2, 0, 0, 0, 6, 0, -8, 0, 0, 0, 0, 0, -1, 0, 0, 0, 6, 0, -8,                    0, 0, 0, 0, 0, -2, 0, 0, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   finite := ((46665385055705 : Rat)/35184372088832, (2283924015250355 : Rat)/562949953421312),   tail := (1865466724833254051869045430850982666015625 : Rat)/2819149472109392511285423510117252056743936,   box := { reLo := (245576427428812892612999041263890209053006565855 : Rat)/369511559608322295239203030318088461581541179392,            reHi := (27898280277046897440349947120691561518166299070005 : Rat)/5912184953733156723827248485089415385304658870272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -800, a6 := -8359 }
def label : String := "392.e1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -800, a6 := -8359 },   conductor := 392,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 1, 0, 1, 0, 0, 0, -2, 0, 3, 0, 6, 0, 1, 0, 5, 0, -1, 0, 0, 0, -7, 0, -4, 0, -5, 0, 2, 0, 5, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   geometricUpper := (6557932551624643 : Rat)/9007199254740992,   tail := (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/3924031525491300136655458366938936403852593478855257948421937809420266808949417934054130839301181742736915896127839081851452458244239521152629976889442378293017895248354486002493260235722845523754956830347097400149517582317806824102294872345862949215200943738068884916577209001918742824657491068593706630657336178515212055113216771852747396708291308958102541185921569150895404861557667619070212602563894403414965311528952427725523309178077009352454106202298941431559205589915813275053926749635163994814643631042631349675113840640,   box := { reLo := (2820071920938939265327375789087069738744768986338031304869889782267611777046685256471381060568981598483367031930498069190104901829845236648351768207416050291907566783783144939493944604740343437624822963666403491861110644564408418380626136583478420125765354101316609899594950875141032470166158599205058392060764724857007736686179601530264489357100927195878842343430107404809763818520246507257724762285820370169129125965054075947792221522032681784385439340823096982336960429400574037190304927579599277372501803836728918236016908446830556521 : Rat)/1839753551777392389643374644446166819854073224809784656926685445172822124993349865217915971878581686520444357908542384037680113220966841169712139306829669068977889987230847817609988071190628337076139298494193769706889307619326655225333665376428182792642078208548272490166650076548166374576764551386821107818856117503565960755719988476236533672225475853274479910499343449813099466646523510769653966254976105380318051406429492807989403635182304420653274058279827957569637171179886146218541418127666650739372297737334347465376164488505458688,            reHi := (80781084907540004462982098834840956344621132748804401925050032458023323213316704279557720111240109648738220207238871697655528050003203040600036473592108576099342742042503253420277864684851517360697381871970971477296591313326774296145539480754431092655760007140345131312578601879029370149932473473416448124347854538252190931882167129429313575784637736841087653388029820612604707967644682271330786697920922288986739071990971282065446232005839319114524786874663064946886967927151599644684189579887888665139929547836781924606597943126089215689 : Rat)/38917863595290992857840617478668913496913087447899290819602961340194314182551631764225145558969997214855553724988396585412463933520452409359295254567550691843763057422191011526365132275186368668918331314300252820722658430408833091305135229116750020613582423642367302676602213157749673308354634740875061896168110177960049169832538217766542058450923527665421690414409188361430950255984151189358064670778340690737497241289854655553621999975010285821511566617457899102434632467266822323853760768085256073332875529058995811767572710333769318400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1065037661612206258698035528506703418646709162299877308726934968954007223268941935723368608069697709742650147535583003917231932472175823014025476645682021040883473418741853073045608646102192109798582587063374488667721415726325581802187188211306528194370047690406857713883569562892350264090906482222502289312533722979190188548802611200074512229356210120497769201962780267427452787861257699664935557247905287948498569044833304701637712547806853447807595891492362852381827152805268450935053893519068748250258640249403214385342993603 : Rat)/7848063050982600273310916733877872807705186957710515896843875618840533617898835868108261678602363485473831792255678163702904916488479042305259953778884756586035790496708972004986520471445691047509913660694194800299035164635613648204589744691725898430401887476137769833154418003837485649314982137187413261314672357030424110226433543705494793416582617916205082371843138301790809723115335238140425205127788806829930623057904855451046618356154018704908212404597882863118411179831626550107853499270327989629287262085262699350227681280, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -343, a6 := -2401 }
def label : String := "392.f1"
def inputConductor : Nat := 392
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 392 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -343, a6 := -2401 },   conductor := 392,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 3, 0, -1, 0, 0, 0, 6, 0, -1, 0, 2, 0, -3, 0, 3, 0, 5, 0, 0, 0, -3, 0],   alphaLo := (168662971306525236982345367552 : Rat)/531475087495808696746826171875,   alphaHi := (5397215081808807583452231630848 : Rat)/17007202799865878200531005859375,   geometricUpper := (6557932551624643 : Rat)/9007199254740992,   tail := (102549530304854455844032493938692437006055565309523555225222644421150124814178957409158040371436722688866641159821796714433483633015442470459905870810681061101423602765311035737113039021866140655852756148132719541740468177412322736097966921922497184735883313014506914008499472655551037082243806099018747334254250551104097463826776348182864745212200490723737569489339735384077026762804414363072438671875 : Rat)/48638264546361451993587475756985658300278802711435455589022182938921370535377419171801705659885399080931343638050429521857832624214054698685131693464048162727140244998798539235458882336860886975473104731416922146340403939168333834994820962685715068652819747691785392089018351158119207629286868109275634400603485416683793540806239600371182718032203111819878048385224028590089994681199667486761771073536,   box := { reLo := (1538643167514220130405687060719829517151668984751583601622550521121249105093883708315995592658973678943229880438932107361208665220538303098593941552091102232166138267923746551607231177290468974846579105247455386398680350859609912927217277810468865845446576494897678755940970307398268673094169111545492298177734891868863450545666969836135776956055679698172225367316623274530219632749075832058370993829634521 : Rat)/13597556427903539326587282660001695562717443480022453141744986573319552953722788190764743842805861594060571084171568329278184977588402201837908841883276624612812962593089113621361062440504513867298138524238571839841655027253595248580327122433231933167925552763453983139366415341519596280881583282969642731204713400515204741235496373877769696566672862955924206596815155552788509363049585040936554530173091840,            reHi := (1235185217766451190873543841025632431113262344115729078141375076931085529734328347939883910043592095505149783919486888749221959583281520703032337539308629056086910152924212516962021488920013605417640329199186797340913831700286040253723427642360046246657384497920196220357145981471111175806858861778787859867984072282405469221092850003916524334524770622317273362197951305194797550271422919975891598371909307 : Rat)/285263421564409915942390545314720885931135177902568947029615102936773838189988563442617003695227865609662330437165769145696188341015430807788297382166642474394677536917953432615966344905689102111149759249760248388286469103222277942244624946151718877648787820212321324602092629542369152745767481460901595759539441968850449116828595256176986641258871250823584753779338927680877818805236049809857787346288640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (102549530304854455844032493938692437006055565309523555225222644421150124814178957409158040371436722688866641159821796714433483633015442470459905870810681061101423602765311035737113039021866140655852756148132719541740468177412322736097966921922497184735883313014506914008499472655551037082243806099018747334254250551104097463826776348182864745212200490723737569489339735384077026762804414363072438671875 : Rat)/97276529092722903987174951513971316600557605422870911178044365877842741070754838343603411319770798161862687276100859043715665248428109397370263386928096325454280489997597078470917764673721773950946209462833844292680807878336667669989641925371430137305639495383570784178036702316238415258573736218551268801206970833367587081612479200742365436064406223639756096770448057180179989362399334973523542147072, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N392.C392_f1
