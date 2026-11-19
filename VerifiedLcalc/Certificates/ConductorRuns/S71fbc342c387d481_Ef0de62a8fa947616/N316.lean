module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := -2 }
def label : String := "316.a1"
def inputConductor : Nat := 316
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 79] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 316 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := -2 },   conductor := 316,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -3, 0, 1, 0, 1, 0, 6, 0, -6, 0, -1, 0, -3, 0, -4, 0, -6, 0, -3, 0, 2, 0, -4, 0, -9, 0, -8, 0,                    4, 0, 18, 0, 1, 0, 4, 0, 3, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3817450434286023044586181640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15269801737144092082977294921875,   finite := ((4128183152915301 : Rat)/4503599627370496, (12225226005191367 : Rat)/4503599627370496),   tail := (120307818583797278758875771732616424560546875 : Rat)/369164343569046801829408728778400471950819328,   box := { reLo := (457353786022881227745036358908094976733913483481211 : Rat)/774193741444513638550148174375080106552604655353856,            reHi := (2353887902634897272167195309543413437673061011749337 : Rat)/774193741444513638550148174375080106552604655353856,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -180, a6 := -872 }
def label : String := "316.b1"
def inputConductor : Nat := 316
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 79] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 316 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -180, a6 := -872 },   conductor := 316,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 1, 0, 3, 0, -2, 0, 2, 0, -1, 0, -1, 0, 4, 0, 6, 0, -3, 0, 6, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3817450434286023044586181640625,   alphaHi := (5397215081808807583452231630848 : Rat)/15269801737144092082977294921875,   geometricUpper := (6325362760117613 : Rat)/9007199254740992,   tail := (41581099550501097062847408196839189225680969745241425618114446579998101320721448661012571369552464759947504998469295602008186544789246576186476289200502005051392325719780620684697518703385542094393834250020353832739973851461686748945878668957744725865595560433631293624419001057433230825837969722893891765733189121070532161994176413712496522777952878870953010528562797550193911322169270393781130078125 : Rat)/55030083841204832547932840811900629757608386744127434065361470883897810960087888942255883649226763989377051767867432668573973912342814767060066459068428099550170178481649942795864204847877010628320050270013656018959156583210251431897974596710757417924588424356493032282165233020417164752008692272738754860020142628475615365128071008503833327028381171539015982405927565515127364391579807560077437566976,   box := { reLo := (479857472845551434598318499176309484010838047003885142551910372675318603868540029562360930753552041827408771700463917981931990751719216981380910409915384746437412250834017914929663119865338540971963485615257957528489688322068305083695803204781546624005225069159187724245227354856142073677409390246056332937369038893375074015994677950919942045702152358321095754400511798044630918948827301127595441103612171327 : Rat)/876915667176786453641982144570002974816589952486953207955518437636442816700247328312080668406576575657341142216579952397423331957834783590129406338879510794092369578991680576690369256412913979149458806662972961461598046780554914668837764283378245159898991082747709550487920832053116705842032673148007970139167276913997768344465662775065327352029294786614385177914848971634485152689524507330383783504463790080,            reHi := (361012832754167603196638634597827897461982193450034158095063014271844779570682070208160038618773732422641049981553397036502584624638253077476616551214454746364112801557283390845303761842165330787287333860645082840269127719089791021844691910901857027871731369488865705766166043079297767294822295600513405784435877782954548955345292426560972724738976672401252403840456830498334342600291986187585640251997181325 : Rat)/175383133435357290728396428914000594963317990497390641591103687527288563340049465662416133681315315131468228443315990479484666391566956718025881267775902158818473915798336115338073851282582795829891761332594592292319609356110982933767552856675649031979798216549541910097584166410623341168406534629601594027833455382799553668893132555013065470405858957322877035582969794326897030537904901466076756700892758016,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (41581099550501097062847408196839189225680969745241425618114446579998101320721448661012571369552464759947504998469295602008186544789246576186476289200502005051392325719780620684697518703385542094393834250020353832739973851461686748945878668957744725865595560433631293624419001057433230825837969722893891765733189121070532161994176413712496522777952878870953010528562797550193911322169270393781130078125 : Rat)/110060167682409665095865681623801259515216773488254868130722941767795621920175777884511767298453527978754103535734865337147947824685629534120132918136856199100340356963299885591728409695754021256640100540027312037918313166420502863795949193421514835849176848712986064564330466040834329504017384545477509720040285256951230730256142017007666654056762343078031964811855131030254728783159615120154875133952, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N316.C316_b1
