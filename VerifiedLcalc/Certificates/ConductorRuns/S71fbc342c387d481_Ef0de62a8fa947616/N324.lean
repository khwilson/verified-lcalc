module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -189, a6 := -999 }
def label : String := "324.a1"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -189, a6 := -999 },   conductor := 324,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -3, 0, -1, 0, 0, 0, -3, 0, -1, 0, 0, 0, -6, 0, -4, 0, 0, 0, 3, 0, 4, 0, 0, 0, -3, 0, 5,                    0, 0, 0, 3, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   finite := ((3050353370100347 : Rat)/2251799813685248, (1788715415206825 : Rat)/562949953421312),   tail := (522750154468399381767684853428745269775390625 : Rat)/1473562432650622845791387793723372166763773952,   box := { reLo := (386237799196180032981209459518578137485501251092607 : Rat)/386285550344764875287137561797819673284122758873088,            reHi := (341104577954486830716711214795297791755985186890325 : Rat)/96571387586191218821784390449454918321030689718272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -9, a6 := 9 }
def label : String := "324.a2"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -9, a6 := 9 },   conductor := 324,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -3, 0, -1, 0, 0, 0, -3, 0, -1, 0, 0, 0, -6, 0, -4, 0, 0, 0, 3, 0, 4, 0, 0, 0, -3, 0, 5,                    0, 0, 0, 3, 0, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   finite := ((3050353370100347 : Rat)/2251799813685248, (1788715415206825 : Rat)/562949953421312),   tail := (522750154468399381767684853428745269775390625 : Rat)/1473562432650622845791387793723372166763773952,   box := { reLo := (386237799196180032981209459518578137485501251092607 : Rat)/386285550344764875287137561797819673284122758873088,            reHi := (341104577954486830716711214795297791755985186890325 : Rat)/96571387586191218821784390449454918321030689718272,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := 94 }
def label : String := "324.b1"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := 94 },   conductor := 324,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, -3, 0, 2, 0, 0, 0, 6, 0, 5, 0, 0, 0, 3, 0, 2, 0, 0, 0, -6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   geometricUpper := (1588299525715723 : Rat)/2251799813685248,   tail := (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/48197066518549368640924617449754656620533417902223793318129973240321425350472180858924205420559949806780973171622674357664217320144057092602559354471612351197677078849002698122674200721794578674582222467424738518271918978716678928289130712785373515062553199778825491527364360006658605892666969166357880300979016037162263242765443337824136664990646012130071627033085564705832479768969216,   box := { reLo := (366789393828001334058012583280538480011307022447778319895361832055904261525880126517776639420864506861048266382653262072328600485653080822569009967902182185043348130808359768810758510759850862066381579112554218452022863324505832483892168909392221015811475501030051317566450316843046201935466500206036173507960639317611469843424578165300347556781075973077172666985413391397747016554415028649 : Rat)/856220886702029533906025828994891474863776169033005688296578974614310121351138292958788509296247508317463988393876809963904820692359174250084466932188193419026733305752532932149307175822680690153953182133800479777100640656901801161056407112632160495086257594070834856983627855518290133683228707240347743546892219900187606507728100896445787853558826405490722454242765056999114003095738122240,            reHi := (3832719468629739036376657670022019420814437107168812572042369012380571281654172796745961460520680771388280424865121578850222215627968314913270941946933854034243363089131945694057713823943596966130053667112243485209897920890667665921397744808715852425852866397930697063872708458127300949423819443761657916969671000594904150287806068683347419018790610527453127869283829579399247904706684658079051 : Rat)/1792070315867347814465312060086307856889883521786080905604739793867751083987932447162744349957046034908452127708384163254452789709107751705426789289069888826022952808940051426988499918996870684492224010206044404173471640894895469830091060086739111916215537144390257355666733101599781249798997684254047827243645416251092660420674915176261033977498623666692082096730107264299145608479379889848320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/96394133037098737281849234899509313241066835804447586636259946480642850700944361717848410841119899613561946343245348715328434640288114185205118708943224702395354157698005396245348401443589157349164444934849477036543837957433357856578261425570747030125106399557650983054728720013317211785333938332715760601958032074324526485530886675648273329981292024260143254066171129411664959537938432, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 81, a6 := 486 }
def label : String := "324.b2"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -81, a6 := -243 }
def label : String := "324.c1"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1.nonsingular
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := 37 }
def label : String := "324.c2"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -21, a6 := 37 },   conductor := 324,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 3, 0, -1, 0, 0, 0, 3, 0, -1, 0, 0, 0, 6, 0, -4, 0, 0, 0, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   geometricUpper := (1588299525715723 : Rat)/2251799813685248,   tail := (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/48197066518549368640924617449754656620533417902223793318129973240321425350472180858924205420559949806780973171622674357664217320144057092602559354471612351197677078849002698122674200721794578674582222467424738518271918978716678928289130712785373515062553199778825491527364360006658605892666969166357880300979016037162263242765443337824136664990646012130071627033085564705832479768969216,   box := { reLo := (58556098849899785583116039073975703368852949295911562999433619623516386605434502009270042801385052156962239216883508084697853717159454525876236677266652669610007407194099280237220960671035229171335412903272703776776768084720658183584496503967390676427603100461438302859846015196217630721739267802880415330919023743689445455493693295481066395537951185983349582795070011732449304753723287879443 : Rat)/77916100689884687585448350438535124212603631382003517634988686689902221042953584659249754345958523256889222943842789706715338683004684856757686490829125601131432730823480496825586952999863942804009739574175843659716158299778063905656133047249526605052849441060445971985510134852164402165173812358871644662767192010917072192203257181576566694673853202899655743336091620186919374281712169123840,            reHi := (48481533416433264670371166561818708663757281193107046000317661983920407413889925349426023981912062502564212855978022930391331066637087439852358046212331989524282128621987969802407067417298013838843674022177031177471008713752031338624883393150303216778335025468163782101970573261574954806424773387706830363649056345312272760958648088328463051897549599648774287674538520930048160644485208281553 : Rat)/19693080394146679279838594066882503921866851887759130830821316416129132791076180738052135713813692691301671733059166629169810875924261007751942739440328448637614866032308257439434065043921655873540923189077411034873314735108741426704297363590539691386983924663629201710623440676920673074714260266527998101578521057704314949677746320618253120631853007326286616447583596310979622071201976811520,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/96394133037098737281849234899509313241066835804447586636259946480642850700944361717848410841119899613561946343245348715328434640288114185205118708943224702395354157698005396245348401443589157349164444934849477036543837957433357856578261425570747030125106399557650983054728720013317211785333938332715760601958032074324526485530886675648273329981292024260143254066171129411664959537938432, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -351, a6 := -2538 }
def label : String := "324.d1"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -351, a6 := -2538 },   conductor := 324,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 3, 0, 2, 0, 0, 0, -6, 0, 5, 0, 0, 0, -3, 0, 2, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   geometricUpper := (1588299525715723 : Rat)/2251799813685248,   tail := (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/48197066518549368640924617449754656620533417902223793318129973240321425350472180858924205420559949806780973171622674357664217320144057092602559354471612351197677078849002698122674200721794578674582222467424738518271918978716678928289130712785373515062553199778825491527364360006658605892666969166357880300979016037162263242765443337824136664990646012130071627033085564705832479768969216,   box := { reLo := (15733885433629534810340294318232142047608117126732987974911068166752187644622882926052714288624654706710053827121146776325462776633540705104484804803198604232271080751653017567276850034784909875862099920469072550378417798108858482172946614253406319599687590840897459755315965164997563242011602109201902441573755058377295528450076158705438477790495359531052133710484052693743837478304011054639 : Rat)/19693080394146679279838594066882503921866851887759130830821316416129132791076180738052135713813692691301671733059166629169810875924261007751942739440328448637614866032308257439434065043921655873540923189077411034873314735108741426704297363590539691386983924663629201710623440676920673074714260266527998101578521057704314949677746320618253120631853007326286616447583596310979622071201976811520,            reHi := (195513601817739996171052352877172926455787398596448454531229734828783162519182088618045737151202388558205273982358811216454589890658635692006179187878506943742795817380455360719956070177767648283850787599667526438010873373060133930884764225148604735797000823512889934519125251086503630599823645685556405565248743165890314651933711175024725785277517227527319549779887310710193591721041696047341 : Rat)/77916100689884687585448350438535124212603631382003517634988686689902221042953584659249754345958523256889222943842789706715338683004684856757686490829125601131432730823480496825586952999863942804009739574175843659716158299778063905656133047249526605052849441060445971985510134852164402165173812358871644662767192010917072192203257181576566694673853202899655743336091620186919374281712169123840,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/96394133037098737281849234899509313241066835804447586636259946480642850700944361717848410841119899613561946343245348715328434640288114185205118708943224702395354157698005396245348401443589157349164444934849477036543837957433357856578261425570747030125106399557650983054728720013317211785333938332715760601958032074324526485530886675648273329981292024260143254066171129411664959537938432, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := -18 }
def label : String := "324.d2"
def inputConductor : Nat := 324
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 324 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 9, a6 := -18 },   conductor := 324,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 0, 0, 3, 0, 2, 0, 0, 0, -6, 0, 5, 0, 0, 0, -3, 0, 2, 0, 0, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15461882265600000095367431640625,   alphaHi := (314159265358979323847 : Rat)/900000000000000000000,   geometricUpper := (1588299525715723 : Rat)/2251799813685248,   tail := (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/48197066518549368640924617449754656620533417902223793318129973240321425350472180858924205420559949806780973171622674357664217320144057092602559354471612351197677078849002698122674200721794578674582222467424738518271918978716678928289130712785373515062553199778825491527364360006658605892666969166357880300979016037162263242765443337824136664990646012130071627033085564705832479768969216,   box := { reLo := (15733885433629534810340294318232142047608117126732987974911068166752187644622882926052714288624654706710053827121146776325462776633540705104484804803198604232271080751653017567276850034784909875862099920469072550378417798108858482172946614253406319599687590840897459755315965164997563242011602109201902441573755058377295528450076158705438477790495359531052133710484052693743837478304011054639 : Rat)/19693080394146679279838594066882503921866851887759130830821316416129132791076180738052135713813692691301671733059166629169810875924261007751942739440328448637614866032308257439434065043921655873540923189077411034873314735108741426704297363590539691386983924663629201710623440676920673074714260266527998101578521057704314949677746320618253120631853007326286616447583596310979622071201976811520,            reHi := (195513601817739996171052352877172926455787398596448454531229734828783162519182088618045737151202388558205273982358811216454589890658635692006179187878506943742795817380455360719956070177767648283850787599667526438010873373060133930884764225148604735797000823512889934519125251086503630599823645685556405565248743165890314651933711175024725785277517227527319549779887310710193591721041696047341 : Rat)/77916100689884687585448350438535124212603631382003517634988686689902221042953584659249754345958523256889222943842789706715338683004684856757686490829125601131432730823480496825586952999863942804009739574175843659716158299778063905656133047249526605052849441060445971985510134852164402165173812358871644662767192010917072192203257181576566694673853202899655743336091620186919374281712169123840,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (41216412707601063212914054267157960643767656458010480336113132339553727174618796872950923990935041113647521002166252141915152928626387551831512606975882829311181718500108905735299575207524146359221589870355006990668327063488500805681462683375665030521572326480694537777557045166934799975864217833867187056960195908683228951855956521462629086001914402634548423676698964542165930641796875 : Rat)/96394133037098737281849234899509313241066835804447586636259946480642850700944361717848410841119899613561946343245348715328434640288114185205118708943224702395354157698005396245348401443589157349164444934849477036543837957433357856578261425570747030125106399557650983054728720013317211785333938332715760601958032074324526485530886675648273329981292024260143254066171129411664959537938432, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N324.C324_d2
