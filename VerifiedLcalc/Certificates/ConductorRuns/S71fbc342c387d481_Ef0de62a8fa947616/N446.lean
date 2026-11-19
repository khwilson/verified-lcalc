module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4, a6 := 4 }
def label : String := "446.a1"
def inputConductor : Nat := 446
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 223] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 446 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.root_formula
theorem coefficients_correct : modelCoefficients equation 8 = (List.range 8).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 8

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -30, a6 := 52 }
def label : String := "446.b1"
def inputConductor : Nat := 446
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 223] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 446 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -30, a6 := 52 },   conductor := 446,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -1, 1, 0, 1, 0, -1, -2, 0, 1, -1, -2, 0, 0, 1, 1, 2, -4, 0, 0, -1, 1, 1, -5, 2, 5, 0, -3, 0,                    -10, -1, -1, -1, 0, -2, -3, 4, 2, 0, -5, 0, -6, 1, 0, -1, 6, -1, -7, 5, -1, -2, -9, -5, 0, 0, 4, 3,                    -1, 0, 4, 10, 0, 1],   alphaLo := (337325942613050473964690735104 : Rat)/1133802221569809055328369140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18140835545116944789886474609375,   finite := ((12977472527426599 : Rat)/9007199254740992, (26827320075569669 : Rat)/9007199254740992),   tail := (87450863930050684822155361008930206298828125 : Rat)/88444272392510131157966114528727132448751616,   box := { reLo := (670730618321945143402519394710424753553056713309807 : Rat)/1483848661891979252625527624129193306153314791981056,            reHi := (5886722655486218088384939733468691538674093025588317 : Rat)/1483848661891979252625527624129193306153314791981056,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -39, a6 := -35 }
def label : String := "446.c1"
def inputConductor : Nat := 446
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 223] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 446 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -39, a6 := -35 },   conductor := 446,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -2, -1, -2, 1, -2, -2, -3, -1, 0, -2, 2, 1, 1, -2, -6, -2, 2, -3, -3, -1, -1, 0, 5, -2,                    5, 2, 2, 1, 3, 1, 4, -2, -7, -6, 0, -2],   alphaLo := (337325942613050473964690735104 : Rat)/1133802221569809055328369140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18140835545116944789886474609375,   finite := ((10689943308612689 : Rat)/9007199254740992, (3389671888500427 : Rat)/562949953421312),   tail := (87450863930050684822155361008930206298828125 : Rat)/88444272392510131157966114528727132448751616,   box := { reLo := (293882380109696149126875753042653011615301088367177 : Rat)/1483848661891979252625527624129193306153314791981056,            reHi := (650114423788788769271718302820007223176310371905011 : Rat)/92740541368248703289095476508074581634582174498816,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -38, a6 := -101 }
def label : String := "446.d1"
def inputConductor : Nat := 446
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 223, 223] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 446 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -38, a6 := -101 },   conductor := 446,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 2, 1, 0, 2, 0, 1, 1, 0, -2, 2, 4, 0, 0, 1, -2, 1, 8, 0, 0, -2, -8, 2, -5, 4, -4, 0, -6, 0, 8,                    1],   alphaLo := (337325942613050473964690735104 : Rat)/1133802221569809055328369140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18140835545116944789886474609375,   geometricUpper := (1633125788011 : Rat)/2199023255552,   tail := (12697077433853914997065491531410667926019968909997335211738307514265377439120187651160892228289170962901457527125312895946558997882457587664158114523240257347999994872919020634150470841050724922618616844336092890276252052042069420512077917266342110856905733236513003671911732121447754399726021386931224405988612837712111868515183436401461567852410730309163678653405585620878135450136216253074316169589192908651 : Rat)/22656754296480896442191794733945118385868031566222659918695169684958623531105006133800140782332256643106797575605233034445253713326264615657970103711279824094626549716818735364724852373923281622651675813756080315480525046462152376087571423807220192677898805863889756585320554776331362193264913175739912569403027638754284685675314555789832256738564800733018578732371663506802089273927876309998296221302208331776,   box := { reLo := (524775041182988682389601815308548880456022446548041195539421128770628820148384059746287704571218076582555917958800413636397135322671098449457711260183354818185910082030454082359128212430331835317016421274223148383232651204236898012854096058375822880542669450984147699229013342349614641957356573075608330344438939426898540915002589362765693986580198676914789082810903439342097318596555002575841000319713364580658266608959 : Rat)/224705756692938062206867231152414686966566493888897549637649904608293258338006274594640183257736435888208957523531491313356402838309138984977730813027422647087837136234306617703537507375568827139084485182720189994855891033481938062559377741985836770806658217051818839787607531109564696279922334852333105565414119684672875125106300528352680660097444864670439037498044474572686563314191847950711357068591651916765263298560,            reHi := (348144420728190827339359468879525570655203727944349844338193576386139153213960548503560672294882603170617112180078811034763269284695477062990294295161706949697341110867479847538747994789343898194038405392816470163804095997746050909279066530415865374208522765890108915592722057399310752833680409747744784002942253213169593329378602591196100538581748648716894000142923274469061816011705164771190530577869450079529177492337 : Rat)/100730166793386027885837034654530721743633255881229936044463750341648702013589019645873185598295643674024705096755496105987352996483407131196913812736430841797995957622275380349861641237323956993382700254322843790797468394319489476319721056752271655878846786954263617835824065669804863849620357002770012839668398479336116435392479547192580985560923560024679568533606143773962942175327380115836125582472119824756842168320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (12697077433853914997065491531410667926019968909997335211738307514265377439120187651160892228289170962901457527125312895946558997882457587664158114523240257347999994872919020634150470841050724922618616844336092890276252052042069420512077917266342110856905733236513003671911732121447754399726021386931224405988612837712111868515183436401461567852410730309163678653405585620878135450136216253074316169589192908651 : Rat)/45313508592961792884383589467890236771736063132445319837390339369917247062210012267600281564664513286213595151210466068890507426652529231315940207422559648189253099433637470729449704747846563245303351627512160630961050092924304752175142847614440385355797611727779513170641109552662724386529826351479825138806055277508569371350629111579664513477129601466037157464743327013604178547855752619996592442604416663552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 2, a6 := -5 }
def label : String := "446.d2"
def inputConductor : Nat := 446
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 223] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 446 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 2, a6 := -5 },   conductor := 446,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 2, 1, 0, 2, 0, 1, 1, 0, -2, 2, 4, 0, 0, 1, -2, 1, 8, 0, 0, -2, -8, 2, -5, 4, -4, 0, -6, 0, 8,                    1],   alphaLo := (337325942613050473964690735104 : Rat)/1133802221569809055328369140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18140835545116944789886474609375,   geometricUpper := (1633125788011 : Rat)/2199023255552,   tail := (12697077433853914997065491531410667926019968909997335211738307514265377439120187651160892228289170962901457527125312895946558997882457587664158114523240257347999994872919020634150470841050724922618616844336092890276252052042069420512077917266342110856905733236513003671911732121447754399726021386931224405988612837712111868515183436401461567852410730309163678653405585620878135450136216253074316169589192908651 : Rat)/22656754296480896442191794733945118385868031566222659918695169684958623531105006133800140782332256643106797575605233034445253713326264615657970103711279824094626549716818735364724852373923281622651675813756080315480525046462152376087571423807220192677898805863889756585320554776331362193264913175739912569403027638754284685675314555789832256738564800733018578732371663506802089273927876309998296221302208331776,   box := { reLo := (524775041182988682389601815308548880456022446548041195539421128770628820148384059746287704571218076582555917958800413636397135322671098449457711260183354818185910082030454082359128212430331835317016421274223148383232651204236898012854096058375822880542669450984147699229013342349614641957356573075608330344438939426898540915002589362765693986580198676914789082810903439342097318596555002575841000319713364580658266608959 : Rat)/224705756692938062206867231152414686966566493888897549637649904608293258338006274594640183257736435888208957523531491313356402838309138984977730813027422647087837136234306617703537507375568827139084485182720189994855891033481938062559377741985836770806658217051818839787607531109564696279922334852333105565414119684672875125106300528352680660097444864670439037498044474572686563314191847950711357068591651916765263298560,            reHi := (348144420728190827339359468879525570655203727944349844338193576386139153213960548503560672294882603170617112180078811034763269284695477062990294295161706949697341110867479847538747994789343898194038405392816470163804095997746050909279066530415865374208522765890108915592722057399310752833680409747744784002942253213169593329378602591196100538581748648716894000142923274469061816011705164771190530577869450079529177492337 : Rat)/100730166793386027885837034654530721743633255881229936044463750341648702013589019645873185598295643674024705096755496105987352996483407131196913812736430841797995957622275380349861641237323956993382700254322843790797468394319489476319721056752271655878846786954263617835824065669804863849620357002770012839668398479336116435392479547192580985560923560024679568533606143773962942175327380115836125582472119824756842168320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (12697077433853914997065491531410667926019968909997335211738307514265377439120187651160892228289170962901457527125312895946558997882457587664158114523240257347999994872919020634150470841050724922618616844336092890276252052042069420512077917266342110856905733236513003671911732121447754399726021386931224405988612837712111868515183436401461567852410730309163678653405585620878135450136216253074316169589192908651 : Rat)/45313508592961792884383589467890236771736063132445319837390339369917247062210012267600281564664513286213595151210466068890507426652529231315940207422559648189253099433637470729449704747846563245303351627512160630961050092924304752175142847614440385355797611727779513170641109552662724386529826351479825138806055277508569371350629111579664513477129601466037157464743327013604178547855752619996592442604416663552, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N446.C446_d2
