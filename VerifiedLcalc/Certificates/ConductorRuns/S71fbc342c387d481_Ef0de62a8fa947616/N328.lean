module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -10 }
def label : String := "328.a1"
def inputConductor : Nat := 328
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 328 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -10 },   conductor := 328,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -2, 0, -3, 0, 0, 0, -4, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, -1, 0, 0, 0, 0, 0, 4,                    0, 0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/15557033208393858623504638671875,   finite := ((3096327312630775 : Rat)/2251799813685248, (29224197025902375 : Rat)/9007199254740992),   tail := (45353697239890496811241469825649261474609375 : Rat)/122664766365781625733004039173171096567414784,   box := { reLo := (129306139145567980968843777691848316440793147016825 : Rat)/128623330056765833984610443380047055754273524547584,            reHi := (1859520137491065699532873353585133663005717615959625 : Rat)/514493320227063335938441773520188223017094098190336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 29, a6 := -66 }
def label : String := "328.a2"
def inputConductor : Nat := 328
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 41, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 328 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 29, a6 := -66 },   conductor := 328,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -2, 0, -2, 0, -3, 0, 0, 0, -4, 0, 0, 0, -2, 0, 4, 0, 0, 0, -4, 0, -1, 0, 0, 0, 0, 0, 4,                    0, 0, 0, 4, 0, -6, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/15557033208393858623504638671875,   finite := ((3096327312630775 : Rat)/2251799813685248, (29224197025902375 : Rat)/9007199254740992),   tail := (45353697239890496811241469825649261474609375 : Rat)/122664766365781625733004039173171096567414784,   box := { reLo := (129306139145567980968843777691848316440793147016825 : Rat)/128623330056765833984610443380047055754273524547584,            reHi := (1859520137491065699532873353585133663005717615959625 : Rat)/514493320227063335938441773520188223017094098190336,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := 20 }
def label : String := "328.b1"
def inputConductor : Nat := 328
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 328 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := 20 },   conductor := 328,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 2, 0, -2, 0, 1, 0, 2, 0, 6, 0, 4, 0, -6, 0, -2, 0, -4, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/15557033208393858623504638671875,   geometricUpper := (3183388269674599 : Rat)/4503599627370496,   tail := (1458815353590726514454041339974828312929265281442944630042575560715572355464981957033053864817512669447837289727953529258176174929360586722216729661804114385061025346864128166263119767327541795374845656207178948627122881515420564245737562295191212621978485347580055916357986643445307465311424311610885250977533411307449751424903962366596213256366713286462889753880703413265309083591353515234375 : Rat)/1606103494109056455008493820028322372062772624267780116158400621394115237748750199312700365266361036753199248810667390301438651728532779604912567724945695207368925838117523102632599655642445153271660611176402787179668437470287930723634820838624505001320876307620639252792782986310751183290923780829846497346708837863550466535159945786089533883291697302132330625441667425108439656598309519228928,   box := { reLo := (406340107937336746915494914602229741699797782866977170971658606412933714074337709037871976192228696130536622457782663827896173840284011691798522011897283515236916480471069154293991012702257353878476320042625588177338390316880430990996562084012171347832604152823881792669009915927686139099110017723685417663865174468042606514849499965408339437847364346101254359215581622200775796154884784626374375641 : Rat)/370921571447016043001936605266440910216037023711522478926201831507863943581885114780271585856439749632967600516579580453165749423446002785856532953237583579665816577684051372937485727472344495922323659848134341685208527291575646160969843698576136307530049778863448532236229266773536432025122392563748899329735672560397662493962513679568447402676801033440951096292625883491668596493096591918324776960,            reHi := (7561066321251504619996963773740686468494787762395433943401089141038677566616493011310511508879007418422717967977072613410281987170155184867837855143941054113087432602804427921628990617415498264733471981335108658402758346453240189351109313897480621727858059815684573492493020435250945779943546590275077310329966295741445392161179464584620722158952636884184757054042221207188531839192614176663489589777 : Rat)/2596451000129112301013556236865086371512259165980657352483412820555047605073195803461901100995078247430773203616057063172160245964122019500995730672663085057660716043788359610562400092306411471456265618936940391796459691041029523126788905890032954152710348452044139725653604867414755024175856747946242295308149707922783637457737595756979131818737607234086657674048381184441680175451676143428273438720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1458815353590726514454041339974828312929265281442944630042575560715572355464981957033053864817512669447837289727953529258176174929360586722216729661804114385061025346864128166263119767327541795374845656207178948627122881515420564245737562295191212621978485347580055916357986643445307465311424311610885250977533411307449751424903962366596213256366713286462889753880703413265309083591353515234375 : Rat)/3212206988218112910016987640056644744125545248535560232316801242788230475497500398625400730532722073506398497621334780602877303457065559209825135449891390414737851676235046205265199311284890306543321222352805574359336874940575861447269641677249010002641752615241278505585565972621502366581847561659692994693417675727100933070319891572179067766583394604264661250883334850216879313196619038457856, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := 60 }
def label : String := "328.b2"
def inputConductor : Nat := 328
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 41, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 328 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := 60 },   conductor := 328,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, 2, 0, -2, 0, 1, 0, 2, 0, 6, 0, 4, 0, -6, 0, -2, 0, -4, 0, 0, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/3889258302098464679718017578125,   alphaHi := (5397215081808807583452231630848 : Rat)/15557033208393858623504638671875,   geometricUpper := (3183388269674599 : Rat)/4503599627370496,   tail := (1458815353590726514454041339974828312929265281442944630042575560715572355464981957033053864817512669447837289727953529258176174929360586722216729661804114385061025346864128166263119767327541795374845656207178948627122881515420564245737562295191212621978485347580055916357986643445307465311424311610885250977533411307449751424903962366596213256366713286462889753880703413265309083591353515234375 : Rat)/1606103494109056455008493820028322372062772624267780116158400621394115237748750199312700365266361036753199248810667390301438651728532779604912567724945695207368925838117523102632599655642445153271660611176402787179668437470287930723634820838624505001320876307620639252792782986310751183290923780829846497346708837863550466535159945786089533883291697302132330625441667425108439656598309519228928,   box := { reLo := (406340107937336746915494914602229741699797782866977170971658606412933714074337709037871976192228696130536622457782663827896173840284011691798522011897283515236916480471069154293991012702257353878476320042625588177338390316880430990996562084012171347832604152823881792669009915927686139099110017723685417663865174468042606514849499965408339437847364346101254359215581622200775796154884784626374375641 : Rat)/370921571447016043001936605266440910216037023711522478926201831507863943581885114780271585856439749632967600516579580453165749423446002785856532953237583579665816577684051372937485727472344495922323659848134341685208527291575646160969843698576136307530049778863448532236229266773536432025122392563748899329735672560397662493962513679568447402676801033440951096292625883491668596493096591918324776960,            reHi := (7561066321251504619996963773740686468494787762395433943401089141038677566616493011310511508879007418422717967977072613410281987170155184867837855143941054113087432602804427921628990617415498264733471981335108658402758346453240189351109313897480621727858059815684573492493020435250945779943546590275077310329966295741445392161179464584620722158952636884184757054042221207188531839192614176663489589777 : Rat)/2596451000129112301013556236865086371512259165980657352483412820555047605073195803461901100995078247430773203616057063172160245964122019500995730672663085057660716043788359610562400092306411471456265618936940391796459691041029523126788905890032954152710348452044139725653604867414755024175856747946242295308149707922783637457737595756979131818737607234086657674048381184441680175451676143428273438720,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1458815353590726514454041339974828312929265281442944630042575560715572355464981957033053864817512669447837289727953529258176174929360586722216729661804114385061025346864128166263119767327541795374845656207178948627122881515420564245737562295191212621978485347580055916357986643445307465311424311610885250977533411307449751424903962366596213256366713286462889753880703413265309083591353515234375 : Rat)/3212206988218112910016987640056644744125545248535560232316801242788230475497500398625400730532722073506398497621334780602877303457065559209825135449891390414737851676235046205265199311284890306543321222352805574359336874940575861447269641677249010002641752615241278505585565972621502366581847561659692994693417675727100933070319891572179067766583394604264661250883334850216879313196619038457856, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N328.C328_b2
