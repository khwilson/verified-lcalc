module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -11, a6 := -16 }
def label : String := "381.a1"
def inputConductor : Nat := 381
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 127] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 381 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -11, a6 := -16 },   conductor := 381,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -1, 0, -2, 0, 1, 0, -4, -2, -3, 0, -1, 4, 0, 0, -4, 2, -2, 0, -3, 0, -4, 0, 1, 4, 5, 0,                    -5, 0, -4, 0, 2, -2, 5, 0, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8383441710946250247955322265625,   alphaHi := (5397215081808807583452231630848 : Rat)/16766883421892500400543212890625,   finite := ((12653767189943929 : Rat)/9007199254740992, (18110101879474163 : Rat)/4503599627370496),   tail := (218882149824928871515946501739788055419921875 : Rat)/362180852212663992393064869660795137643511808,   box := { reLo := (608022568695091922485453233728430116689916045471367 : Rat)/759548298579492716975100777538875844499366075170816,            reHi := (1756681525324406795600262385841078447462431721172749 : Rat)/379774149289746358487550388769437922249683037585408,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -4, a6 := -5 }
def label : String := "381.b1"
def inputConductor : Nat := 381
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 127] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 381 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -4, a6 := -5 },   conductor := 381,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 1, 2, 3, 2, -4, 0, 1, 6, 6, 2, -7, -8, 3, -4, -2, 2, 0, 6, -4, 12, 1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/8383441710946250247955322265625,   alphaHi := (5397215081808807583452231630848 : Rat)/16766883421892500400543212890625,   geometricUpper := (1632042795810037 : Rat)/2251799813685248,   tail := (81292148749966112729120778598094547491853094140188787868874018385127469025573789656221154655609590071445093484415240747600686197894763529240905327070202930517985453208069273042609678999891327110232750475953903979774955378117255583843627836633777530138388878318857562143922975865702936719140447055385787552831672372959514217050963279300107180407731844371549876336590714019277719358203125 : Rat)/43925938003220166769744383799338749066618693685490068564495019607975021490728608035259586709782093630456298757403891636465968804609279653076717521076249378128507794009878568886790991093826223269302284771911714317920966429817402147172930692550681773069917836008121616228334999045981609621333241828114794504825242941632341035806377804457389306135548181953803713638793928966091013256904704,   box := { reLo := (378347929736979257667894994109510008632951434628129291667524329145083630285734147403979929486936159720199273813569983230714427868296325118822703301034356885408154804620378970691586794266828263823613986062463176928449435290969714623339450060071382686042577760668918163884850385657538064836221672543760521055176023426946197107300824575947949007416940694288484063155049895950115022887080472425147 : Rat)/257883252015275164382655361794104885038994357103864651382894053290774274544166409412924273528924851121768818404385998272320779946072458590460243209373314805326421910079805744327550191928056090273932358087449466679081074578989942656762407750321558347654123176295820912458363954174086822569548582785215163040570849902526353855179410228965730868765475077246217839272017919779509916544497835048960,            reHi := (799715034887351668940149062964955493822604485746521792045762776359782119756084309480514768846547592585277261780703068357665927690796547850198453119536588175700405920609332393467217322451614079231990694310956320404562618508652088534952777356494961114017360688803527813910194643658988597404431183492540287834966412650911174332834670542191247425206556061325602713036870128811951011712952780199107 : Rat)/154729951209165098629593217076462931023396614262318790829736431974464564726499845647754564117354910673061291042631598963392467967643475154276145925623988883195853146047883446596530115156833654164359414852469680007448644747393965594057444650192935008592473905777492547475018372504452093541729149671129097824342509941515812313107646137379438521259285046347730703563210751867705949926698701029376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (81292148749966112729120778598094547491853094140188787868874018385127469025573789656221154655609590071445093484415240747600686197894763529240905327070202930517985453208069273042609678999891327110232750475953903979774955378117255583843627836633777530138388878318857562143922975865702936719140447055385787552831672372959514217050963279300107180407731844371549876336590714019277719358203125 : Rat)/87851876006440333539488767598677498133237387370980137128990039215950042981457216070519173419564187260912597514807783272931937609218559306153435042152498756257015588019757137773581982187652446538604569543823428635841932859634804294345861385101363546139835672016243232456669998091963219242666483656229589009650485883264682071612755608914778612271096363907607427277587857932182026513809408, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N381.C381_b1
