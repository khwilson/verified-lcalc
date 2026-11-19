module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -25, a6 := 52 }
def label : String := "475.a1"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -25, a6 := 52 },   conductor := 475,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 2, 3, -3, 0, -4, 0, -2, -2, 0, -1, 4, 3, 1, 0, 0, 4, -6, 0, 0, 2, 0, -2, -6, 0,                    -4, -5, 0, -4, 0, 3, -10, -1, 0, 0, -10, 0, 2, 4, 0, 6, -6, 0, -3, 0, 0, 2, 10, 0, 0, 6, 0, 6, 0, 0,                    2, 4, -6, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   finite := ((14073496478315783 : Rat)/9007199254740992, (3577889903458661 : Rat)/1125899906842624),   tail := (267784995255894894405664645227264404296875 : Rat)/223768869351403159384747211192572787556352,   box := { reLo := (85823422422860788837068159139989418255302392773 : Rat)/234638665949016919255020691723463203284689354752,            reHi := (128303593906249169682885007123982232678473052991 : Rat)/29329833243627114906877586465432900410586169344,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 2 }
def label : String := "475.a2"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 2 },   conductor := 475,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 0, 0, 2, 3, -3, 0, -4, 0, -2, -2, 0, -1, 4, 3, 1, 0, 0, 4, -6, 0, 0, 2, 0, -2, -6, 0,                    -4, -5, 0, -4, 0, 3, -10, -1, 0, 0, -10, 0, 2, 4, 0, 6, -6, 0, -3, 0, 0, 2, 10, 0, 0, 6, 0, 6, 0, 0,                    2, 4, -6, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   finite := ((14073496478315783 : Rat)/9007199254740992, (3577889903458661 : Rat)/1125899906842624),   tail := (267784995255894894405664645227264404296875 : Rat)/223768869351403159384747211192572787556352,   box := { reLo := (85823422422860788837068159139989418255302392773 : Rat)/234638665949016919255020691723463203284689354752,            reHi := (128303593906249169682885007123982232678473052991 : Rat)/29329833243627114906877586465432900410586169344,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -19233, a6 := -1020257 }
def label : String := "475.b1"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -19233, a6 := -1020257 },   conductor := 475,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, -2, 0, 0, 1, 0, 1, 0, 3, -4, 4, 0, 0, 4, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, -4, -2, 6, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   geometricUpper := (6751278275530941 : Rat)/9007199254740992,   tail := (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/392262116173716935977895471244328277778320493524194347669712692000633613365648255109895717821982423405549791033141221445139107229290355802005444637462823777581991330571464739477605801002294690808382387448102712054886251424210686834028363148585368764914265676305463952483183292367616684503033263934282790126205657682375499626604143683185838390322606893274437193316980424667172916321946920499259220228034818956160778318920346649360627485136010763690807229023660660453435221371115245275443241532237856610046999573941627937760477184,   box := { reLo := (456180097187093417475734430474673747685316081756176301117451709575957984442639729521125117237013016661111812585471566388096508784341671300883479324742710080891776436074180261700094565718174532100482640304951699554172837468387656596847775701464427457458073837966167837062704974496990099408459554579901760773222215144327918469745064722177867844142564081789979227412066551407549869882945334508428198169264106726816700301643644067958888881580447596372459456411959338397212687671477402530532001988798578710599187712850354851582565575060918847 : Rat)/439782944418065229895948396911818759853756963369517505862185594891527496835096892267192335165270023812521893581076361502419687122629751841981808025318706129422956886762369186506069823895380879496294284379788421624094543120088790744316769117153542969404957045478098137368738164781917151214313877004460047502870547427084515907042379752359165644063758127956484171940370428450791105572000224385453516520314573235391792636350608439644370370117421413856555994195647758289480921964946160220138242467276006495071539535385532097432349035460558848,            reHi := (2679598076453182837158386398953465156662842302628019053169614387209845591488377157359266807632799064035511064276846297420452566273380985218963485783569522694454037190622905678894719850651508803785814556357440127549789619966695762826680663859696290435839882919987340833866766706292298561712169500022241294382787682021885562649355937884939438464982927464899796738215392237722340740105779669860341184495811092323938815830859185544956208874819810850683990721975607551730825684273772939882469265678810848430640296098452849729843079445855688045 : Rat)/1026160203642152203090546259460910439658766247862207513678433054746897492615226081956782115385630055562551085022511510172312603286136087631290885392410314301986899402445528101847496255755888718824686663552839650456220600613540511736739127940024933595278233106115562320527055717824473352833399046343740110840031277329863870449765552755504719836148768965231796401194197666385179246334667190232724871880734004215914182818151419692503530863607316632331963986456511436008788817918207707180322565756977348488500258915899574894008814416074637312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/784524232347433871955790942488656555556640987048388695339425384001267226731296510219791435643964846811099582066282442890278214458580711604010889274925647555163982661142929478955211602004589381616764774896205424109772502848421373668056726297170737529828531352610927904966366584735233369006066527868565580252411315364750999253208287366371676780645213786548874386633960849334345832643893840998518440456069637912321556637840693298721254970272021527381614458047321320906870442742230490550886483064475713220093999147883255875520954368, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -233, a6 := -1382 }
def label : String := "475.b2"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -233, a6 := -1382 },   conductor := 475,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, -2, 0, 0, 1, 0, 1, 0, 3, -4, 4, 0, 0, 4, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, -4, -2, 6, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   geometricUpper := (6751278275530941 : Rat)/9007199254740992,   tail := (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/392262116173716935977895471244328277778320493524194347669712692000633613365648255109895717821982423405549791033141221445139107229290355802005444637462823777581991330571464739477605801002294690808382387448102712054886251424210686834028363148585368764914265676305463952483183292367616684503033263934282790126205657682375499626604143683185838390322606893274437193316980424667172916321946920499259220228034818956160778318920346649360627485136010763690807229023660660453435221371115245275443241532237856610046999573941627937760477184,   box := { reLo := (456180097187093417475734430474673747685316081756176301117451709575957984442639729521125117237013016661111812585471566388096508784341671300883479324742710080891776436074180261700094565718174532100482640304951699554172837468387656596847775701464427457458073837966167837062704974496990099408459554579901760773222215144327918469745064722177867844142564081789979227412066551407549869882945334508428198169264106726816700301643644067958888881580447596372459456411959338397212687671477402530532001988798578710599187712850354851582565575060918847 : Rat)/439782944418065229895948396911818759853756963369517505862185594891527496835096892267192335165270023812521893581076361502419687122629751841981808025318706129422956886762369186506069823895380879496294284379788421624094543120088790744316769117153542969404957045478098137368738164781917151214313877004460047502870547427084515907042379752359165644063758127956484171940370428450791105572000224385453516520314573235391792636350608439644370370117421413856555994195647758289480921964946160220138242467276006495071539535385532097432349035460558848,            reHi := (2679598076453182837158386398953465156662842302628019053169614387209845591488377157359266807632799064035511064276846297420452566273380985218963485783569522694454037190622905678894719850651508803785814556357440127549789619966695762826680663859696290435839882919987340833866766706292298561712169500022241294382787682021885562649355937884939438464982927464899796738215392237722340740105779669860341184495811092323938815830859185544956208874819810850683990721975607551730825684273772939882469265678810848430640296098452849729843079445855688045 : Rat)/1026160203642152203090546259460910439658766247862207513678433054746897492615226081956782115385630055562551085022511510172312603286136087631290885392410314301986899402445528101847496255755888718824686663552839650456220600613540511736739127940024933595278233106115562320527055717824473352833399046343740110840031277329863870449765552755504719836148768965231796401194197666385179246334667190232724871880734004215914182818151419692503530863607316632331963986456511436008788817918207707180322565756977348488500258915899574894008814416074637312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/784524232347433871955790942488656555556640987048388695339425384001267226731296510219791435643964846811099582066282442890278214458580711604010889274925647555163982661142929478955211602004589381616764774896205424109772502848421373668056726297170737529828531352610927904966366584735233369006066527868565580252411315364750999253208287366371676780645213786548874386633960849334345832643893840998518440456069637912321556637840693298721254970272021527381614458047321320906870442742230490550886483064475713220093999147883255875520954368, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 17, a6 := -7 }
def label : String := "475.b3"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 17, a6 := -7 },   conductor := 475,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, -2, 0, 0, 1, 0, 1, 0, 3, -4, 4, 0, 0, 4, 3, 0, 1, 0, 2, 0, 0, 0, 0, 0, -4, -2, 6, 0, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   geometricUpper := (6751278275530941 : Rat)/9007199254740992,   tail := (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/392262116173716935977895471244328277778320493524194347669712692000633613365648255109895717821982423405549791033141221445139107229290355802005444637462823777581991330571464739477605801002294690808382387448102712054886251424210686834028363148585368764914265676305463952483183292367616684503033263934282790126205657682375499626604143683185838390322606893274437193316980424667172916321946920499259220228034818956160778318920346649360627485136010763690807229023660660453435221371115245275443241532237856610046999573941627937760477184,   box := { reLo := (456180097187093417475734430474673747685316081756176301117451709575957984442639729521125117237013016661111812585471566388096508784341671300883479324742710080891776436074180261700094565718174532100482640304951699554172837468387656596847775701464427457458073837966167837062704974496990099408459554579901760773222215144327918469745064722177867844142564081789979227412066551407549869882945334508428198169264106726816700301643644067958888881580447596372459456411959338397212687671477402530532001988798578710599187712850354851582565575060918847 : Rat)/439782944418065229895948396911818759853756963369517505862185594891527496835096892267192335165270023812521893581076361502419687122629751841981808025318706129422956886762369186506069823895380879496294284379788421624094543120088790744316769117153542969404957045478098137368738164781917151214313877004460047502870547427084515907042379752359165644063758127956484171940370428450791105572000224385453516520314573235391792636350608439644370370117421413856555994195647758289480921964946160220138242467276006495071539535385532097432349035460558848,            reHi := (2679598076453182837158386398953465156662842302628019053169614387209845591488377157359266807632799064035511064276846297420452566273380985218963485783569522694454037190622905678894719850651508803785814556357440127549789619966695762826680663859696290435839882919987340833866766706292298561712169500022241294382787682021885562649355937884939438464982927464899796738215392237722340740105779669860341184495811092323938815830859185544956208874819810850683990721975607551730825684273772939882469265678810848430640296098452849729843079445855688045 : Rat)/1026160203642152203090546259460910439658766247862207513678433054746897492615226081956782115385630055562551085022511510172312603286136087631290885392410314301986899402445528101847496255755888718824686663552839650456220600613540511736739127940024933595278233106115562320527055717824473352833399046343740110840031277329863870449765552755504719836148768965231796401194197666385179246334667190232724871880734004215914182818151419692503530863607316632331963986456511436008788817918207707180322565756977348488500258915899574894008814416074637312,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (308710608277801843565470529800708829964439988867563117039398684516083306681289972130026607061899403120383148362748672710837609799250106610338015843795612463531111217663556444646023537630611804574763528649530055965635901194724960869805794344811287939172898344671410314381238696041406732901274001113525622167305005855060151454135524683332728567964251372783150738127284315907149831051414842216943877261844848369127022564389943352651531279695690470597159312254611072354625374406814741041665683319785265980782125713846356764304067349 : Rat)/784524232347433871955790942488656555556640987048388695339425384001267226731296510219791435643964846811099582066282442890278214458580711604010889274925647555163982661142929478955211602004589381616764774896205424109772502848421373668056726297170737529828531352610927904966366584735233369006066527868565580252411315364750999253208287366371676780645213786548874386633960849334345832643893840998518440456069637912321556637840693298721254970272021527381614458047321320906870442742230490550886483064475713220093999147883255875520954368, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -617, a6 := 5916 }
def label : String := "475.c1"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -617, a6 := 5916 },   conductor := 475,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 0, 0, -2, -3, -3, 0, -4, 0, 2, -2, 0, -1, -4, -3, 1, 0, 0, -4, 6, 0, 0, 2, 0, 2, -6, 0,                    -4, 5, 0, -4, 0, 3, 10, 1, 0, 0, -10, 0, -2, 4, 0, 6, 6, 0, -3, 0, 0, -2, -10, 0, 0, 6, 0, -6, 0, 0,                    2, -4, 6, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   finite := ((5889806843945479 : Rat)/2251799813685248, (47943367508719399 : Rat)/9007199254740992),   tail := (267784995255894894405664645227264404296875 : Rat)/223768869351403159384747211192572787556352,   box := { reLo := (83231974363199775552162579630263451080091505349 : Rat)/58659666487254229813755172930865800821172338688,            reHi := (1529723632850760470365119659435291394181401336869 : Rat)/234638665949016919255020691723463203284689354752,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 8, a6 := 291 }
def label : String := "475.c2"
def inputConductor : Nat := 475
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.nonsingular
def minimality : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 475 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 8, a6 := 291 },   conductor := 475,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, 0, 0, -2, -3, -3, 0, -4, 0, 2, -2, 0, -1, -4, -3, 1, 0, 0, -4, 6, 0, 0, 2, 0, 2, -6, 0,                    -4, 5, 0, -4, 0, 3, 10, 1, 0, 0, -10, 0, -2, 4, 0, 6, 6, 0, -3, 0, 0, -2, -10, 0, 0, 6, 0, -6, 0, 0,                    2, -4, 6, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/18721328409076143360137939453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4680332102269035816192626953125,   finite := ((5889806843945479 : Rat)/2251799813685248, (47943367508719399 : Rat)/9007199254740992),   tail := (267784995255894894405664645227264404296875 : Rat)/223768869351403159384747211192572787556352,   box := { reLo := (83231974363199775552162579630263451080091505349 : Rat)/58659666487254229813755172930865800821172338688,            reHi := (1529723632850760470365119659435291394181401336869 : Rat)/234638665949016919255020691723463203284689354752,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N475.C475_c2
