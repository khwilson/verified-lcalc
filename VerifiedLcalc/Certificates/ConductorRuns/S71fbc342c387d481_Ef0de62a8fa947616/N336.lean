module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12544, a6 := 544960 }
def label : String := "336.a1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -784, a6 := 8704 }
def label : String := "336.a2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -624, a6 := -5760 }
def label : String := "336.a3"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -544, a6 := 13888 }
def label : String := "336.a4"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -64, a6 := 64 }
def label : String := "336.a5"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := 0 }
def label : String := "336.a6"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 0],              kodaira := -8 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_a6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1828, a6 := 30700 }
def label : String := "336.b1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1828, a6 := 30700 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (977306644549851017099131334230016696777092687537258070732945964865642223239621341779183361977491269125540773089728640199739871357665233689329620228790972457765482856383196064650841927152097109618292497585859690946594620877881746373338521919276836626727785140068486174061072833942006489382424228052602153163961476910754615431762331279770155155806726211749304731800392924215472488225680147477 : Rat)/5633216964660400869843331864135412216748281070947366662860988069080859535953305403663150267697563983062391010183924783924349010059654513185403563459928069129621131431624620640387686549196943816474804000416438645382139679500422067393974509472057538566322710090929167849237796678248165253007616687715687165598646480624575258834560771674806278872265080451994108783126896883264941498874969718784,            reHi := (1032700690217873424146028075081377776380132593419362398209114643266800383791709881729886519963325262072257083629145833566308434447484494785511889522543679773852733277572374371056821209771703499029712828264363927344515512800497889865124523459937827855450464596218044509516220972997099481303863488532787709444108471643191184681956816651529408069063296074011627747639522627241054112428220872325 : Rat)/465905162490709846378019928612703266046850314138504009710307283908943269890874883009734232666715818148017301594159192655397286546287215376236384947813599702449868013141885917626049263467416405873855969959254324054161928379734155949877591008967164843831201586467825912342975665118269306639727695976485404673572265314814495091580214198668188478157262293022069147476660644480559071335523811328,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -113, a6 := 516 }
def label : String := "336.b2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -113, a6 := 516 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (977306644549851017099131334230016696777092687537258070732945964865642223239621341779183361977491269125540773089728640199739871357665233689329620228790972457765482856383196064650841927152097109618292497585859690946594620877881746373338521919276836626727785140068486174061072833942006489382424228052602153163961476910754615431762331279770155155806726211749304731800392924215472488225680147477 : Rat)/5633216964660400869843331864135412216748281070947366662860988069080859535953305403663150267697563983062391010183924783924349010059654513185403563459928069129621131431624620640387686549196943816474804000416438645382139679500422067393974509472057538566322710090929167849237796678248165253007616687715687165598646480624575258834560771674806278872265080451994108783126896883264941498874969718784,            reHi := (1032700690217873424146028075081377776380132593419362398209114643266800383791709881729886519963325262072257083629145833566308434447484494785511889522543679773852733277572374371056821209771703499029712828264363927344515512800497889865124523459937827855450464596218044509516220972997099481303863488532787709444108471643191184681956816651529408069063296074011627747639522627241054112428220872325 : Rat)/465905162490709846378019928612703266046850314138504009710307283908943269890874883009734232666715818148017301594159192655397286546287215376236384947813599702449868013141885917626049263467416405873855969959254324054161928379734155949877591008967164843831201586467825912342975665118269306639727695976485404673572265314814495091580214198668188478157262293022069147476660644480559071335523811328,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -28, a6 := 28 }
def label : String := "336.b3"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -28, a6 := 28 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (977306644549851017099131334230016696777092687537258070732945964865642223239621341779183361977491269125540773089728640199739871357665233689329620228790972457765482856383196064650841927152097109618292497585859690946594620877881746373338521919276836626727785140068486174061072833942006489382424228052602153163961476910754615431762331279770155155806726211749304731800392924215472488225680147477 : Rat)/5633216964660400869843331864135412216748281070947366662860988069080859535953305403663150267697563983062391010183924783924349010059654513185403563459928069129621131431624620640387686549196943816474804000416438645382139679500422067393974509472057538566322710090929167849237796678248165253007616687715687165598646480624575258834560771674806278872265080451994108783126896883264941498874969718784,            reHi := (1032700690217873424146028075081377776380132593419362398209114643266800383791709881729886519963325262072257083629145833566308434447484494785511889522543679773852733277572374371056821209771703499029712828264363927344515512800497889865124523459937827855450464596218044509516220972997099481303863488532787709444108471643191184681956816651529408069063296074011627747639522627241054112428220872325 : Rat)/465905162490709846378019928612703266046850314138504009710307283908943269890874883009734232666715818148017301594159192655397286546287215376236384947813599702449868013141885917626049263467416405873855969959254324054161928379734155949877591008967164843831201586467825912342975665118269306639727695976485404673572265314814495091580214198668188478157262293022069147476660644480559071335523811328,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 7, a6 := 0 }
def label : String := "336.b4"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 7, a6 := 0 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (977306644549851017099131334230016696777092687537258070732945964865642223239621341779183361977491269125540773089728640199739871357665233689329620228790972457765482856383196064650841927152097109618292497585859690946594620877881746373338521919276836626727785140068486174061072833942006489382424228052602153163961476910754615431762331279770155155806726211749304731800392924215472488225680147477 : Rat)/5633216964660400869843331864135412216748281070947366662860988069080859535953305403663150267697563983062391010183924783924349010059654513185403563459928069129621131431624620640387686549196943816474804000416438645382139679500422067393974509472057538566322710090929167849237796678248165253007616687715687165598646480624575258834560771674806278872265080451994108783126896883264941498874969718784,            reHi := (1032700690217873424146028075081377776380132593419362398209114643266800383791709881729886519963325262072257083629145833566308434447484494785511889522543679773852733277572374371056821209771703499029712828264363927344515512800497889865124523459937827855450464596218044509516220972997099481303863488532787709444108471643191184681956816651529408069063296074011627747639522627241054112428220872325 : Rat)/465905162490709846378019928612703266046850314138504009710307283908943269890874883009734232666715818148017301594159192655397286546287215376236384947813599702449868013141885917626049263467416405873855969959254324054161928379734155949877591008967164843831201586467825912342975665118269306639727695976485404673572265314814495091580214198668188478157262293022069147476660644480559071335523811328,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -152, a6 := -672 }
def label : String := "336.c1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -152, a6 := -672 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -2, 0, -2, 0, 6, 0, 4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (23087877953176551906314425696014962560857509407618609031014918229456653878073953378537372361778593553234562766195300971393556065039566677965916120465875668763061629217377404849867008973243970656932546434173878204803478647593879240155831535383974389893238580824121795620487654939646522012412926172042123038013892520737817190702983729343015144953021398046982797888501212532947977793594852625663 : Rat)/68403348856590581990954744064501434060514841575789452334740569410267580079432994187338253250613276937186176552233372376224237979295804802965614699156269410859685167384013250633279050954534317771479762862199612122497410393933696532641119043589270111162490051104139895312173245378727720929378202636547629867983564407584128142991095084622647672020361691202785606652255176439645718200624632299520,            reHi := (59993618146667670586929168302733967940930416389051139740649685607605682388515052052543132786558580334160616565907231889455971052249306310813541305643014713150363276358091894250286300201806586527872065706638549181428753924102302365679799058235030882688855212140983317631064788115305912229673497367878847604154063768935116974149869237894761082324821579422959221526849662817662100026716723752381 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := 0 }
def label : String := "336.c2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := 0 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -2, 0, -2, 0, 6, 0, 4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (23087877953176551906314425696014962560857509407618609031014918229456653878073953378537372361778593553234562766195300971393556065039566677965916120465875668763061629217377404849867008973243970656932546434173878204803478647593879240155831535383974389893238580824121795620487654939646522012412926172042123038013892520737817190702983729343015144953021398046982797888501212532947977793594852625663 : Rat)/68403348856590581990954744064501434060514841575789452334740569410267580079432994187338253250613276937186176552233372376224237979295804802965614699156269410859685167384013250633279050954534317771479762862199612122497410393933696532641119043589270111162490051104139895312173245378727720929378202636547629867983564407584128142991095084622647672020361691202785606652255176439645718200624632299520,            reHi := (59993618146667670586929168302733967940930416389051139740649685607605682388515052052543132786558580334160616565907231889455971052249306310813541305643014713150363276358091894250286300201806586527872065706638549181428753924102302365679799058235030882688855212140983317631064788115305912229673497367878847604154063768935116974149869237894761082324821579422959221526849662817662100026716723752381 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7, a6 := 10 }
def label : String := "336.c3"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7, a6 := 10 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -2, 0, -2, 0, 6, 0, 4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (23087877953176551906314425696014962560857509407618609031014918229456653878073953378537372361778593553234562766195300971393556065039566677965916120465875668763061629217377404849867008973243970656932546434173878204803478647593879240155831535383974389893238580824121795620487654939646522012412926172042123038013892520737817190702983729343015144953021398046982797888501212532947977793594852625663 : Rat)/68403348856590581990954744064501434060514841575789452334740569410267580079432994187338253250613276937186176552233372376224237979295804802965614699156269410859685167384013250633279050954534317771479762862199612122497410393933696532641119043589270111162490051104139895312173245378727720929378202636547629867983564407584128142991095084622647672020361691202785606652255176439645718200624632299520,            reHi := (59993618146667670586929168302733967940930416389051139740649685607605682388515052052543132786558580334160616565907231889455971052249306310813541305643014713150363276358091894250286300201806586527872065706638549181428753924102302365679799058235030882688855212140983317631064788115305912229673497367878847604154063768935116974149869237894761082324821579422959221526849662817662100026716723752381 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 48, a6 := -48 }
def label : String := "336.c4"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 48, a6 := -48 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -2, 0, -2, 0, 6, 0, 4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (23087877953176551906314425696014962560857509407618609031014918229456653878073953378537372361778593553234562766195300971393556065039566677965916120465875668763061629217377404849867008973243970656932546434173878204803478647593879240155831535383974389893238580824121795620487654939646522012412926172042123038013892520737817190702983729343015144953021398046982797888501212532947977793594852625663 : Rat)/68403348856590581990954744064501434060514841575789452334740569410267580079432994187338253250613276937186176552233372376224237979295804802965614699156269410859685167384013250633279050954534317771479762862199612122497410393933696532641119043589270111162490051104139895312173245378727720929378202636547629867983564407584128142991095084622647672020361691202785606652255176439645718200624632299520,            reHi := (59993618146667670586929168302733967940930416389051139740649685607605682388515052052543132786558580334160616565907231889455971052249306310813541305643014713150363276358091894250286300201806586527872065706638549181428753924102302365679799058235030882688855212140983317631064788115305912229673497367878847604154063768935116974149869237894761082324821579422959221526849662817662100026716723752381 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -21504, a6 := -1220940 }
def label : String := "336.d1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 1, 0],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -14624, a6 := 669300 }
def label : String := "336.d2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 0],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1664, a6 := -9804 }
def label : String := "336.d3"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 1, 0],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1344, a6 := -19404 }
def label : String := "336.d4"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 1, 1, 0, 0],              kodaira := -12 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -64, a6 := -460 }
def label : String := "336.d5"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1],              kodaira := -16 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d5

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 6176, a6 := -69388 }
def label : String := "336.d6"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0, 0],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_d6

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4032, a6 := -99900 }
def label : String := "336.e1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4032, a6 := -99900 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, -1, 0, 1, 0, 0, 0, 6, 0, 2, 0, -2, 0, -4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (19552266044302261360646297007017111014742837698153023052896322277856553166868020571113205040473558365997572535535377701031999554902121774129700842596733189653922842310416887614372899728573711369721252863033625705514627643358993465964136471311459556436394575163496653710643567202403449572241329095775313678877340142618246420535581473808469020692045983859036646250940728119449956885832481231427 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            reHi := (1349756653956192851357120155628567381742560819584244689762552909837163360227179114578847860882520621942927601710820738378302068200238615580677597033136301330735960839660749138392750787533926793884895866148943433465860934058262138477980573835428128295518319244499466743188001336073625063675424331735055692800888128053917485171778435134443578283111770943010257438153809565508411416298651080025351 : Rat)/478823441996134073936683208451510038423603891030526166343183985871873060556030959311367772754292938560303235865633606633569665855070633620759302894093885876017796171688092754432953356681740224400358340035397284857481872757535875728487833305124890778137430357728979267185212717651094046505647418455833409075884950853088897000937665592358533704142531838419499246565786235077520027404372426096640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -392, a6 := 228 }
def label : String := "336.e2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -392, a6 := 228 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, -1, 0, 1, 0, 0, 0, 6, 0, 2, 0, -2, 0, -4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (19552266044302261360646297007017111014742837698153023052896322277856553166868020571113205040473558365997572535535377701031999554902121774129700842596733189653922842310416887614372899728573711369721252863033625705514627643358993465964136471311459556436394575163496653710643567202403449572241329095775313678877340142618246420535581473808469020692045983859036646250940728119449956885832481231427 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            reHi := (1349756653956192851357120155628567381742560819584244689762552909837163360227179114578847860882520621942927601710820738378302068200238615580677597033136301330735960839660749138392750787533926793884895866148943433465860934058262138477980573835428128295518319244499466743188001336073625063675424331735055692800888128053917485171778435134443578283111770943010257438153809565508411416298651080025351 : Rat)/478823441996134073936683208451510038423603891030526166343183985871873060556030959311367772754292938560303235865633606633569665855070633620759302894093885876017796171688092754432953356681740224400358340035397284857481872757535875728487833305124890778137430357728979267185212717651094046505647418455833409075884950853088897000937665592358533704142531838419499246565786235077520027404372426096640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -252, a6 := -1620 }
def label : String := "336.e3"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -252, a6 := -1620 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, -1, 0, 1, 0, 0, 0, 6, 0, 2, 0, -2, 0, -4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (19552266044302261360646297007017111014742837698153023052896322277856553166868020571113205040473558365997572535535377701031999554902121774129700842596733189653922842310416887614372899728573711369721252863033625705514627643358993465964136471311459556436394575163496653710643567202403449572241329095775313678877340142618246420535581473808469020692045983859036646250940728119449956885832481231427 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            reHi := (1349756653956192851357120155628567381742560819584244689762552909837163360227179114578847860882520621942927601710820738378302068200238615580677597033136301330735960839660749138392750787533926793884895866148943433465860934058262138477980573835428128295518319244499466743188001336073625063675424331735055692800888128053917485171778435134443578283111770943010257438153809565508411416298651080025351 : Rat)/478823441996134073936683208451510038423603891030526166343183985871873060556030959311367772754292938560303235865633606633569665855070633620759302894093885876017796171688092754432953356681740224400358340035397284857481872757535875728487833305124890778137430357728979267185212717651094046505647418455833409075884950853088897000937665592358533704142531838419499246565786235077520027404372426096640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := -52 }
def label : String := "336.e4"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := -52 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, -1, 0, 1, 0, 0, 0, 6, 0, 2, 0, -2, 0, -4, 0, -1, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (19552266044302261360646297007017111014742837698153023052896322277856553166868020571113205040473558365997572535535377701031999554902121774129700842596733189653922842310416887614372899728573711369721252863033625705514627643358993465964136471311459556436394575163496653710643567202403449572241329095775313678877340142618246420535581473808469020692045983859036646250940728119449956885832481231427 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            reHi := (1349756653956192851357120155628567381742560819584244689762552909837163360227179114578847860882520621942927601710820738378302068200238615580677597033136301330735960839660749138392750787533926793884895866148943433465860934058262138477980573835428128295518319244499466743188001336073625063675424331735055692800888128053917485171778435134443578283111770943010257438153809565508411416298651080025351 : Rat)/478823441996134073936683208451510038423603891030526166343183985871873060556030959311367772754292938560303235865633606633569665855070633620759302894093885876017796171688092754432953356681740224400358340035397284857481872757535875728487833305124890778137430357728979267185212717651094046505647418455833409075884950853088897000937665592358533704142531838419499246565786235077520027404372426096640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -36, a6 := 72 }
def label : String := "336.f1"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -36, a6 := 72 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 4, 0, 1, 0, 1, 0, -2, 0, -6, 0, 4, 0, -4, 0, 4, 0, 1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (4972633371819543773541905357115519565507564872380488181694085548410429762518922578576667725969465339608634438240306539627684558757237042912395662302489242870415945593373356106537882790848792656677712965901243345768468166118894615318962954662313681178749243190691025211545416362368117253157534445253266832283973638187271612373781855303779722817726697080240118076871466361356265424236694198331571 : Rat)/5267057861957474813303515292966610422659642801335787829775023844590603666116340552425045500297222324163335594521969672969266324405776969828352331835032744636195757888569020298762486923499142468403941740389370133432300600332894633013366166356373798559511733935018771939037339894162034511562121603014167499834734459383977867010314321515943870745567850222614491712223648585852720301448096687063040,            reHi := (75280062019514322422840560155276519870824240421850302265604801427991601889211577877336290183934176534437905946378429658665890035315576887432459120825637502507727785058920270991599334925331544009198523836717239952390566640685543271805979946525953652481119974421582414303981413771876492531246985622195808046765414821491807149318372699522510492589997722175718192414981011498587887962318179806653 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 2 }
def label : String := "336.f2"
def inputConductor : Nat := 336
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 336 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 2 },   conductor := 336,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 4, 0, 1, 0, 1, 0, -2, 0, -6, 0, 4, 0, -4, 0, 4, 0, 1, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15745610193023844051361083984375,   alphaHi := (2698607540904403791726115815424 : Rat)/7872805096511921977996826171875,   geometricUpper := (1598321399510927 : Rat)/2251799813685248,   tail := (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/47218522599646280163982966313236370330075029303588123007024149580312483013162550218884588290941098423838786013394060267092052958983198071980985603305320736034242222878472272993417377467053451492232286405113441173017323237025859526692772981551349431826411430674756857438225971938610449644241177255141928111236674299667020886954516489172817318147082425562183961434748215717093247322947584,   box := { reLo := (4972633371819543773541905357115519565507564872380488181694085548410429762518922578576667725969465339608634438240306539627684558757237042912395662302489242870415945593373356106537882790848792656677712965901243345768468166118894615318962954662313681178749243190691025211545416362368117253157534445253266832283973638187271612373781855303779722817726697080240118076871466361356265424236694198331571 : Rat)/5267057861957474813303515292966610422659642801335787829775023844590603666116340552425045500297222324163335594521969672969266324405776969828352331835032744636195757888569020298762486923499142468403941740389370133432300600332894633013366166356373798559511733935018771939037339894162034511562121603014167499834734459383977867010314321515943870745567850222614491712223648585852720301448096687063040,            reHi := (75280062019514322422840560155276519870824240421850302265604801427991601889211577877336290183934176534437905946378429658665890035315576887432459120825637502507727785058920270991599334925331544009198523836717239952390566640685543271805979946525953652481119974421582414303981413771876492531246985622195808046765414821491807149318372699522510492589997722175718192414981011498587887962318179806653 : Rat)/25201233789270214417720168865868949390715994264764535070693893993256476871370050490071988039699628345279117677138610875451035045003717558987331731268099256632515587983583829180681755614828432863176754738705120255656940671449256617288833331848678462007233176722577856167642774613215476131876179918728074161888681623846784052680929768018870194954870096758921012977146643951448422494966969794560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48235067262611053048850633884937717039569817941580021455006690088234719369147887786274109047016615000162768496211535288047882677538850520286343552364966067212750719417184970149366882737929590231592291766457053720219102631883068949786079969190371002502367015583364924842981235605920484658431304351991994685614837532923107575614427144293203824186758871774110955639351015330632825705859375 : Rat)/94437045199292560327965932626472740660150058607176246014048299160624966026325100437769176581882196847677572026788120534184105917966396143961971206610641472068484445756944545986834754934106902984464572810226882346034646474051719053385545963102698863652822861349513714876451943877220899288482354510283856222473348599334041773909032978345634636294164851124367922869496431434186494645895168, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N336.C336_f2
