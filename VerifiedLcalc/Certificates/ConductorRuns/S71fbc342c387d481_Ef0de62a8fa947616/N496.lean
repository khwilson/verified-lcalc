module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 1 }
def label : String := "496.a1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 1 },   conductor := 496,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -3, 0, 3, 0, -3, 0, -2, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, -4, 0, 4, 0, 0, 0, -6, 0, -1,                    0, 0, 0, -9, 0, -10, 0, 0, 0, 7, 0, 10, 0, 9, 0, -12, 0, 2, 0, 0, 0, -4, 0, 6, 0, 0, 0, -3, 0, 12, 0,                    -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   finite := ((20304946712373075 : Rat)/9007199254740992, (38139936703034305 : Rat)/9007199254740992),   tail := (75506899911524340851033825102954864501953125 : Rat)/55441674714997872038041652469011887396225024,   box := { reLo := (51878690500961239918206653366600071254817088154525 : Rat)/58134809505953608670161563779346608838384050765824,            reHi := (325339806376854079852022006434608816402369103080335 : Rat)/58134809505953608670161563779346608838384050765824,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -5291, a6 := -148134 }
def label : String := "496.b1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -491, a6 := 154 }
def label : String := "496.b2"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -331, a6 := -2310 }
def label : String := "496.b3"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 0],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -70 }
def label : String := "496.b4"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4.nonsingular
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1],              kodaira := -12 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -17, a6 := 27 }
def label : String := "496.c1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -17, a6 := 27 },   conductor := 496,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, 1, 0, -3, 0, -3, 0, -6, 0, -4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 4, 0, -4, 0, 0, 0, 2, 0, 1, 0,                    0, 0, -3, 0, -2, 0, 0, 0, -9, 0, -2, 0, -3, 0, -4, 0, 2, 0, 0, 0, 12, 0, -6, 0, 0, 0, -9, 0, 12, 0,                    9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   finite := ((21227870300133607 : Rat)/9007199254740992, (39882904119496749 : Rat)/9007199254740992),   tail := (75506899911524340851033825102954864501953125 : Rat)/55441674714997872038041652469011887396225024,   box := { reLo := (57835479669888384004318824308837643009417782342729 : Rat)/58134809505953608670161563779346608838384050765824,            reHi := (336589371959384541952838267066857854531326841189603 : Rat)/58134809505953608670161563779346608838384050765824,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := -1 }
def label : String := "496.d1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := -1 },   conductor := 496,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, -3, 0, 1, 0, 1, 0, 6, 0, 2, 0, -6, 0, 6, 0, 1, 0, 2, 0, 6, 0, 4, 0, -4, 0, 0, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   geometricUpper := (6793055402987701 : Rat)/9007199254740992,   tail := (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/3445296365935042178354085803467402481248764700654807730895054507447868753459865578031499952397196960611606443969301127558480909432765734468635309245392039682829408922753860613305624069125148670559678983808241703529141537806365334813229852669458235901860929413703904306968083521496115569703911369175829108294048224480261744488777749872098476086518876568250956800536086641347037410646528718648378617827720665985214745373792997026157628228393577236796994238890305244783513600322308998676215783415520221494511969914035664615506968576,   box := { reLo := (37494221018431952768385971041595364566214779505469056813985582316296133587299181204447162112579750566144567251071786625603203132431146290314584208809528123832300475152331538237918327227296664472180504387836433411669462034883228723862796651324444182369777492029594488497270893847951740110422476459497672132483617466985890020681983305248555215667101585209796283227735509912530765269447268260741532133669300069154861219248286870176440392781674904419346838931894293911743626370332380104659170729829849788561011736493295115120275266092066866399 : Rat)/41239475796786200631938096345381126366412953881852378872964373212608041336607459963695096281741919215687605018052684027521321173121702412987336834285938536505955464114929617676316347911826149596081591947429519959812977440618561069335851335130027148981309782763846798929053257613012837970546855362200616319477297351276910078701742879249864300927352728980294818533241164800174841634777353580617753186286846910056513249265514999115054755524697976779868342989148762233367506769346611198476805227182546085190910716976109162826773080532477542400,            reHi := (1547327153906442485325187099841785665915158437350383050813766519983656116329828253421394192271040059561448343134927709347340941635589658952400832092550352129852098986650611656412223269328911374376420404026403563814905647850430105679791246816304818198084048641261072873734851481966553409566455294608032431515700195197584352828216641384392699317165245027294295148444836340560436595832151292324912643310764812257919030978188855140640735815249261113312936319480168090977629588145385044971185754227336101783584515198869200999643219021461050146989 : Rat)/536113185358220608215195252489954642763368400464080925348536851763904537375896979528036251662644949803938865234684892357777175250582131368835378845717200974577421033494085029792112522853739944749060695316583759477568706728041293901366067356690352936757027175930008386077692348969166893617109119708608012153204865566599831023122657430248235912055585476743832640932135142402272941252105596548030791421729009830734672240451694988495711821821073698138288458858933909033777588001505945580198467953373099107481839320689419116748050046922208051200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/6890592731870084356708171606934804962497529401309615461790109014895737506919731156062999904794393921223212887938602255116961818865531468937270618490784079365658817845507721226611248138250297341119357967616483407058283075612730669626459705338916471803721858827407808613936167042992231139407822738351658216588096448960523488977555499744196952173037753136501913601072173282694074821293057437296757235655441331970429490747585994052315256456787154473593988477780610489567027200644617997352431566831040442989023939828071329231013937152, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 18, a6 := 11 }
def label : String := "496.d2"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 18, a6 := 11 },   conductor := 496,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, -3, 0, 1, 0, 1, 0, 6, 0, 2, 0, -6, 0, 6, 0, 1, 0, 2, 0, 6, 0, 4, 0, -4, 0, 0, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   geometricUpper := (6793055402987701 : Rat)/9007199254740992,   tail := (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/3445296365935042178354085803467402481248764700654807730895054507447868753459865578031499952397196960611606443969301127558480909432765734468635309245392039682829408922753860613305624069125148670559678983808241703529141537806365334813229852669458235901860929413703904306968083521496115569703911369175829108294048224480261744488777749872098476086518876568250956800536086641347037410646528718648378617827720665985214745373792997026157628228393577236796994238890305244783513600322308998676215783415520221494511969914035664615506968576,   box := { reLo := (37494221018431952768385971041595364566214779505469056813985582316296133587299181204447162112579750566144567251071786625603203132431146290314584208809528123832300475152331538237918327227296664472180504387836433411669462034883228723862796651324444182369777492029594488497270893847951740110422476459497672132483617466985890020681983305248555215667101585209796283227735509912530765269447268260741532133669300069154861219248286870176440392781674904419346838931894293911743626370332380104659170729829849788561011736493295115120275266092066866399 : Rat)/41239475796786200631938096345381126366412953881852378872964373212608041336607459963695096281741919215687605018052684027521321173121702412987336834285938536505955464114929617676316347911826149596081591947429519959812977440618561069335851335130027148981309782763846798929053257613012837970546855362200616319477297351276910078701742879249864300927352728980294818533241164800174841634777353580617753186286846910056513249265514999115054755524697976779868342989148762233367506769346611198476805227182546085190910716976109162826773080532477542400,            reHi := (1547327153906442485325187099841785665915158437350383050813766519983656116329828253421394192271040059561448343134927709347340941635589658952400832092550352129852098986650611656412223269328911374376420404026403563814905647850430105679791246816304818198084048641261072873734851481966553409566455294608032431515700195197584352828216641384392699317165245027294295148444836340560436595832151292324912643310764812257919030978188855140640735815249261113312936319480168090977629588145385044971185754227336101783584515198869200999643219021461050146989 : Rat)/536113185358220608215195252489954642763368400464080925348536851763904537375896979528036251662644949803938865234684892357777175250582131368835378845717200974577421033494085029792112522853739944749060695316583759477568706728041293901366067356690352936757027175930008386077692348969166893617109119708608012153204865566599831023122657430248235912055585476743832640932135142402272941252105596548030791421729009830734672240451694988495711821821073698138288458858933909033777588001505945580198467953373099107481839320689419116748050046922208051200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/6890592731870084356708171606934804962497529401309615461790109014895737506919731156062999904794393921223212887938602255116961818865531468937270618490784079365658817845507721226611248138250297341119357967616483407058283075612730669626459705338916471803721858827407808613936167042992231139407822738351658216588096448960523488977555499744196952173037753136501913601072173282694074821293057437296757235655441331970429490747585994052315256456787154473593988477780610489567027200644617997352431566831040442989023939828071329231013937152, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -1 }
def label : String := "496.e1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -1 },   conductor := 496,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, -2, 0, 2, 0, -6, 0, -1, 0, 6, 0, 6, 0, -4, 0, -4, 0, 4, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   geometricUpper := (6793055402987701 : Rat)/9007199254740992,   tail := (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/3445296365935042178354085803467402481248764700654807730895054507447868753459865578031499952397196960611606443969301127558480909432765734468635309245392039682829408922753860613305624069125148670559678983808241703529141537806365334813229852669458235901860929413703904306968083521496115569703911369175829108294048224480261744488777749872098476086518876568250956800536086641347037410646528718648378617827720665985214745373792997026157628228393577236796994238890305244783513600322308998676215783415520221494511969914035664615506968576,   box := { reLo := (20738654271290535596277626771014441377962430848795457499396863839989556171011588184578616345147846090693524982398590012908679731142574310159044342033795161977526964865968461649355091730626000792992358245294127482584768673003053002478097121503548436128701453196194132545123817025355930359011244032053178478950864666993447913028604945927803446769628006960819652299949958071276878687957773452277681689411849896480100450486083656928627020171152236798527156158986444673377156798764245460292035923754364264487218661464475561358252674616116246096999 : Rat)/15547282375388397638240662322208684640137683613458346835107568701153231583901012406313051298216703544314227091805861878375538082266881809696225986525798828262745209971328465863971263162758458397722760164180929024849492495113197523139615953344020235165953788101970243196253078120105839914896164471549632352442941101431395099670557065477198841449611978825571146587031919129665915296311062299892892951230141285091305494973099154666375642832811137246010365306909083361979550052043672421825755570647819874116973340299993154385693451360744033484800,            reHi := (3959678493125270848202218369318217230771109262931113212706109111623215923354915688196798519981721053654406496470138125147140451633706288046344521979510115329537010179009734999777426426096230022752253399297339497350613551267009705534977178911583516912759898990314685203613190500373958080092971826071874425299071576058687225590987626345067038194538510774122138251721876698082807350257380606374320478984725425406483409721794517759795483753046727786965055054805276637430221027499023432091890436917931049351448055441923385821135152224880548672189 : Rat)/1195944798106799818326204794016052664625975662573718987315966823165633198761616338947157792170515657254940545523527836798118314020529369976632768194292217558672708459332958912613174089442958338286366166475456078834576345777938271010739688718770787320457983700151557168942544470777372301145858805503817873264841623187030392282350543498246064726893229140428549737463993779205070407408543253837914842402318560391638884228699934974336587910216241326616181946685314104767657696311051724755827351588293836470536410792307165721976419335441848729600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/6890592731870084356708171606934804962497529401309615461790109014895737506919731156062999904794393921223212887938602255116961818865531468937270618490784079365658817845507721226611248138250297341119357967616483407058283075612730669626459705338916471803721858827407808613936167042992231139407822738351658216588096448960523488977555499744196952173037753136501913601072173282694074821293057437296757235655441331970429490747585994052315256456787154473593988477780610489567027200644617997352431566831040442989023939828071329231013937152, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := 32 }
def label : String := "496.f1"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 31, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := 32 },   conductor := 496,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, 2, 0, 0, 0, 1, 0, -2, 0, 4, 0, 4, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, -4, 0, -4, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   geometricUpper := (6793055402987701 : Rat)/9007199254740992,   tail := (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/3445296365935042178354085803467402481248764700654807730895054507447868753459865578031499952397196960611606443969301127558480909432765734468635309245392039682829408922753860613305624069125148670559678983808241703529141537806365334813229852669458235901860929413703904306968083521496115569703911369175829108294048224480261744488777749872098476086518876568250956800536086641347037410646528718648378617827720665985214745373792997026157628228393577236796994238890305244783513600322308998676215783415520221494511969914035664615506968576,   box := { reLo := (9770030513585629186737117568592075360151497450351828229679864151726818668466258945776719432965197986839965180290909517996881764709061225418805548620134590266886316988206723634661337035181626706043010764049407495360629137685667136863308630196868931995994113228141629529832440992668360217064497129940856724709203788574243806485528716603365057054497035116243848620786705997503711588067460005601152012207905586226087194734081372921922094242404036170375345952398492579574367614020079107874151342658513181002885224173754994649398257035714883427 : Rat)/7428228559669564088982638472149395432459476165054155200720290827115734153798859248118992497953513399099009599525017619864088906959809751407656945306162841979333592915111546041075615462378623219169976189288547073506685377502722180190929743594849610686074432920196007260512698576256970814570551586980235237669823746503294362002177288808981768490020056772848135015304309187609132965270454992782079766474028325413906113221738726548674459069666095196373800911088907483028929790751874066806381065765800226525070874486379911316623722580384153600,            reHi := (317924472076227976924947381579387173214704620348624213290718800258572916013262215284334605663905437753466412627603066059818867408652764052769116895482857138626878531081062994207176903349936417753519018915654546438560519553425078292689092291322477132398391840904364637490119116819063623631123329928578634301275887635284394300392694307374747676361452149072783925158173832433754968127205689893576343464037683082871172657285668778935695875997689473035848930586020032484314905301032171471990566446022564220161275171158947270777743825183955671033 : Rat)/96566971275704333156774300137942140621973190145704017609363780752504543999385170225546902473395674188287124793825229058233155790477526768299540288980116945731336707896450098533983001010922101849209690460751111955586909907535388342482086666733044938918967627962548094386665081491340620589417170630743058089707708704542826706028304754516762990370260738047025755198956019438918728548515914906167036964162368230380779471882603445132767967905659237552859411844155797279376087279774362868482953854955402944825921368322938847116108393544993996800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/6890592731870084356708171606934804962497529401309615461790109014895737506919731156062999904794393921223212887938602255116961818865531468937270618490784079365658817845507721226611248138250297341119357967616483407058283075612730669626459705338916471803721858827407808613936167042992231139407822738351658216588096448960523488977555499744196952173037753136501913601072173282694074821293057437296757235655441331970429490747585994052315256456787154473593988477780610489567027200644617997352431566831040442989023939828071329231013937152, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := 0 }
def label : String := "496.f2"
def inputConductor : Nat := 496
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 31] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 496 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := 0 },   conductor := 496,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, 0, 2, 0, 0, 0, 1, 0, -2, 0, 4, 0, 4, 0, 6, 0, -4, 0, 0, 0, 0, 0, -1, 0, -4, 0, -4, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/19130692680151377773284912109375,   alphaHi := (2698607540904403791726115815424 : Rat)/9565346340075688838958740234375,   geometricUpper := (6793055402987701 : Rat)/9007199254740992,   tail := (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/3445296365935042178354085803467402481248764700654807730895054507447868753459865578031499952397196960611606443969301127558480909432765734468635309245392039682829408922753860613305624069125148670559678983808241703529141537806365334813229852669458235901860929413703904306968083521496115569703911369175829108294048224480261744488777749872098476086518876568250956800536086641347037410646528718648378617827720665985214745373792997026157628228393577236796994238890305244783513600322308998676215783415520221494511969914035664615506968576,   box := { reLo := (9770030513585629186737117568592075360151497450351828229679864151726818668466258945776719432965197986839965180290909517996881764709061225418805548620134590266886316988206723634661337035181626706043010764049407495360629137685667136863308630196868931995994113228141629529832440992668360217064497129940856724709203788574243806485528716603365057054497035116243848620786705997503711588067460005601152012207905586226087194734081372921922094242404036170375345952398492579574367614020079107874151342658513181002885224173754994649398257035714883427 : Rat)/7428228559669564088982638472149395432459476165054155200720290827115734153798859248118992497953513399099009599525017619864088906959809751407656945306162841979333592915111546041075615462378623219169976189288547073506685377502722180190929743594849610686074432920196007260512698576256970814570551586980235237669823746503294362002177288808981768490020056772848135015304309187609132965270454992782079766474028325413906113221738726548674459069666095196373800911088907483028929790751874066806381065765800226525070874486379911316623722580384153600,            reHi := (317924472076227976924947381579387173214704620348624213290718800258572916013262215284334605663905437753466412627603066059818867408652764052769116895482857138626878531081062994207176903349936417753519018915654546438560519553425078292689092291322477132398391840904364637490119116819063623631123329928578634301275887635284394300392694307374747676361452149072783925158173832433754968127205689893576343464037683082871172657285668778935695875997689473035848930586020032484314905301032171471990566446022564220161275171158947270777743825183955671033 : Rat)/96566971275704333156774300137942140621973190145704017609363780752504543999385170225546902473395674188287124793825229058233155790477526768299540288980116945731336707896450098533983001010922101849209690460751111955586909907535388342482086666733044938918967627962548094386665081491340620589417170630743058089707708704542826706028304754516762990370260738047025755198956019438918728548515914906167036964162368230380779471882603445132767967905659237552859411844155797279376087279774362868482953854955402944825921368322938847116108393544993996800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3405696386097740584166362263356047576614712246757217788810033394896116736415398283917461766830717076645069335618950172657162756572770620735363904826385720241332530751100841303254109008010632503614398898358939257030487116926650456132576929624743568961257070349207252096873277448253992419715260708650280352113373914356329641768138355098027128888826032234946949275189883842950520227665343402187841346526763983856723146091858467916354373230054291600176523144866028501067358503405545515085987070240205852891103857206953578778134372021 : Rat)/6890592731870084356708171606934804962497529401309615461790109014895737506919731156062999904794393921223212887938602255116961818865531468937270618490784079365658817845507721226611248138250297341119357967616483407058283075612730669626459705338916471803721858827407808613936167042992231139407822738351658216588096448960523488977555499744196952173037753136501913601072173282694074821293057437296757235655441331970429490747585994052315256456787154473593988477780610489567027200644617997352431566831040442989023939828071329231013937152, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N496.C496_f2
