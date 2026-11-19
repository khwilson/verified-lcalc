module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -10, a6 := 17 }
def label : String := "460.a1"
def inputConductor : Nat := 460
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 460 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -10, a6 := 17 },   conductor := 460,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 1, 0, -2, 0, -2, 0, -4, 0, 1, 0, -1, 0, 0, 0, -4, 0, 2, 0, -1, 0, 1, 0, 5, 0, -7, 0, -7,                    0, 4, 0, -2, 0, -4, 0, -1, 0, 3, 0, 6, 0, -2, 0, -13, 0, -3, 0, 0, 0, 10, 0, -4, 0, 4, 0, -8, 0, 0,                    0, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/9211678605936267566680908203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18423357211872535037994384765625,   finite := ((18185976536749927 : Rat)/9007199254740992, (17288780081379599 : Rat)/4503599627370496),   tail := (382154110508218217157271896268367767333984375 : Rat)/351806755566370549440996306953805120023822336,   box := { reLo := (688203420218616203054579269104586642111382208711657 : Rat)/737792241049525130501284287120786315068199059587072,            reHi := (1816865694200052747921484722665153648865183656540609 : Rat)/368896120524762565250642143560393157534099529793536,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -12 }
def label : String := "460.b1"
def inputConductor : Nat := 460
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 460 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -12 },   conductor := 460,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 0, 0, -1, 0, -1, 0, -3, 0, 6, 0, 6, 0, 0, 0, 7, 0, 2, 0, 0, 0, -1, 0, 1, 0, 0, 0, -5, 0, 1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/9211678605936267566680908203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18423357211872535037994384765625,   geometricUpper := (419992017862815 : Rat)/562949953421312,   tail := (48614682646068241700173740940364997687333754859620354192346274989702127647797040873468572408827890098218247618296334948855332999057406896705309594510957168213122925107056470789915830040224094205297694492549158843019071040520591205849451917751762071268085885301755549800006064339378941343673973086791987524172339189310434080937832780739399383532345980132882129075964279131523986184915378247981265712469795169503343032163271900677164866562843168684116051805412435963167808949947357177734375 : Rat)/73352173688283820640559013515245108970302665733226418368215786945607145689533706860963847851823013110820363500667703324444140078599926161769190957988472805823352364575220460221572316832665234968056164950365866533982187580174614344153696238431935732702910682427516050115277458698769993698022364371473225036846919820605028531982445665695355941504237791908706247203686499071077756079832289891358193921394853844611270299859645694647734342498768306455360843034531067676429820243865774090878976,   box := { reLo := (26580687563592295436626598307376395690094919034952566720906427078993537783445460079918465306771066953199866829738064328261939480215998287416427983879320706984814420441505783919299323448759411396097943570733791566392968771754515860462758777675990959250674318377551942358262110180282343690476433313191790648053095122033053174194633835931677118355024241992842829776435632176110707618843608009678701745255892261286487232013278417695360386115357785655125941741716720781059607303275212311001174605797478821 : Rat)/36778869767557732265548815769517133205422905634753615735484482608536561974807992647976632723430927808798870275196692902529867859925944787965596516169330862065269671097251661887106780657997471798512398339533763287194079604423548309617984544077615932988891090363188493023904225293915354910530941525110298508904513872503390488792584208169886787232243852543197682883410765491397861166779378672027609560666346450837378076654406526816734793563965651159993034112538868619742412491643789443996356472681267200,            reHi := (1321607201028799850089893167779023498327740274832875042694814081741677753270733689043265298117936642470933636605685091048410142096451295154152711552199337311448903964881679127971261366310320900386417161066247874259914699865687193059999000939197727417866187327890076025336207589816743545175191776968870426733498840586680537278443449656068308359150594616058620052245638624804565830340543850519895780374835629148203038204991399492090270305367144391566173755060515353478437242545070477699803438641298227 : Rat)/645243329255398811676295013500300582551279046223747644482183905412922139908912151718888293393525049277173162722748998289997681753086750666063096774900541439741573177144765998019417204526271435061621023500592338371825957972342952800315518317151156719103352462512078824980775882349392191412823535528250851033412524079006850680571652774910294512846383377950836541814223955989436160820690853895221220362567481593638211871129939066960259536209923704561281300219980151223551096344627884982392218818969600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48614682646068241700173740940364997687333754859620354192346274989702127647797040873468572408827890098218247618296334948855332999057406896705309594510957168213122925107056470789915830040224094205297694492549158843019071040520591205849451917751762071268085885301755549800006064339378941343673973086791987524172339189310434080937832780739399383532345980132882129075964279131523986184915378247981265712469795169503343032163271900677164866562843168684116051805412435963167808949947357177734375 : Rat)/146704347376567641281118027030490217940605331466452836736431573891214291379067413721927695703646026221640727001335406648888280157199852323538381915976945611646704729150440920443144633665330469936112329900731733067964375160349228688307392476863871465405821364855032100230554917397539987396044728742946450073693839641210057063964891331390711883008475583817412494407372998142155512159664579782716387842789707689222540599719291389295468684997536612910721686069062135352859640487731548181757952, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -46, a6 := 529 }
def label : String := "460.c1"
def inputConductor : Nat := 460
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 460 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -46, a6 := 529 },   conductor := 460,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -1, 0, -4, 0, -2, 0, -6, 0, -1, 0, -1, 0, 0, 0, 2, 0, -4, 0, 1, 0, 1, 0, -5, 0, 9, 0, 5,                    0, -6, 0, 4, 0, 2, 0, -1, 0, -9, 0, -4, 0, 2, 0, -3, 0, 9, 0, 0, 0, -6, 0, 6, 0, 2, 0, 0, 0, 2, 0, 8,                    0],   alphaLo := (2698607540904403791717525880832 : Rat)/9211678605936267566680908203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18423357211872535037994384765625,   finite := ((20535840481392689 : Rat)/9007199254740992, (40788615102447739 : Rat)/9007199254740992),   tail := (382154110508218217157271896268367767333984375 : Rat)/351806755566370549440996306953805120023822336,   box := { reLo := (880684050084432873267524714602967636860827261292799 : Rat)/737792241049525130501284287120786315068199059587072,            reHi := (4142487552623132193994122991592105043850790728947349 : Rat)/737792241049525130501284287120786315068199059587072,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 414, a6 := -13915 }
def label : String := "460.c2"
def inputConductor : Nat := 460
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 460 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 414, a6 := -13915 },   conductor := 460,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -1, 0, -4, 0, -2, 0, -6, 0, -1, 0, -1, 0, 0, 0, 2, 0, -4, 0, 1, 0, 1, 0, -5, 0, 9, 0, 5,                    0, -6, 0, 4, 0, 2, 0, -1, 0, -9, 0, -4, 0, 2, 0, -3, 0, 9, 0, 0, 0, -6, 0, 6, 0, 2, 0, 0, 0, 2, 0, 8,                    0],   alphaLo := (2698607540904403791717525880832 : Rat)/9211678605936267566680908203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18423357211872535037994384765625,   finite := ((20535840481392689 : Rat)/9007199254740992, (40788615102447739 : Rat)/9007199254740992),   tail := (382154110508218217157271896268367767333984375 : Rat)/351806755566370549440996306953805120023822336,   box := { reLo := (880684050084432873267524714602967636860827261292799 : Rat)/737792241049525130501284287120786315068199059587072,            reHi := (4142487552623132193994122991592105043850790728947349 : Rat)/737792241049525130501284287120786315068199059587072,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -73, a6 := 2453 }
def label : String := "460.d1"
def inputConductor : Nat := 460
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 23, 23, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 460 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -73, a6 := 2453 },   conductor := 460,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 3, 0, -1, 0, 2, 0, 6, 0, 0, 0, -3, 0, -3, 0, 4, 0, -4, 0, 6, 0, -1, 0, 1, 0, 9, 0, 1, 0, 1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/9211678605936267566680908203125,   alphaHi := (5397215081808807583452231630848 : Rat)/18423357211872535037994384765625,   geometricUpper := (419992017862815 : Rat)/562949953421312,   tail := (48614682646068241700173740940364997687333754859620354192346274989702127647797040873468572408827890098218247618296334948855332999057406896705309594510957168213122925107056470789915830040224094205297694492549158843019071040520591205849451917751762071268085885301755549800006064339378941343673973086791987524172339189310434080937832780739399383532345980132882129075964279131523986184915378247981265712469795169503343032163271900677164866562843168684116051805412435963167808949947357177734375 : Rat)/73352173688283820640559013515245108970302665733226418368215786945607145689533706860963847851823013110820363500667703324444140078599926161769190957988472805823352364575220460221572316832665234968056164950365866533982187580174614344153696238431935732702910682427516050115277458698769993698022364371473225036846919820605028531982445665695355941504237791908706247203686499071077756079832289891358193921394853844611270299859645694647734342498768306455360843034531067676429820243865774090878976,   box := { reLo := (303429900281935527898359545688159866996003349355641402946299432348500060285105836929822080105609789577789993393134469582322131081507198199243833802626666835497794442731063734386956403988414612874906143971826016648576585051857769996955573458579416192068105590881666392286389042431944901018209094629208114471545874361738880211326319464084602079853236175502987008879750103671714877773347311180602363112722912764465157814696732751339074602460462836689975335071735006614094810152916401071521051211683989 : Rat)/175975453433290585002625912772809249786712467151931175767868337839887856338794223196060443652779558893774498924386090442726640478114568363471753665881965847202247230130390726732568328507164936834987551863797910465043443083366259854631504995586679105210005217048748770449302513368016052203497327871341141190930688385183686549246814393157353048958104557622955420494788351633482589314733869244151241917063858616446785055762710654625525328057251919425803990969085495788241208093989423177016059677900800,            reHi := (10197070186724894564815473350859878637602050033192255083285720669994573113383104068469848361229074879449350447879513699350453067142763542823899144756029919681430971756691229837265288120511929612043731161124124926414081821821455011544149247511223854296142384787727676540403372144428229666518813606735966690253930295459438530322623803503885501679461307063215892493862683789643397457468239256126091493883547508051870712664536323402824097735642974987041298966132497171521125536554157652584999978485705969 : Rat)/3343533615232521115049892342683375745947536875886692339589498418957869270437090240725148429402811618981715479563335718411806169084176798905963319651757351096842697372477423807918798241636133799864763485412160298835825418583958937237998594916146902998990099123926226638536747753992304991866449229555481682627683079318490044435689473469989707930203986594836152989400978681036169196979943515638873596424213313712488916059491502437884981233087786469090275828412624419976582953785799040363305133880115200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (48614682646068241700173740940364997687333754859620354192346274989702127647797040873468572408827890098218247618296334948855332999057406896705309594510957168213122925107056470789915830040224094205297694492549158843019071040520591205849451917751762071268085885301755549800006064339378941343673973086791987524172339189310434080937832780739399383532345980132882129075964279131523986184915378247981265712469795169503343032163271900677164866562843168684116051805412435963167808949947357177734375 : Rat)/146704347376567641281118027030490217940605331466452836736431573891214291379067413721927695703646026221640727001335406648888280157199852323538381915976945611646704729150440920443144633665330469936112329900731733067964375160349228688307392476863871465405821364855032100230554917397539987396044728742946450073693839641210057063964891331390711883008475583817412494407372998142155512159664579782716387842789707689222540599719291389295468684997536612910721686069062135352859640487731548181757952, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N460.C460_d1
