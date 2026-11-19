module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := -2 }
def label : String := "443.a1"
def inputConductor : Nat := 443
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.nonsingular
def minimality : MinimalityWitness := { primes := [443] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 443 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := -2 },   conductor := 443,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -2, -1, 0, 2, 1, 3, 1, 0, 3, 2, 3, -1, 0, -1, -5, -1, -7, 0, -2, -3, -3, -6, -5, -3, 4, -1, 0,                    0, 7, -5, -6, 5, 0, -1, -3, 7, -6, 0, -6, 2, -8, -3, 0, 3, -2, 2, -6, 5, 10, -3, 4, -4, 0, 3, 14, 0,                    6, 0, -13, -7, 1, 7],   alphaLo := (337325942613050473964690735104 : Rat)/1129982551348507785797119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18079720821576124477386474609375,   finite := ((10857180375269867 : Rat)/9007199254740992, (19053174612724939 : Rat)/9007199254740992),   tail := (21441257747596306570254270570278167724609375 : Rat)/22137025047770440122018584025881176080121856,   box := { reLo := (87954091114274671753501509067537015069892477089521 : Rat)/371397650823854992342172140216358081430237684432896,            reHi := (1145352207955522095843540074890020349367740933805457 : Rat)/371397650823854992342172140216358081430237684432896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 1, a6 := 1 }
def label : String := "443.b1"
def inputConductor : Nat := 443
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.nonsingular
def minimality : MinimalityWitness := { primes := [443] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 443 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 1, a6 := 1 },   conductor := 443,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -2, 0, 2, 0, -2, 0, -2, -2, -3, 0, -2, 4, -2, 0, -8, 4, 2, 0, 6, 0, -1, 0, -5, -4, -4,                    0, -10, 0, -2, 0, -4, 4, 7, 0, -3, 0, 10, 0, 4, 4, 4, 0, -7, 4, -3, 0, -2, 6, 12, 0, 4, 0, -8, 0, 5,                    4, -10, 0, -4, -8],   alphaLo := (337325942613050473964690735104 : Rat)/1129982551348507785797119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18079720821576124477386474609375,   finite := ((18754602724541079 : Rat)/9007199254740992, (36327598825788211 : Rat)/9007199254740992),   tail := (21441257747596306570254270570278167724609375 : Rat)/22137025047770440122018584025881176080121856,   box := { reLo := (413591842109878794329715452067863504362696341540277 : Rat)/371397650823854992342172140216358081430237684432896,            reHi := (1857635836930365542676224937541057711935558672177993 : Rat)/371397650823854992342172140216358081430237684432896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -84, a6 := -301 }
def label : String := "443.c1"
def inputConductor : Nat := 443
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.nonsingular
def minimality : MinimalityWitness := { primes := [443] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 443 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -84, a6 := -301 },   conductor := 443,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -2, -1, 4, -2, -1, -3, 1, 4, 5, 2, 3, -1, -8, -1, 3, 1, -1, -4, 2, 5, 3, 6, 11, 3, 4, 1, 4, -8,                    -7, 5],   alphaLo := (337325942613050473964690735104 : Rat)/1129982551348507785797119140625,   alphaHi := (5397215081808807583452231630848 : Rat)/18079720821576124477386474609375,   geometricUpper := (6682559226383301 : Rat)/9007199254740992,   tail := (660765637880290070403116262722639915256863426518381744955020513139086443643767864627895699027758751177993260754571698835893465029610831106466016150739305854119798712675220391105129321432570863021772108316979219242782767636176976226774375838582637410568479904675429005927041465051839655677342304618206095468286720441486395127542245731171531770777501387635452441804384315254729154812704294167501773598092812905674708324812711772289013164942143821463205702866104855923319516819456099211820080589239184306182644164042652999902547607 : Rat)/1223426115445167544401861367931832719085456567664431912469055184067329882644352608540598962640190332672937758709181584544234091556938482253623432223684422758978991619219949757766833649387057028396828492973700235922817238534189066769219265167886407211431392729559817305978757036785586391814789123367489347135842137999411194552014277118413513551473357207133089177235644821560492740722304393778617599545652180377230071266187509604018312025041974706674832396180437000878706869374351412464063015938472283604457106749545008142160494592,   box := { reLo := (43137185436699818492535130755719586654388949186112829003049567070458200871628314751705289220560733652825138785106920887112113956633733411439354635063997923889888066154560172487146257792099644496350790562696471403218639217225322650601707910115125376855360008114431453882419264106262572172883574814581280892835730162579702094142130684341259803181369468285698358626464460428988324815559901282205860376630226673484537681969757970752303602462398922343138235620726529587175138403546422923746859940963592058971887832583403767249472950941042067193 : Rat)/41510121657212836327196478998693340434596766373880709842016216082162583339321816857312386608232616308577995279384853619290499973929208481718142910096143845994033472889384192955361247722052680173717354439759233546003603832659224397366488773977210734932425187638746606811338368721675428912715995129447186017332028157654531230767799300350374528817481983945350050333579215700543596611130665694617079253918808260576012828276176120375826201036451532498945607353796185400834327323700380669395722281775075716319032395493501915176295970158883635200,            reHi := (87975956931023135894468479227308196749934503279686616115957295336321412051619613713564077263649972687876397373488094642837959249824975576039399027481841922998087090460905514038878551049074465759882581436238542380731094204697077706505244257820632217873864011197605417056637942073835162845982976942550723862536698171378554347002036198722127011652518020604182698012981746775919763199749489464514620392528682520487067629876155121362466326962039393747669731633466377414311068213784959034476619792637762173236026718511981916026435737477013321991 : Rat)/41510121657212836327196478998693340434596766373880709842016216082162583339321816857312386608232616308577995279384853619290499973929208481718142910096143845994033472889384192955361247722052680173717354439759233546003603832659224397366488773977210734932425187638746606811338368721675428912715995129447186017332028157654531230767799300350374528817481983945350050333579215700543596611130665694617079253918808260576012828276176120375826201036451532498945607353796185400834327323700380669395722281775075716319032395493501915176295970158883635200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (660765637880290070403116262722639915256863426518381744955020513139086443643767864627895699027758751177993260754571698835893465029610831106466016150739305854119798712675220391105129321432570863021772108316979219242782767636176976226774375838582637410568479904675429005927041465051839655677342304618206095468286720441486395127542245731171531770777501387635452441804384315254729154812704294167501773598092812905674708324812711772289013164942143821463205702866104855923319516819456099211820080589239184306182644164042652999902547607 : Rat)/2446852230890335088803722735863665438170913135328863824938110368134659765288705217081197925280380665345875517418363169088468183113876964507246864447368845517957983238439899515533667298774114056793656985947400471845634477068378133538438530335772814422862785459119634611957514073571172783629578246734978694271684275998822389104028554236827027102946714414266178354471289643120985481444608787557235199091304360754460142532375019208036624050083949413349664792360874001757413738748702824928126031876944567208914213499090016284320989184, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N443.C443_c1
