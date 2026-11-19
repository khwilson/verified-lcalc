module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -28, a6 := -59 }
def label : String := "427.a1"
def inputConductor : Nat := 427
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.nonsingular
def minimality : MinimalityWitness := { primes := [7, 7, 7, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 427 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -28, a6 := -59 },   conductor := 427,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, -1, 0, -1, -1, 3, -2, 0, -5, -1, 4, 1, 0, -1, -5, 2, -7, 0, -1, 5, 9, 3, -5, -4, -5, 1, -6,                    0, 0, -5, -5, 5, 0, 2, 2, 7, 4, 0, -10, 1, 1, 5, 0, -9, 7, -1, 1, 5, -5, -4, -6, 5, 0, -3, -7, 6, -6,                    0, -1, 0, 2, 7],   alphaLo := (5397215081808807583435051761664 : Rat)/17750222217734603404998779296875,   alphaHi := (2698607540904403791726115815424 : Rat)/8875111108867301654815673828125,   finite := ((3601218084447677 : Rat)/2251799813685248, (14504921512799731 : Rat)/4503599627370496),   tail := (1232923072563442785502797614108562469482421875 : Rat)/1425458909241632906358378367222101959122092032,   box := { reLo := (274401677017033141050544152416719354460155070794817 : Rat)/373675500304238616604410738697070695972101693636608,            reHi := (3053429709799146321335592065775260685317716115535151 : Rat)/747351000608477233208821477394141391944203387273216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := -1 }
def label : String := "427.b1"
def inputConductor : Nat := 427
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.nonsingular
def minimality : MinimalityWitness := { primes := [7, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 427 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := -1 },   conductor := 427,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 0, 2, -2, 4, 0, 1, 0, 1, 0, -2, -4, 2, 0, 8, 4, 5, 0, -8, -8, 2, 0, -6, 0, 11, 0, -4, -2, 2, 0, 1,                    0],   alphaLo := (5397215081808807583435051761664 : Rat)/17750222217734603404998779296875,   alphaHi := (2698607540904403791726115815424 : Rat)/8875111108867301654815673828125,   geometricUpper := (6645630201594661 : Rat)/9007199254740992,   tail := (1651008873320096884386119173612613644666804406705191729489274209657716026545249053469633651247017003869301614039199411953289687979371775120563634582890587114448121211114330005155497091343639544790141803542914386865249430739696119776913141077327315341850598613551176286304866732715957982173411459462913217862012836267695582150557668534665873799787038744833750124477768061272551238326378526620705803047022892357743938177412974111542347280988600685625499411302723426027710615500392106152011619795411489833850563311076360193493176101 : Rat)/3745469772740704426360643754909062662251475202585190436162006901559411278471351319035268177819135994556328346615425150285924808889148408240081342385386279948326251037326356183752322993878344375114547510187366388172122293004189564463903199640412033780911367447969028805381520435976675723924888983435854609213888485864267514328489593231398317198225266468143411364282543506483473680222973882116717410860095171564258200865751879047045555194914194655956898939337891431692716034599311868318326426484429358453622859174181513113314000896,   box := { reLo := (1478544872029001891693760215525419274435402928421329665793807229145663051609744333456621044891729627570163362480007928870152101627732983767946797012169606609227488138078056182342968277657872570227209565737142683274048384896488787016711952685562111869172606480585917137882385349182882854034240770282138196625933784154411150807328680156186677992227171680829169475463868526546468654523105806465988021708103675677425239780465994269355599922882947606209396184217707718753904795733780451538448406385848502587098446030146848053546429062625811103949 : Rat)/889570957959444544522521162189732475010571926778189675342679634519839958673707531497660323749286998164747371817581546425929724184237851362429000349859571171358333661937415038003013181526945741735936843661466360330420807498023363517211172067737696743716751058036679106895612510862742146835004567949156850862396552441172318940056320496031867502999922405395561780152167120153995898217667205967323575276216770027153496315732195359709921698022319351504800181428468656445943011980438452399453434554399616382023754683067408132147566346662785843200,            reHi := (144757825812941630905498334791913313498367000756695896719932283759371483378312142485539620631809511034415124214951773272647653130076545876495905199844102126283441756544492346128243616048737284174300572812883163968125399792614685990990100403470104507639486820581277541765369648419889401509715069016577142047870083103952499621770646442499857627533567137888128535183100732093504563978037814200300968754534998110960024879398593930046967792931415710941503305380118950360509976002276644256155186472487207109992927708525172512181878669046041036449 : Rat)/56908579802119347966087212395976151600002917874699002799700043959181680857913949826449650340863477997071380688666832936338938584176832242040912480294046640591947271302393554619721381983205283141356229055784043253461263779334827969114519425208808882594674310110090582596015615173037376396852144077555488775708870358189474949027172018264664924434338470378840652602327189504801084397763221930569521650667066096013186632992968726715449536237118072991889573896097321456137768443193032308382542951291557950365156023495894796332672594567652966400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1651008873320096884386119173612613644666804406705191729489274209657716026545249053469633651247017003869301614039199411953289687979371775120563634582890587114448121211114330005155497091343639544790141803542914386865249430739696119776913141077327315341850598613551176286304866732715957982173411459462913217862012836267695582150557668534665873799787038744833750124477768061272551238326378526620705803047022892357743938177412974111542347280988600685625499411302723426027710615500392106152011619795411489833850563311076360193493176101 : Rat)/7490939545481408852721287509818125324502950405170380872324013803118822556942702638070536355638271989112656693230850300571849617778296816480162684770772559896652502074652712367504645987756688750229095020374732776344244586008379128927806399280824067561822734895938057610763040871953351447849777966871709218427776971728535028656979186462796634396450532936286822728565087012966947360445947764233434821720190343128516401731503758094091110389828389311913797878675782863385432069198623736636652852968858716907245718348363026226628001792, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 7 }
def label : String := "427.c1"
def inputConductor : Nat := 427
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.nonsingular
def minimality : MinimalityWitness := { primes := [7, 61] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 427 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 7 },   conductor := 427,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 1, -1, -4, 1, 1, -3, -2, -4, -3, -1, -4, 1, -4, -1, 5, -2, 1, 4, 1, -3, 7, -3, 11, -4, -5, -1,                    -10, -4, -8, 5, -3, 5, -4, 2, 10, 1, -4, 12],   alphaLo := (5397215081808807583435051761664 : Rat)/17750222217734603404998779296875,   alphaHi := (2698607540904403791726115815424 : Rat)/8875111108867301654815673828125,   finite := ((13552209051582569 : Rat)/9007199254740992, (54412232768737509 : Rat)/9007199254740992),   tail := (1232923072563442785502797614108562469482421875 : Rat)/1425458909241632906358378367222101959122092032,   box := { reLo := (956111279332202082992301825125160774316808717133149 : Rat)/1494702001216954466417642954788282783888406774546432,            reHi := (10322265530968180472323872343249056416682398152778889 : Rat)/1494702001216954466417642954788282783888406774546432,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N427.C427_c1
