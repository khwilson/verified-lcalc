module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -103, a6 := -402 }
def label : String := "380.a1"
def inputConductor : Nat := 380
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 380 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -103, a6 := -402 },   conductor := 380,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, -4, 0, -4, 0, 0, 0, 6, 0, 1, 0, 0, 0, -2, 0, 1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, 4, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16744865180716899013519287109375,   alphaHi := (2698607540904403791726115815424 : Rat)/8372432590358449459075927734375,   finite := ((12376478736776007 : Rat)/9007199254740992, (17603842997298613 : Rat)/4503599627370496),   tail := (54279829864788229131221375520992279052734375 : Rat)/90574934935622616063987595079344763055374336,   box := { reLo := (73584904103774489157522887004227145545759232664531 : Rat)/94974702975055420261911856497919014265552199745536,            reHi := (214078644715486080114930228606574149749614787955929 : Rat)/47487351487527710130955928248959507132776099872768,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -3 }
def label : String := "380.a2"
def inputConductor : Nat := 380
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 380 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := -3 },   conductor := 380,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, 0, -1, 0, -2, 0, -3, 0, -4, 0, -4, 0, 0, 0, 6, 0, 1, 0, 0, 0, -2, 0, 1, 0, 0, 0, -6, 0, -8,                    0, 0, 0, 2, 0, 4, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16744865180716899013519287109375,   alphaHi := (2698607540904403791726115815424 : Rat)/8372432590358449459075927734375,   finite := ((12376478736776007 : Rat)/9007199254740992, (17603842997298613 : Rat)/4503599627370496),   tail := (54279829864788229131221375520992279052734375 : Rat)/90574934935622616063987595079344763055374336,   box := { reLo := (73584904103774489157522887004227145545759232664531 : Rat)/94974702975055420261911856497919014265552199745536,            reHi := (214078644715486080114930228606574149749614787955929 : Rat)/47487351487527710130955928248959507132776099872768,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -921, a6 := 10346 }
def label : String := "380.b1"
def inputConductor : Nat := 380
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 380 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -921, a6 := 10346 },   conductor := 380,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, -1, 0, 2, 0, 1, 0, 0, 0, 6, 0, -2, 0, 2, 0, -1, 0, 4, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16744865180716899013519287109375,   alphaHi := (2698607540904403791726115815424 : Rat)/8372432590358449459075927734375,   geometricUpper := (6525408583447057 : Rat)/9007199254740992,   tail := (90563413106715595058350669573772152969990135915438270918668761666683591515818737195561805401361320471774106976011655300978199974431664362082067185519669991832687521425020871231865650129121706277081678669893732155325053138590076751660577633246675746539065756294531516565586920623027000667410854033580771770965532597728674045889573589166718207907841613067564215195355022813288036290689722803252756640625 : Rat)/49532135267899603195322522632882915117932496838455434029076101117417089973337834463712008617461852495699203986228664535211595780541407230830979566918628821192872070928043897093367798522628753460508838184442524577686428444699379870916729559414308740644519430094088966695301643400943313965796045519120453596323344368285176882371687974702777363398112501771239229596930249771954438949430231032509040164864,   box := { reLo := (199994174866890829955899324390725500375613459854594918008457007665682599611822871143995625052355435353194045805112461858058135986039656602158665979010709049313321974550466414490272698337128040097799336620000686257779344641050487716835959662715852325761018195112786320379325562516447398971950647508491438251691393128517949954780053619437468790083394037158745499938447336246539989723555868060696147159602216501 : Rat)/1506854483746901093005318929519518987403538525357765792451216024549288943981840132285603116718313198470299737364071806467396039994664458131568506794804630934268361888115574066619647291544773893731002050581755294283854992969675583084960372057760044002246112195062001493007626246640864266355525676751530254796217683152601421247175310502854090768843345991321705889186560810651203812882023878064387055180652216320,            reHi := (126893113463543861108976443297414044195801009940221145705406561917742807811111178481058175534682605358462739840306628178420742431433878525180981813919287186272330749568499560204757947168424508581309310366276986840396622458656510039794169248851101229232585716747740566876339909466396324116544424828609060353600924863404516352846458725200914720490907601563163143362994451889045692846017593624268544796171504855 : Rat)/33485655194375579844562642878211533053411967230172573165582578323317532088485336273013402593740293299339994163646040143719911999881432402923744595440102909650408041958123868147103273145439419860688934457372339872974555399326124068554674934616889866716580271001377810955725027703130317030122792816700672328804837403391142694381673566730090905974296577584926797537479129125582306952933863956986379004014493696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (90563413106715595058350669573772152969990135915438270918668761666683591515818737195561805401361320471774106976011655300978199974431664362082067185519669991832687521425020871231865650129121706277081678669893732155325053138590076751660577633246675746539065756294531516565586920623027000667410854033580771770965532597728674045889573589166718207907841613067564215195355022813288036290689722803252756640625 : Rat)/99064270535799206390645045265765830235864993676910868058152202234834179946675668927424017234923704991398407972457329070423191561082814461661959133837257642385744141856087794186735597045257506921017676368885049155372856889398759741833459118828617481289038860188177933390603286801886627931592091038240907192646688736570353764743375949405554726796225003542478459193860499543908877898860462065018080329728, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 884, a6 := 44280 }
def label : String := "380.b2"
def inputConductor : Nat := 380
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 380 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 884, a6 := 44280 },   conductor := 380,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, 0, -1, 0, 2, 0, 1, 0, 0, 0, 6, 0, -2, 0, 2, 0, -1, 0, 4, 0, -2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16744865180716899013519287109375,   alphaHi := (2698607540904403791726115815424 : Rat)/8372432590358449459075927734375,   geometricUpper := (6525408583447057 : Rat)/9007199254740992,   tail := (90563413106715595058350669573772152969990135915438270918668761666683591515818737195561805401361320471774106976011655300978199974431664362082067185519669991832687521425020871231865650129121706277081678669893732155325053138590076751660577633246675746539065756294531516565586920623027000667410854033580771770965532597728674045889573589166718207907841613067564215195355022813288036290689722803252756640625 : Rat)/49532135267899603195322522632882915117932496838455434029076101117417089973337834463712008617461852495699203986228664535211595780541407230830979566918628821192872070928043897093367798522628753460508838184442524577686428444699379870916729559414308740644519430094088966695301643400943313965796045519120453596323344368285176882371687974702777363398112501771239229596930249771954438949430231032509040164864,   box := { reLo := (199994174866890829955899324390725500375613459854594918008457007665682599611822871143995625052355435353194045805112461858058135986039656602158665979010709049313321974550466414490272698337128040097799336620000686257779344641050487716835959662715852325761018195112786320379325562516447398971950647508491438251691393128517949954780053619437468790083394037158745499938447336246539989723555868060696147159602216501 : Rat)/1506854483746901093005318929519518987403538525357765792451216024549288943981840132285603116718313198470299737364071806467396039994664458131568506794804630934268361888115574066619647291544773893731002050581755294283854992969675583084960372057760044002246112195062001493007626246640864266355525676751530254796217683152601421247175310502854090768843345991321705889186560810651203812882023878064387055180652216320,            reHi := (126893113463543861108976443297414044195801009940221145705406561917742807811111178481058175534682605358462739840306628178420742431433878525180981813919287186272330749568499560204757947168424508581309310366276986840396622458656510039794169248851101229232585716747740566876339909466396324116544424828609060353600924863404516352846458725200914720490907601563163143362994451889045692846017593624268544796171504855 : Rat)/33485655194375579844562642878211533053411967230172573165582578323317532088485336273013402593740293299339994163646040143719911999881432402923744595440102909650408041958123868147103273145439419860688934457372339872974555399326124068554674934616889866716580271001377810955725027703130317030122792816700672328804837403391142694381673566730090905974296577584926797537479129125582306952933863956986379004014493696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (90563413106715595058350669573772152969990135915438270918668761666683591515818737195561805401361320471774106976011655300978199974431664362082067185519669991832687521425020871231865650129121706277081678669893732155325053138590076751660577633246675746539065756294531516565586920623027000667410854033580771770965532597728674045889573589166718207907841613067564215195355022813288036290689722803252756640625 : Rat)/99064270535799206390645045265765830235864993676910868058152202234834179946675668927424017234923704991398407972457329070423191561082814461661959133837257642385744141856087794186735597045257506921017676368885049155372856889398759741833459118828617481289038860188177933390603286801886627931592091038240907192646688736570353764743375949405554726796225003542478459193860499543908877898860462065018080329728, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N380.C380_b2
