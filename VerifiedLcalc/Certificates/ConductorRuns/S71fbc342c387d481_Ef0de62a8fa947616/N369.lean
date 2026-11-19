module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 13 }
def label : String := "369.a1"
def inputConductor : Nat := 369
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 369 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 13 },   conductor := 369,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, 2, 0, -4, 0, 0, 0, -5, 0, -4, 0, 0, 4, 5, 0, -2, -4, 0, 0, -4, 0, -1, 0, 0, 8, -1, 0,                    -5, 0, 0, 0, -8, 0, -7, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16500725515199414539337158203125,   alphaHi := (1349303770452201895863057907712 : Rat)/4125181378799853610992431640625,   finite := ((12083335468440407 : Rat)/9007199254740992, (8303022304638185 : Rat)/2251799813685248),   tail := (792942581204715743248465373862361907958984375 : Rat)/1454340179055860423972292296563443955759316992,   box := { reLo := (1214338518013727902024715870845776291791605127872057 : Rat)/1524986207593677899927170367161309809354281574203392,            reHi := (1613628922711613051660128740602659656153379441388935 : Rat)/381246551898419474981792591790327452338570393550848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -93, a6 := -369 }
def label : String := "369.b1"
def inputConductor : Nat := 369
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 0, 1, 1],                kodaira := -9 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 369 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -93, a6 := -369 },   conductor := 369,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 4, 0, -2, 0, 0, 8, 3, 0, -6, -4, 0, -4, -3, 0, 0, 8, 0, 6, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16500725515199414539337158203125,   alphaHi := (1349303770452201895863057907712 : Rat)/4125181378799853610992431640625,   geometricUpper := (202948852451309 : Rat)/281474976710656,   tail := (1889839989832255796195553057359174247518838428464970058598617324408014646748657125320273467618268339667295315626723066553720853988273118738384868325142562903344503655803019883488441402089921788462866171235752044907115803683627545406992725641297081221592615783373494189432999705399891679163499134106468397217436423817721622915612845801312502480627615766504980078125 : Rat)/1184554290860794224774757520910789886169591674277079810806467481883956400240604574934418707692550933477814437571308387482921302034527775491705580463742839030919208049001403980521326450928589316630452167660894970216580661352653497830730505865695011542135199180326348332756661670199854179468492908426027442792373178124092834014419043667733103805912741273782104096768,   box := { reLo := (3396136032995814885655377775230682482375402074637272504103983704442326490352843447709254150074622819086625125556662406656175304872858975375407843826908868684107188377009845532596057967716226852759806930281508172217556573618142141755020934112666972075634697082130431465789362410089579037054582952440014716242946512824675641564666742187425874995406367000847039635100817921 : Rat)/2318119442271485562144085604333974821689013274934902721156770571010217897232852325940785362112476012024076352677359805426640256622979302887370694216423867555752498787533542526701112404776957506126546521764826716440188608137382025847337217106401181312439188711935549001529812838805955635781764539608856534309748652795834091988687419600788636158499968599434257522690621440,            reHi := (1541828523942883419752972457186729821214224671127070257810906631955055720346586299035136197963606528335187477786961882979692725459504748509061928728152485858248775233376254693994021695975806692906981384865770767393790242511101338997220271882038503113655166521053612418082326897219531167998837961980498386231620459532637559983196894056120817489814202459918977320937733193 : Rat)/331159920324497937449155086333424974527001896419271817308110081572888271033264617991540766016068001717725193239622829346662893803282757555338670602346266793678928398219077503814444629253851072303792360252118102348598372591054575121048173872343025901777026958847935571647116119829422233683109219944122362044249807542262013141241059942969805165499995514204893931812945920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1889839989832255796195553057359174247518838428464970058598617324408014646748657125320273467618268339667295315626723066553720853988273118738384868325142562903344503655803019883488441402089921788462866171235752044907115803683627545406992725641297081221592615783373494189432999705399891679163499134106468397217436423817721622915612845801312502480627615766504980078125 : Rat)/2369108581721588449549515041821579772339183348554159621612934963767912800481209149868837415385101866955628875142616774965842604069055550983411160927485678061838416098002807961042652901857178633260904335321789940433161322705306995661461011731390023084270398360652696665513323340399708358936985816852054885584746356248185668028838087335466207611825482547564208193536, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 177, a6 := 24201 }
def label : String := "369.b2"
def inputConductor : Nat := 369
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 41, 41, 41, 41, 41] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 369 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 177, a6 := 24201 },   conductor := 369,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 4, 0, -2, 0, 0, 8, 3, 0, -6, -4, 0, -4, -3, 0, 0, 8, 0, 6, 6, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16500725515199414539337158203125,   alphaHi := (1349303770452201895863057907712 : Rat)/4125181378799853610992431640625,   geometricUpper := (202948852451309 : Rat)/281474976710656,   tail := (1889839989832255796195553057359174247518838428464970058598617324408014646748657125320273467618268339667295315626723066553720853988273118738384868325142562903344503655803019883488441402089921788462866171235752044907115803683627545406992725641297081221592615783373494189432999705399891679163499134106468397217436423817721622915612845801312502480627615766504980078125 : Rat)/1184554290860794224774757520910789886169591674277079810806467481883956400240604574934418707692550933477814437571308387482921302034527775491705580463742839030919208049001403980521326450928589316630452167660894970216580661352653497830730505865695011542135199180326348332756661670199854179468492908426027442792373178124092834014419043667733103805912741273782104096768,   box := { reLo := (3396136032995814885655377775230682482375402074637272504103983704442326490352843447709254150074622819086625125556662406656175304872858975375407843826908868684107188377009845532596057967716226852759806930281508172217556573618142141755020934112666972075634697082130431465789362410089579037054582952440014716242946512824675641564666742187425874995406367000847039635100817921 : Rat)/2318119442271485562144085604333974821689013274934902721156770571010217897232852325940785362112476012024076352677359805426640256622979302887370694216423867555752498787533542526701112404776957506126546521764826716440188608137382025847337217106401181312439188711935549001529812838805955635781764539608856534309748652795834091988687419600788636158499968599434257522690621440,            reHi := (1541828523942883419752972457186729821214224671127070257810906631955055720346586299035136197963606528335187477786961882979692725459504748509061928728152485858248775233376254693994021695975806692906981384865770767393790242511101338997220271882038503113655166521053612418082326897219531167998837961980498386231620459532637559983196894056120817489814202459918977320937733193 : Rat)/331159920324497937449155086333424974527001896419271817308110081572888271033264617991540766016068001717725193239622829346662893803282757555338670602346266793678928398219077503814444629253851072303792360252118102348598372591054575121048173872343025901777026958847935571647116119829422233683109219944122362044249807542262013141241059942969805165499995514204893931812945920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1889839989832255796195553057359174247518838428464970058598617324408014646748657125320273467618268339667295315626723066553720853988273118738384868325142562903344503655803019883488441402089921788462866171235752044907115803683627545406992725641297081221592615783373494189432999705399891679163499134106468397217436423817721622915612845801312502480627615766504980078125 : Rat)/2369108581721588449549515041821579772339183348554159621612934963767912800481209149868837415385101866955628875142616774965842604069055550983411160927485678061838416098002807961042652901857178633260904335321789940433161322705306995661461011731390023084270398360652696665513323340399708358936985816852054885584746356248185668028838087335466207611825482547564208193536, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N369.C369_b2
