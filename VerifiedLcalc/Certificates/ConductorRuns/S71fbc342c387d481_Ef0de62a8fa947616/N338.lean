module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -35944, a6 := -2868878 }
def label : String := "338.a1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -35944, a6 := -2868878 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -3, 1, 1, 3, -1, -1, 6, -1, 2, -3, 0, 1, -3, 1, -3, -6, -6, 1, 3, -2, -4, 3, -4, 0, -9, -1, 2,                    3, -4, -1, -6, 3, -1, 6, -3, 6, 0, -1, 0, -3, -5, 2, 6, 4, -13, -3, -6, 4, 9, 0, 12, 9, 2, 1, 18, -2,                    10, -3, -8, 4, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((2501091522867681 : Rat)/4503599627370496, (2512120840878543 : Rat)/1125899906842624),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (10251171634197105334149558833279091547757691733549 : Rat)/69964132847924524964666548883231917003090830557184,            reHi := (46177115008645198003650529849860588760016514590147 : Rat)/17491033211981131241166637220807979250772707639296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -454, a6 := 5812 }
def label : String := "338.a2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -454, a6 := 5812 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, -3, 1, 1, 3, -1, -1, 6, -1, 2, -3, 0, 1, -3, 1, -3, -6, -6, 1, 3, -2, -4, 3, -4, 0, -9, -1, 2,                    3, -4, -1, -6, 3, -1, 6, -3, 6, 0, -1, 0, -3, -5, 2, 6, 4, -13, -3, -6, 4, 9, 0, 12, 9, 2, 1, 18, -2,                    10, -3, -8, 4, -6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((2501091522867681 : Rat)/4503599627370496, (2512120840878543 : Rat)/1125899906842624),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (10251171634197105334149558833279091547757691733549 : Rat)/69964132847924524964666548883231917003090830557184,            reHi := (46177115008645198003650529849860588760016514590147 : Rat)/17491033211981131241166637220807979250772707639296,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -54421, a6 := 4945517 }
def label : String := "338.b1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -54421, a6 := 4945517 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, -1, 1, 3, 1, 3, -1, -2, -3, 0, -1, 0, -3, -3, 1, -3, 2, 6, 3, -3, 0, 6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (20547069754555727745542032306239231726115164707769917361967416360274420483012964918157691422293569482097411536263609050680417721412056818960681278415651984250119825268662824384609885162401752023468024784539463393768997186462200618914203558623050118637126340720551128440268964950821366426657904535181586361128031024581661449073307900127732685653331754254898379491096347279271586016236516969475866163 : Rat)/739047199192767972486491732055066721890347499113029176286069038398629026577701930967574713374076850040512687765583729005260402572418654340782064522330421793886247784447717635515512626852820061615333200867854318098997596941823986796507384965910903203903378038829931597089767404758480772407551620974075575096095886332207740043013621909478671189878308613741807767393831422285206601590550110660796088320,            reHi := (1574510499329071306611986809131074922079070186263220260084055125910664499775502385759901952291215051743855960329203614512794109797234068869663246273856474710956866496833662351186071250005667058732807275403537500221898379814790162694264626433851312265001090237880791985244738039174372460118871885946734322094318574269933381944597366146230274533225162781034232733611296541876255823837085388748098240973 : Rat)/739047199192767972486491732055066721890347499113029176286069038398629026577701930967574713374076850040512687765583729005260402572418654340782064522330421793886247784447717635515512626852820061615333200867854318098997596941823986796507384965910903203903378038829931597089767404758480772407551620974075575096095886332207740043013621909478671189878308613741807767393831422285206601590550110660796088320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 504, a6 := -13112 }
def label : String := "338.b2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 13, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 504, a6 := -13112 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, -1, 1, 3, 1, 3, -1, -2, -3, 0, -1, 0, -3, -3, 1, -3, 2, 6, 3, -3, 0, 6, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (20547069754555727745542032306239231726115164707769917361967416360274420483012964918157691422293569482097411536263609050680417721412056818960681278415651984250119825268662824384609885162401752023468024784539463393768997186462200618914203558623050118637126340720551128440268964950821366426657904535181586361128031024581661449073307900127732685653331754254898379491096347279271586016236516969475866163 : Rat)/739047199192767972486491732055066721890347499113029176286069038398629026577701930967574713374076850040512687765583729005260402572418654340782064522330421793886247784447717635515512626852820061615333200867854318098997596941823986796507384965910903203903378038829931597089767404758480772407551620974075575096095886332207740043013621909478671189878308613741807767393831422285206601590550110660796088320,            reHi := (1574510499329071306611986809131074922079070186263220260084055125910664499775502385759901952291215051743855960329203614512794109797234068869663246273856474710956866496833662351186071250005667058732807275403537500221898379814790162694264626433851312265001090237880791985244738039174372460118871885946734322094318574269933381944597366146230274533225162781034232733611296541876255823837085388748098240973 : Rat)/739047199192767972486491732055066721890347499113029176286069038398629026577701930967574713374076850040512687765583729005260402572418654340782064522330421793886247784447717635515512626852820061615333200867854318098997596941823986796507384965910903203903378038829931597089767404758480772407551620974075575096095886332207740043013621909478671189878308613741807767393831422285206601590550110660796088320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -389, a6 := -2859 }
def label : String := "338.c1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -389, a6 := -2859 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 1, 0, -4, -1, -3, -1, -4, 0, 0, 4, 0, 1, 3, 3, 0, 1, 0, 4, -4, 0, -4, 0, 0, -4, -1, 0,                    -4, -1, 0, -3, -4, -3, -3, 0, 0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((9646088113654393 : Rat)/9007199254740992, (26200608713152919 : Rat)/9007199254740992),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (92646143336771838576431606904282089466391969869797 : Rat)/139928265695849049929333097766463834006181661114368,            reHi := (464237964146457145062101627785733190492884776943851 : Rat)/139928265695849049929333097766463834006181661114368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1, a6 := 1 }
def label : String := "338.c2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1, a6 := 1 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, 1, 0, -4, -1, -3, -1, -4, 0, 0, 4, 0, 1, 3, 3, 0, 1, 0, 4, -4, 0, -4, 0, 0, -4, -1, 0,                    -4, -1, 0, -3, -4, -3, -3, 0, 0, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((9646088113654393 : Rat)/9007199254740992, (26200608713152919 : Rat)/9007199254740992),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (92646143336771838576431606904282089466391969869797 : Rat)/139928265695849049929333097766463834006181661114368,            reHi := (464237964146457145062101627785733190492884776943851 : Rat)/139928265695849049929333097766463834006181661114368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -322, a6 := 2127 }
def label : String := "338.d1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -322, a6 := 2127 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -3, -1, -3, 1, -2, -3, 0, -1, 0, -3, 3, 1, -3, -2, -6, -3, 3, 0, 6, -1, 4, 0, 5, -3, 0,                    3, 0, 1, 0, -3, 9, -2, -3, -6, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((14329549076891327 : Rat)/9007199254740992, (36359654319038799 : Rat)/9007199254740992),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (165404450498124827187573138232962239892557027652083 : Rat)/139928265695849049929333097766463834006181661114368,            reHi := (622060345172214132016574746019635467733983834818371 : Rat)/139928265695849049929333097766463834006181661114368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 3, a6 := -5 }
def label : String := "338.d2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 3, a6 := -5 },   conductor := 338,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -3, -1, -3, 1, -2, -3, 0, -1, 0, -3, 3, 1, -3, -2, -6, -3, 3, 0, 6, -1, 4, 0, 5, -3, 0,                    3, 0, 1, 0, -3, 9, -2, -3, -6, 0, -3],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   finite := ((14329549076891327 : Rat)/9007199254740992, (36359654319038799 : Rat)/9007199254740992),   tail := (54557191732637963016100327950191497802734375 : Rat)/133445993133400964669545266882385095602208768,   box := { reLo := (165404450498124827187573138232962239892557027652083 : Rat)/139928265695849049929333097766463834006181661114368,            reHi := (622060345172214132016574746019635467733983834818371 : Rat)/139928265695849049929333097766463834006181661114368,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -65773, a6 := -6478507 }
def label : String := "338.e1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -65773, a6 := -6478507 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, -1, 0, 4, 1, -3, -1, 4, 0, 0, 4, 0, 1, 3, -3, 0, -1, 0, 4, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (147683774770219822437223645945678406420767896730869710630668603568906294775146918437496353576187771898826573978887088437896313825310342958380875479105380565171014534923410407362352847456067801889532947183759778164293984880797038998017805439640533690966032073520188281389861385989109585661031356305330361480917474944068733834252797498296461611714227767306393021809671685754656864788993839575713045433 : Rat)/142623143703867503462305421975539191943751271758654753318364200392717882322012653344619681528330620183256834481077561737857270671870266627168468592028677890048223256647805157731063840269842468031029214202568377176999536251930944820378618151316139214788371200475951711719077920216548920990931014573944409229071135958847107727599120017618690931380024469318594481426879748160303028377123705566118543360,            reHi := (63938779165970424012646345568107535495462167648883609351841863627563150054744581924894758068733635000972287407702164712132755965819195807335442559365474055274024011062385867766729367164875809851899232153403123979539717506599582340019141708636169379002336814176923230653432798282230221052042457267580165616710516155157773052517282582880686974978995103998695118244948966485769198493924647810273323457 : Rat)/20374734814838214780329345996505598849107324536950679045480600056102554617430379049231383075475802883322404925868223105408181524552895232452638370289811127149746179521115022533009120038548924004432744886081196739571362321704420688625516878759448459255481600067993101674153988602364131570133002081992058461295876565549586818228445716802670133054289209902656354489554249737186146911017672223731220480,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 137, a6 := 2643 }
def label : String := "338.e2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 137, a6 := 2643 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, -1, 0, 4, 1, -3, -1, 4, 0, 0, 4, 0, 1, 3, -3, 0, -1, 0, 4, -4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (147683774770219822437223645945678406420767896730869710630668603568906294775146918437496353576187771898826573978887088437896313825310342958380875479105380565171014534923410407362352847456067801889532947183759778164293984880797038998017805439640533690966032073520188281389861385989109585661031356305330361480917474944068733834252797498296461611714227767306393021809671685754656864788993839575713045433 : Rat)/142623143703867503462305421975539191943751271758654753318364200392717882322012653344619681528330620183256834481077561737857270671870266627168468592028677890048223256647805157731063840269842468031029214202568377176999536251930944820378618151316139214788371200475951711719077920216548920990931014573944409229071135958847107727599120017618690931380024469318594481426879748160303028377123705566118543360,            reHi := (63938779165970424012646345568107535495462167648883609351841863627563150054744581924894758068733635000972287407702164712132755965819195807335442559365474055274024011062385867766729367164875809851899232153403123979539717506599582340019141708636169379002336814176923230653432798282230221052042457267580165616710516155157773052517282582880686974978995103998695118244948966485769198493924647810273323457 : Rat)/20374734814838214780329345996505598849107324536950679045480600056102554617430379049231383075475802883322404925868223105408181524552895232452638370289811127149746179521115022533009120038548924004432744886081196739571362321704420688625516878759448459255481600067993101674153988602364131570133002081992058461295876565549586818228445716802670133054289209902656354489554249737186146911017672223731220480,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -77659, a6 := -8336303 }
def label : String := "338.f1"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -77659, a6 := -8336303 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, -6, 1, 0, 1, 3, 1, -3, -2, -2, 3, 1, -6, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (538147244560203789711099393659861601462202714227564500669747286330794640455774365914742764411242047843632465853816764297110221979667985750007061608363543944512092910013340654140535403577218343938754490005693786109977808080695570269133618379741701893396639977741975316310042468693277704609922015757601047399420209833141214619971712688711230008870511647837532081227427539865783859552858757097957661431 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            reHi := (1281347145661059052666873554681107540821751942783181006509750204010142470742849399429583849027285058699392821188917514920210764321027806586538125727778377819624311898606706006832369658875852537383469013737871927208559702410639075866050641837113954657246395129350044828270102086412518272725739618117263094081938648616618487140763778289413634071513521448089997554688059677012353426015092873946336552201 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -764, a6 := -16264 }
def label : String := "338.f2"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 13, 13, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -764, a6 := -16264 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, -6, 1, 0, 1, 3, 1, -3, -2, -2, 3, 1, -6, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (538147244560203789711099393659861601462202714227564500669747286330794640455774365914742764411242047843632465853816764297110221979667985750007061608363543944512092910013340654140535403577218343938754490005693786109977808080695570269133618379741701893396639977741975316310042468693277704609922015757601047399420209833141214619971712688711230008870511647837532081227427539865783859552858757097957661431 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            reHi := (1281347145661059052666873554681107540821751942783181006509750204010142470742849399429583849027285058699392821188917514920210764321027806586538125727778377819624311898606706006832369658875852537383469013737871927208559702410639075866050641837113954657246395129350044828270102086412518272725739618117263094081938648616618487140763778289413634071513521448089997554688059677012353426015092873946336552201 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 81, a6 := 467 }
def label : String := "338.f3"
def inputConductor : Nat := 338
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 13, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 338 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 81, a6 := 467 },   conductor := 338,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, 3, 1, 1, 1, -2, 3, -6, 1, 0, 1, 3, 1, -3, -2, -2, 3, 1, -6, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/15792402599875458431243896484375,   alphaHi := (2698607540904403791726115815424 : Rat)/7896201299937729167938232421875,   geometricUpper := (3199891068697655 : Rat)/4503599627370496,   tail := (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/315813916373528865850257242447579614804422607718370596690391382718787175345739425703036240804089016249281638779636101765607711765525772804039965438887252997748526381788964156134373712137470727806444158507032422530750404118490594259095045784072672390226793769944867111123831490387725824538990964612757629408600737278920976799634902221230258591866840423198579469728811125121074895931452719890432,   box := { reLo := (538147244560203789711099393659861601462202714227564500669747286330794640455774365914742764411242047843632465853816764297110221979667985750007061608363543944512092910013340654140535403577218343938754490005693786109977808080695570269133618379741701893396639977741975316310042468693277704609922015757601047399420209833141214619971712688711230008870511647837532081227427539865783859552858757097957661431 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            reHi := (1281347145661059052666873554681107540821751942783181006509750204010142470742849399429583849027285058699392821188917514920210764321027806586538125727778377819624311898606706006832369658875852537383469013737871927208559702410639075866050641837113954657246395129350044828270102086412518272725739618117263094081938648616618487140763778289413634071513521448089997554688059677012353426015092873946336552201 : Rat)/353457356135671639015278654461118866991035760445361779962902583581953012711074836549709645526732406541114763713974826915559322969417617293417509119375419118815161983866299738724810386755696551207333269980278152134303198537394080641807879766305214575779876453353445546434236584884490804194915992639775275045958902158881962629267384391489799264724408467441734149623136767179881418152002226837772042240,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (332024312608997874460503399169813844384330055297867239645051528413019302659352044292793699570098155324488785200218304060881658079040536567993576801971190767585925809194816969401766639727433439898665755216512077318997813039634790132538674297464231874799093248552312875429873775387121816505847668387262493812622897700997658281643942042510191199420926315471102620479472872125916182994842529296875 : Rat)/631627832747057731700514484895159229608845215436741193380782765437574350691478851406072481608178032498563277559272203531215423531051545608079930877774505995497052763577928312268747424274941455612888317014064845061500808236981188518190091568145344780453587539889734222247662980775451649077981929225515258817201474557841953599269804442460517183733680846397158939457622250242149791862905439780864, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N338.C338_f3
