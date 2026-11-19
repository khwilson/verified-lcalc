module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -304, a6 := -1892 }
def label : String := "312.a1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -304, a6 := -1892 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, -2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 8, 0, -4, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (21905515955378017252792947371543905984591112290739314278504031178645095052627925004980755851749183678647273170634256827688170372512820711408125204118455430569132989245871834181555265139579484057480195760251762193420256069710724637043196404089611294820675109873690400333826931493815842475021523428394835045987434426367774599598546245230477407749981929718100918718627946019461118401382096435531043701231 : Rat)/50247989031145521347095785303138488479025656056190126059836122336292548527956459010350070059784401527069659827114141765347119584623564897068690263362689092380948557608332191559592794712127421032097610177284138437475191280264485361064707861478414475613891058164658045825175017563244999288747029690596719115196103562093430945235266587676568794839817007448799846057877482563058501638731033064207883960320,            reHi := (810124664863959522719604055492940429983059658070218942691614521992926627121378598552178658799594612749122520748390714234404334320261741500867258754338342378543814701939581327111366855800980107656345219908604383236132967587082249703983851605697875421578208529172199072254257007078864043477365433337873777175286871378935153223185421107489399872617126242404753928196939372206581701964756237565254269547 : Rat)/436939035053439316061702480896856421556744835271218487476835846402543900243099643568261478780733926322344868061862102307366257257596216496249480550979905151138683109637671230952980823583716704626935740672035986412827750263169437922301807491116647614033835288388330833262391457071695645989104606005188861871270465757334182132480579023274511259476669629989563878764152022287465231641139417949633773568,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -44, a6 := 84 }
def label : String := "312.a2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -44, a6 := 84 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, -2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 8, 0, -4, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (21905515955378017252792947371543905984591112290739314278504031178645095052627925004980755851749183678647273170634256827688170372512820711408125204118455430569132989245871834181555265139579484057480195760251762193420256069710724637043196404089611294820675109873690400333826931493815842475021523428394835045987434426367774599598546245230477407749981929718100918718627946019461118401382096435531043701231 : Rat)/50247989031145521347095785303138488479025656056190126059836122336292548527956459010350070059784401527069659827114141765347119584623564897068690263362689092380948557608332191559592794712127421032097610177284138437475191280264485361064707861478414475613891058164658045825175017563244999288747029690596719115196103562093430945235266587676568794839817007448799846057877482563058501638731033064207883960320,            reHi := (810124664863959522719604055492940429983059658070218942691614521992926627121378598552178658799594612749122520748390714234404334320261741500867258754338342378543814701939581327111366855800980107656345219908604383236132967587082249703983851605697875421578208529172199072254257007078864043477365433337873777175286871378935153223185421107489399872617126242404753928196939372206581701964756237565254269547 : Rat)/436939035053439316061702480896856421556744835271218487476835846402543900243099643568261478780733926322344868061862102307366257257596216496249480550979905151138683109637671230952980823583716704626935740672035986412827750263169437922301807491116647614033835288388330833262391457071695645989104606005188861871270465757334182132480579023274511259476669629989563878764152022287465231641139417949633773568,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -39, a6 := 108 }
def label : String := "312.a3"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -39, a6 := 108 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, -2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 8, 0, -4, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (21905515955378017252792947371543905984591112290739314278504031178645095052627925004980755851749183678647273170634256827688170372512820711408125204118455430569132989245871834181555265139579484057480195760251762193420256069710724637043196404089611294820675109873690400333826931493815842475021523428394835045987434426367774599598546245230477407749981929718100918718627946019461118401382096435531043701231 : Rat)/50247989031145521347095785303138488479025656056190126059836122336292548527956459010350070059784401527069659827114141765347119584623564897068690263362689092380948557608332191559592794712127421032097610177284138437475191280264485361064707861478414475613891058164658045825175017563244999288747029690596719115196103562093430945235266587676568794839817007448799846057877482563058501638731033064207883960320,            reHi := (810124664863959522719604055492940429983059658070218942691614521992926627121378598552178658799594612749122520748390714234404334320261741500867258754338342378543814701939581327111366855800980107656345219908604383236132967587082249703983851605697875421578208529172199072254257007078864043477365433337873777175286871378935153223185421107489399872617126242404753928196939372206581701964756237565254269547 : Rat)/436939035053439316061702480896856421556744835271218487476835846402543900243099643568261478780733926322344868061862102307366257257596216496249480550979905151138683109637671230952980823583716704626935740672035986412827750263169437922301807491116647614033835288388330833262391457071695645989104606005188861871270465757334182132480579023274511259476669629989563878764152022287465231641139417949633773568,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 136, a6 := 444 }
def label : String := "312.a4"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 136, a6 := 444 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, -2, 0, 4, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, 8, 0, -4, 0, 8, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (21905515955378017252792947371543905984591112290739314278504031178645095052627925004980755851749183678647273170634256827688170372512820711408125204118455430569132989245871834181555265139579484057480195760251762193420256069710724637043196404089611294820675109873690400333826931493815842475021523428394835045987434426367774599598546245230477407749981929718100918718627946019461118401382096435531043701231 : Rat)/50247989031145521347095785303138488479025656056190126059836122336292548527956459010350070059784401527069659827114141765347119584623564897068690263362689092380948557608332191559592794712127421032097610177284138437475191280264485361064707861478414475613891058164658045825175017563244999288747029690596719115196103562093430945235266587676568794839817007448799846057877482563058501638731033064207883960320,            reHi := (810124664863959522719604055492940429983059658070218942691614521992926627121378598552178658799594612749122520748390714234404334320261741500867258754338342378543814701939581327111366855800980107656345219908604383236132967587082249703983851605697875421578208529172199072254257007078864043477365433337873777175286871378935153223185421107489399872617126242404753928196939372206581701964756237565254269547 : Rat)/436939035053439316061702480896856421556744835271218487476835846402543900243099643568261478780733926322344868061862102307366257257596216496249480550979905151138683109637671230952980823583716704626935740672035986412827750263169437922301807491116647614033835288388330833262391457071695645989104606005188861871270465757334182132480579023274511259476669629989563878764152022287465231641139417949633773568,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_a4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3, a6 := 0 }
def label : String := "312.b1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3, a6 := 0 },   conductor := 312,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -4, 0, 1, 0, -2, 0, -1, 0, 0, 0, -6, 0, -4, 0, 4, 0, 4, 0, -5, 0, -1, 0, 10, 0,                    -8, 0, 2, 0, 0, 0, -2, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   finite := ((2840497611445709 : Rat)/2251799813685248, (6596812640894079 : Rat)/2251799813685248),   tail := (6149395737827295574867196579830169677734375 : Rat)/19708887955998010709320000700110508237258752,   box := { reLo := (4905257488897429889792045040759272163496220107279 : Rat)/5166566724337142519383982263529769071347958284288,            reHi := (16747863192903938008151558604633712607475784285749 : Rat)/5166566724337142519383982263529769071347958284288,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 12, a6 := -12 }
def label : String := "312.b2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 12, a6 := -12 },   conductor := 312,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -4, 0, 1, 0, -2, 0, -1, 0, 0, 0, -6, 0, -4, 0, 4, 0, 4, 0, -5, 0, -1, 0, 10, 0,                    -8, 0, 2, 0, 0, 0, -2, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   finite := ((2840497611445709 : Rat)/2251799813685248, (6596812640894079 : Rat)/2251799813685248),   tail := (6149395737827295574867196579830169677734375 : Rat)/19708887955998010709320000700110508237258752,   box := { reLo := (4905257488897429889792045040759272163496220107279 : Rat)/5166566724337142519383982263529769071347958284288,            reHi := (16747863192903938008151558604633712607475784285749 : Rat)/5166566724337142519383982263529769071347958284288,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -651, a6 := 6228 }
def label : String := "312.c1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -651, a6 := 6228 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 4, 0, 0, 0, 1, 0, -2, 0, -1, 0, -4, 0, 2, 0, 8, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (1051595769928038086663687752326163016239074425433235846071547420176911058021422790355939795411141478090915980075578143965745151558641862133645801782759321145928453245963119354468132459496127737200242802136678984755539839525581899620708180961391911103030899274725461867612537332015792278018473495269994109958913327417328341404385085579298993914690035214921942211724034127443246694027077168208176049605 : Rat)/1435656829461300609917022437232528242257875887319717887423889209608358529370184543152859144565268615059133137917546907581346273846387568487676864667505402639455673074523776901702651277489354886631360290779546812499291179436128153173277367470811842160396887376133087023576429073235571408249915134017049117577031530345526598435293331076473394138280485927108567030225070930373100046820886658977368113152,            reHi := (7383300602273572936289869188863037996827244473317189673995352847567697693075432882455882291758633812969367055403833636548392622999767162854158735221831988563772463286963089055671319192110686128744663780109069542220804464284434924424035200246687219526658776870607360212215354457871313593002854044803471839051428462934301255384088356871994156492924563667632486788763906666008507004849810561756692267483 : Rat)/3433092418277023197627662349903871883660137991416716687317995936019987787624354342322054476134337992532709677628916518129306307023970272470531632900556397616089653004295988243201992185300631250640209390994568464672218037782045583675228487430202231253122991551622599404204504305563322932771536190040769628988553659521911431040918835182871159895888118521346573333146908746544369677180381141032836792320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 564, a6 := 25668 }
def label : String := "312.c2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 13, 13, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 564, a6 := 25668 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 4, 0, 0, 0, 1, 0, -2, 0, -1, 0, -4, 0, 2, 0, 8, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (1051595769928038086663687752326163016239074425433235846071547420176911058021422790355939795411141478090915980075578143965745151558641862133645801782759321145928453245963119354468132459496127737200242802136678984755539839525581899620708180961391911103030899274725461867612537332015792278018473495269994109958913327417328341404385085579298993914690035214921942211724034127443246694027077168208176049605 : Rat)/1435656829461300609917022437232528242257875887319717887423889209608358529370184543152859144565268615059133137917546907581346273846387568487676864667505402639455673074523776901702651277489354886631360290779546812499291179436128153173277367470811842160396887376133087023576429073235571408249915134017049117577031530345526598435293331076473394138280485927108567030225070930373100046820886658977368113152,            reHi := (7383300602273572936289869188863037996827244473317189673995352847567697693075432882455882291758633812969367055403833636548392622999767162854158735221831988563772463286963089055671319192110686128744663780109069542220804464284434924424035200246687219526658776870607360212215354457871313593002854044803471839051428462934301255384088356871994156492924563667632486788763906666008507004849810561756692267483 : Rat)/3433092418277023197627662349903871883660137991416716687317995936019987787624354342322054476134337992532709677628916518129306307023970272470531632900556397616089653004295988243201992185300631250640209390994568464672218037782045583675228487430202231253122991551622599404204504305563322932771536190040769628988553659521911431040918835182871159895888118521346573333146908746544369677180381141032836792320,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -60, a6 := 144 }
def label : String := "312.d1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -60, a6 := 144 },   conductor := 312,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -4, 0, -4, 0, 1, 0, -2, 0, -1, 0, -4, 0, -6, 0, 4, 0, -4, 0, 4, 0, 11, 0, 1, 0, -6, 0, 8,                    0, -2, 0, 16, 0, -10, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   finite := ((1566690199812505 : Rat)/1125899906842624, (14867677180371041 : Rat)/4503599627370496),   tail := (6149395737827295574867196579830169677734375 : Rat)/19708887955998010709320000700110508237258752,   box := { reLo := (2788626300346410773264787514312322304357930771155 : Rat)/2583283362168571259691991131764884535673979142144,            reHi := (37336698741106549057772704913627665248361378436971 : Rat)/10333133448674285038767964527059538142695916568576,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 5, a6 := 14 }
def label : String := "312.d2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 5, a6 := 14 },   conductor := 312,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, 0, -4, 0, -4, 0, 1, 0, -2, 0, -1, 0, -4, 0, -6, 0, 4, 0, -4, 0, 4, 0, 11, 0, 1, 0, -6, 0, 8,                    0, -2, 0, 16, 0, -10, 0, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   finite := ((1566690199812505 : Rat)/1125899906842624, (14867677180371041 : Rat)/4503599627370496),   tail := (6149395737827295574867196579830169677734375 : Rat)/19708887955998010709320000700110508237258752,   box := { reLo := (2788626300346410773264787514312322304357930771155 : Rat)/2583283362168571259691991131764884535673979142144,            reHi := (37336698741106549057772704913627665248361378436971 : Rat)/10333133448674285038767964527059538142695916568576,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -68, a6 := -240 }
def label : String := "312.e1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -68, a6 := -240 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 6, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (790931184428921594325659234897967513099055942239458546930143549544788051154969519294466380134569833118608796822526060881743811664353793010918509416095573198844644063536646083240009665695527289541780773285499963842377819234640852718269743010312859541068215675271069248295181867410986723323330307920770608947253163063509300885275519182033444008658522330719754249130712333797902397785478383351491280781 : Rat)/831169743372331932057223516292516350780875513711415619034883226615365464372212103930602662643050250823708658794369262283937316437382276492865553228555759422842758095776923469406798108020152829102366484135527101973273840726179457100318475904154224408650829533550734592596879989767962394249950867062502120702491938621094346462538244307431965027425544484115486175393462117584426342896302802565844697088,            reHi := (7785172000291142688607329520248057277256463090360810683778219946664039489088836858009648395437027059162233258659430962983985364195810302181853703237751377433987193192405594175905043683015319292048106477591624928682420182820950268258234282577243470181707060572978774944943451380139310485727979309335280127036285944276580335318934887149398121757114692493157369455150694006416552482638238066001738287 : Rat)/3285255902657438466629341961630499410201088987001642762983728168440179701075937169686176532185969370844698256104226333138092159831550499971800605646465452264200624884493768653781810703636967703961922862195759296337050753858416826483472236775313139955141618709686697994454071105802222902173718842144277156926845607198001369417147210701312114732907290451049352471910917460808009260459694871801757696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -6 }
def label : String := "312.e2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -6 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 6, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (790931184428921594325659234897967513099055942239458546930143549544788051154969519294466380134569833118608796822526060881743811664353793010918509416095573198844644063536646083240009665695527289541780773285499963842377819234640852718269743010312859541068215675271069248295181867410986723323330307920770608947253163063509300885275519182033444008658522330719754249130712333797902397785478383351491280781 : Rat)/831169743372331932057223516292516350780875513711415619034883226615365464372212103930602662643050250823708658794369262283937316437382276492865553228555759422842758095776923469406798108020152829102366484135527101973273840726179457100318475904154224408650829533550734592596879989767962394249950867062502120702491938621094346462538244307431965027425544484115486175393462117584426342896302802565844697088,            reHi := (7785172000291142688607329520248057277256463090360810683778219946664039489088836858009648395437027059162233258659430962983985364195810302181853703237751377433987193192405594175905043683015319292048106477591624928682420182820950268258234282577243470181707060572978774944943451380139310485727979309335280127036285944276580335318934887149398121757114692493157369455150694006416552482638238066001738287 : Rat)/3285255902657438466629341961630499410201088987001642762983728168440179701075937169686176532185969370844698256104226333138092159831550499971800605646465452264200624884493768653781810703636967703961922862195759296337050753858416826483472236775313139955141618709686697994454071105802222902173718842144277156926845607198001369417147210701312114732907290451049352471910917460808009260459694871801757696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -832, a6 := -9520 }
def label : String := "312.f1"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -832, a6 := -9520 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, -4, 0, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (66702356029407870466346972295136442537748872403845986159009374978118489389433097430853667645976047419185049704840741834563653996711030160702526575110771157389174457866518332805664036546199488678383373132733861636193875650426056579354003394904129231753210411144252090060448386087228874367649083154218926929703859870009288046344627966449921876975156436071119536731161735268317245378936164992526904963 : Rat)/62419862150491330865957497270979488793820690753031212496690835200363414320442806224037354111533418046049266865980300329623751036799459499464211507282843593019811872805381604421854403369102386375276534381719426630403964323309919703185972498730949659147690755484047261894627351010242235141300658000741265981610066536762026018925797003324930179925238518569937696966307431755352175948734202564233396224,            reHi := (776113149736960551893617005633644218083749323467577477904858417345895536085468504316389639699978773305849579401709851084468313724898547383854051555596604646696930057634714472583922589715538088070891841922670829851226052102048097463965461529580611027553815881855766665073156611085502571388061206206260987280487572365792795234785653489202831639299566322150088959417291585868822692043588648621083154289 : Rat)/312099310752456654329787486354897443969103453765156062483454176001817071602214031120186770557667090230246334329901501648118755183997297497321057536414217965099059364026908022109272016845511931876382671908597133152019821616549598515929862493654748295738453777420236309473136755051211175706503290003706329908050332683810130094628985016624650899626192592849688484831537158776760879743671012821166981120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -52, a6 := -160 }
def label : String := "312.f2"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -52, a6 := -160 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, -4, 0, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (66702356029407870466346972295136442537748872403845986159009374978118489389433097430853667645976047419185049704840741834563653996711030160702526575110771157389174457866518332805664036546199488678383373132733861636193875650426056579354003394904129231753210411144252090060448386087228874367649083154218926929703859870009288046344627966449921876975156436071119536731161735268317245378936164992526904963 : Rat)/62419862150491330865957497270979488793820690753031212496690835200363414320442806224037354111533418046049266865980300329623751036799459499464211507282843593019811872805381604421854403369102386375276534381719426630403964323309919703185972498730949659147690755484047261894627351010242235141300658000741265981610066536762026018925797003324930179925238518569937696966307431755352175948734202564233396224,            reHi := (776113149736960551893617005633644218083749323467577477904858417345895536085468504316389639699978773305849579401709851084468313724898547383854051555596604646696930057634714472583922589715538088070891841922670829851226052102048097463965461529580611027553815881855766665073156611085502571388061206206260987280487572365792795234785653489202831639299566322150088959417291585868822692043588648621083154289 : Rat)/312099310752456654329787486354897443969103453765156062483454176001817071602214031120186770557667090230246334329901501648118755183997297497321057536414217965099059364026908022109272016845511931876382671908597133152019821616549598515929862493654748295738453777420236309473136755051211175706503290003706329908050332683810130094628985016624650899626192592849688484831537158776760879743671012821166981120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := 2 }
def label : String := "312.f3"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := 2 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, -4, 0, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (66702356029407870466346972295136442537748872403845986159009374978118489389433097430853667645976047419185049704840741834563653996711030160702526575110771157389174457866518332805664036546199488678383373132733861636193875650426056579354003394904129231753210411144252090060448386087228874367649083154218926929703859870009288046344627966449921876975156436071119536731161735268317245378936164992526904963 : Rat)/62419862150491330865957497270979488793820690753031212496690835200363414320442806224037354111533418046049266865980300329623751036799459499464211507282843593019811872805381604421854403369102386375276534381719426630403964323309919703185972498730949659147690755484047261894627351010242235141300658000741265981610066536762026018925797003324930179925238518569937696966307431755352175948734202564233396224,            reHi := (776113149736960551893617005633644218083749323467577477904858417345895536085468504316389639699978773305849579401709851084468313724898547383854051555596604646696930057634714472583922589715538088070891841922670829851226052102048097463965461529580611027553815881855766665073156611085502571388061206206260987280487572365792795234785653489202831639299566322150088959417291585868822692043588648621083154289 : Rat)/312099310752456654329787486354897443969103453765156062483454176001817071602214031120186770557667090230246334329901501648118755183997297497321057536414217965099059364026908022109272016845511931876382671908597133152019821616549598515929862493654748295738453777420236309473136755051211175706503290003706329908050332683810130094628985016624650899626192592849688484831537158776760879743671012821166981120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := -448 }
def label : String := "312.f4"
def inputConductor : Nat := 312
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13, 13, 13] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 312 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := -448 },   conductor := 312,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 2, 0, -4, 0, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/15172849634788292026519775390625,   alphaHi := (337325942613050473965764476928 : Rat)/948303102174268245697021484375,   geometricUpper := (3155546420695587 : Rat)/4503599627370496,   tail := (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/1651712369360200335158040201925841835194112110106406617890260517063941528947178064196167185613860920485016720012180157434938240237079185506184316564336577307290409695572533259819914883678716794349885803014459173623454375997192974602047378972002584190619215037549873300379120716843752087568486094592396760646981200200101241537027255254556116004478275742106260669638470317148320392387981333233664,   box := { reLo := (66702356029407870466346972295136442537748872403845986159009374978118489389433097430853667645976047419185049704840741834563653996711030160702526575110771157389174457866518332805664036546199488678383373132733861636193875650426056579354003394904129231753210411144252090060448386087228874367649083154218926929703859870009288046344627966449921876975156436071119536731161735268317245378936164992526904963 : Rat)/62419862150491330865957497270979488793820690753031212496690835200363414320442806224037354111533418046049266865980300329623751036799459499464211507282843593019811872805381604421854403369102386375276534381719426630403964323309919703185972498730949659147690755484047261894627351010242235141300658000741265981610066536762026018925797003324930179925238518569937696966307431755352175948734202564233396224,            reHi := (776113149736960551893617005633644218083749323467577477904858417345895536085468504316389639699978773305849579401709851084468313724898547383854051555596604646696930057634714472583922589715538088070891841922670829851226052102048097463965461529580611027553815881855766665073156611085502571388061206206260987280487572365792795234785653489202831639299566322150088959417291585868822692043588648621083154289 : Rat)/312099310752456654329787486354897443969103453765156062483454176001817071602214031120186770557667090230246334329901501648118755183997297497321057536414217965099059364026908022109272016845511931876382671908597133152019821616549598515929862493654748295738453777420236309473136755051211175706503290003706329908050332683810130094628985016624650899626192592849688484831537158776760879743671012821166981120,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1171181946997753341083342027829767162673123319159582537397416275390084546316348329299936938909535870085224241400960900400355508869334553177370922997983234634628140669786570044213761325820675967593532032813710835258923936232032299716403426581118424896580031517138011006389253468863982104001470393643346562280344908912101837412687967390517516264774970212561561165890972074947255470320722776171875 : Rat)/3303424738720400670316080403851683670388224220212813235780521034127883057894356128392334371227721840970033440024360314869876480474158371012368633128673154614580819391145066519639829767357433588699771606028918347246908751994385949204094757944005168381238430075099746600758241433687504175136972189184793521293962400400202483074054510509112232008956551484212521339276940634296640784775962666467328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N312.C312_f4
