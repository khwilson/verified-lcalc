module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -238, a6 := 1470 }
def label : String := "322.a1"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 7, 7, 7, 7, 7, 7, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -238, a6 := 1470 },   conductor := 322,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 1, -1, -3, 2, -4, 0, 4, -1, 0, 1, -8, 3, -2, -2, 0, 4, 1, 0, -1, -4, 0, 1, 2, 0,                    -6, -1, 0, 8, -2, -3, -10, 2, 0, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   finite := ((4784802367776619 : Rat)/4503599627370496, (23508373932274591 : Rat)/9007199254740992),   tail := (512186907141653502203457779539203643798828125 : Rat)/1474345655004446667239531943167555875542925312,   box := { reLo := (552712918356904889007772083150892382661787620683909 : Rat)/772981734770971334273679723419431534876649225977856,            reHi := (4571960132052567382580786655591358719361976730528401 : Rat)/1545963469541942668547359446838863069753298451955712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8, a6 := 44 }
def label : String := "322.a2"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 7, 7, 7, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8, a6 := 44 },   conductor := 322,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -2, 0, 1, -1, -3, 2, -4, 0, 4, -1, 0, 1, -8, 3, -2, -2, 0, 4, 1, 0, -1, -4, 0, 1, 2, 0,                    -6, -1, 0, 8, -2, -3, -10, 2, 0, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   finite := ((4784802367776619 : Rat)/4503599627370496, (23508373932274591 : Rat)/9007199254740992),   tail := (512186907141653502203457779539203643798828125 : Rat)/1474345655004446667239531943167555875542925312,   box := { reLo := (552712918356904889007772083150892382661787620683909 : Rat)/772981734770971334273679723419431534876649225977856,            reHi := (4571960132052567382580786655591358719361976730528401 : Rat)/1545963469541942668547359446838863069753298451955712,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -605, a6 := 5117 }
def label : String := "322.b1"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 7, 7, 23, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -605, a6 := 5117 },   conductor := 322,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 2, 1, 0, -2, 1, -1, 1, 0, 4, 2, 0, -1, 0, 1, 6, -1, -6, 0, 2, -4, -1, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   geometricUpper := (3173162632725609 : Rat)/4503599627370496,   tail := (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/1622854529585239921099199802803776023015147027196667561145729676660143167167409620444910282410690312574032289839381326171652557647712299327609517087140502254128303665649222163789265590577380383160466617181870341137358986795763197727466627100914023955192643262216570337974222934506837505218220457958854424274224916906786938416383116983845210114204369055070416261311067934596802742601165882523648,   box := { reLo := (236482617852632057452796561147128601262829053116150929256744609469281334555939519833140739071580136990581250853797540213737253859143863907578678106891367420071760162983830196837925930594162237692681227050723054320283017573892981511670188975895394688807075318525898768848333843463369511768157104335682605815555227824629909823002913780812970512814038792006385606933505352825319836810701031246713313 : Rat)/374879396334190421773915154447672261316498963282430206624663555308493071615671622322774275236869462204601458952897086345651740816621541144677798447129456020703638146764970319835320351423374868510067788569012048802729925949821298675044790860311139533649500593572027748072045497871079463705408925788495372007345955805467782774184500023268243536381209251721266156362856692891861433540869318862962688,            reHi := (694869270896692485081471987403784580250627194946082773626721126137666013184682562297600168674758939481485392411912819378816347296180965044642999321393654966055687965707106246783181508870021580257586899716113645967017974516446726395294444598963405932998386918591903053070217776134882392054606256494148943300217995231437620363890054420642158842584026593764574300732324995841330663897463585456452755 : Rat)/303473797032439865245550363124306116303832494085776833934251449535446772260305599023198222810799088451344038199964307994099028280122199974262979695295273921521992785476404544628592665437970131651007257413009753792686130530807717975036259267870922479621024290034498653201179688752778613475807225638305777339280059461569157483863642875979054291356217013298167840865169703769602112866418020031922176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/3245709059170479842198399605607552046030294054393335122291459353320286334334819240889820564821380625148064579678762652343305115295424598655219034174281004508256607331298444327578531181154760766320933234363740682274717973591526395454933254201828047910385286524433140675948445869013675010436440915917708848548449833813573876832766233967690420228408738110140832522622135869193605485202331765047296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 35, a6 := 381 }
def label : String := "322.b2"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 35, a6 := 381 },   conductor := 322,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 2, 1, 0, -2, 1, -1, 1, 0, 4, 2, 0, -1, 0, 1, 6, -1, -6, 0, 2, -4, -1, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   geometricUpper := (3173162632725609 : Rat)/4503599627370496,   tail := (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/1622854529585239921099199802803776023015147027196667561145729676660143167167409620444910282410690312574032289839381326171652557647712299327609517087140502254128303665649222163789265590577380383160466617181870341137358986795763197727466627100914023955192643262216570337974222934506837505218220457958854424274224916906786938416383116983845210114204369055070416261311067934596802742601165882523648,   box := { reLo := (236482617852632057452796561147128601262829053116150929256744609469281334555939519833140739071580136990581250853797540213737253859143863907578678106891367420071760162983830196837925930594162237692681227050723054320283017573892981511670188975895394688807075318525898768848333843463369511768157104335682605815555227824629909823002913780812970512814038792006385606933505352825319836810701031246713313 : Rat)/374879396334190421773915154447672261316498963282430206624663555308493071615671622322774275236869462204601458952897086345651740816621541144677798447129456020703638146764970319835320351423374868510067788569012048802729925949821298675044790860311139533649500593572027748072045497871079463705408925788495372007345955805467782774184500023268243536381209251721266156362856692891861433540869318862962688,            reHi := (694869270896692485081471987403784580250627194946082773626721126137666013184682562297600168674758939481485392411912819378816347296180965044642999321393654966055687965707106246783181508870021580257586899716113645967017974516446726395294444598963405932998386918591903053070217776134882392054606256494148943300217995231437620363890054420642158842584026593764574300732324995841330663897463585456452755 : Rat)/303473797032439865245550363124306116303832494085776833934251449535446772260305599023198222810799088451344038199964307994099028280122199974262979695295273921521992785476404544628592665437970131651007257413009753792686130530807717975036259267870922479621024290034498653201179688752778613475807225638305777339280059461569157483863642875979054291356217013298167840865169703769602112866418020031922176,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/3245709059170479842198399605607552046030294054393335122291459353320286334334819240889820564821380625148064579678762652343305115295424598655219034174281004508256607331298444327578531181154760766320933234363740682274717973591526395454933254201828047910385286524433140675948445869013675010436440915917708848548449833813573876832766233967690420228408738110140832522622135869193605485202331765047296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -174, a6 := 868 }
def label : String := "322.c1"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 7, 7, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -174, a6 := 868 },   conductor := 322,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -2, -2, -1, 1, 1, -2, -2, -2, -4, -1, 4, 1, -6, 1, 0, -2, 2, -2, 1, -2, -1, -4, 4, -1,                    -2, 4, 4, 1, 4, -6, 2, 1, 0, 0, 8, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   finite := ((13322579900988771 : Rat)/9007199254740992, (8095231093190143 : Rat)/2251799813685248),   tail := (512186907141653502203457779539203643798828125 : Rat)/1474345655004446667239531943167555875542925312,   box := { reLo := (1749573073137780966838076490335441819329001677626381 : Rat)/1545963469541942668547359446838863069753298451955712,            reHi := (1523703240157964522286171450133356566374240887668273 : Rat)/386490867385485667136839861709715767438324612988928,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14, a6 := 4 }
def label : String := "322.c2"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -14, a6 := 4 },   conductor := 322,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -2, 1, -2, -2, -1, 1, 1, -2, -2, -2, -4, -1, 4, 1, -6, 1, 0, -2, 2, -2, 1, -2, -1, -4, 4, -1,                    -2, 4, 4, 1, 4, -6, 2, 1, 0, 0, 8, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   finite := ((13322579900988771 : Rat)/9007199254740992, (8095231093190143 : Rat)/2251799813685248),   tail := (512186907141653502203457779539203643798828125 : Rat)/1474345655004446667239531943167555875542925312,   box := { reLo := (1749573073137780966838076490335441819329001677626381 : Rat)/1545963469541942668547359446838863069753298451955712,            reHi := (1523703240157964522286171450133356566374240887668273 : Rat)/386490867385485667136839861709715767438324612988928,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -14, a6 := -23 }
def label : String := "322.d1"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 7, 7, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -14, a6 := -23 },   conductor := 322,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, 1, -2, 2, 1, 1, 1, -2, 6, 2, -4, 1, -4, 1, -2, 1, 4, -2, 2, 6, 1, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   geometricUpper := (3173162632725609 : Rat)/4503599627370496,   tail := (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/1622854529585239921099199802803776023015147027196667561145729676660143167167409620444910282410690312574032289839381326171652557647712299327609517087140502254128303665649222163789265590577380383160466617181870341137358986795763197727466627100914023955192643262216570337974222934506837505218220457958854424274224916906786938416383116983845210114204369055070416261311067934596802742601165882523648,   box := { reLo := (20918761662020112904866730002634824413525300256334358202956751679755349617627361769022355891608309866554027246905427632897917669699927372970030448552118431839719716950530580342243559327772887424351828715215195600531417460886818709114491012975719681110473025551152608689694064084787081320814883454659795682042641573829130152987453644763537540157558825170539649663650746796736642279311374116632963601 : Rat)/12552779786341830789702310474687207538022162255366223585462219048966207398039913414141381034446689567760139761907614557937732533405054635299059614669031784935682428853796733436909969343116037263746209283901767088697471762865228334421954360625569975293415095633245171564230614398410388102862935242311738971761129732273996968650723409870042700233370794640969669781241110474106269214020018101320417280,            reHi := (2077680839960016127119508265572778637526527940237914191276069630102535683427194236191080099270784562919351352776329219758309945686231280420432096340456060538206205859426692154936811998427334441370830920908744366280894181945302670540421508890224798931479989400222349004545124819622711096826881014701311903795953571049550206777563984472943604989135758365274608297666136829112886863062134146833053577 : Rat)/624798993890317369623191924079453768860831605470717011041105925514155119359452703871290458728115770341002431588161810576086234694369235241129664078549093367839396911274950533058867252372291447516779647615020081337883209916368831125074651433851899222749167655953379580120075829785132439509014876314158953345576593009112971290307500038780405893968682086202110260604761154819769055901448864771604480,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/3245709059170479842198399605607552046030294054393335122291459353320286334334819240889820564821380625148064579678762652343305115295424598655219034174281004508256607331298444327578531181154760766320933234363740682274717973591526395454933254201828047910385286524433140675948445869013675010436440915917708848548449833813573876832766233967690420228408738110140832522622135869193605485202331765047296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -4, a6 := 1 }
def label : String := "322.d2"
def inputConductor : Nat := 322
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 7, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 322 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -4, a6 := 1 },   conductor := 322,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 2, 1, -2, 2, 1, 1, 1, -2, 6, 2, -4, 1, -4, 1, -2, 1, 4, -2, 2, 6, 1, 2],   alphaLo := (5397215081808807583435051761664 : Rat)/15414086533732027339935302734375,   alphaHi := (2698607540904403791726115815424 : Rat)/7707043266866013622283935546875,   geometricUpper := (3173162632725609 : Rat)/4503599627370496,   tail := (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/1622854529585239921099199802803776023015147027196667561145729676660143167167409620444910282410690312574032289839381326171652557647712299327609517087140502254128303665649222163789265590577380383160466617181870341137358986795763197727466627100914023955192643262216570337974222934506837505218220457958854424274224916906786938416383116983845210114204369055070416261311067934596802742601165882523648,   box := { reLo := (20918761662020112904866730002634824413525300256334358202956751679755349617627361769022355891608309866554027246905427632897917669699927372970030448552118431839719716950530580342243559327772887424351828715215195600531417460886818709114491012975719681110473025551152608689694064084787081320814883454659795682042641573829130152987453644763537540157558825170539649663650746796736642279311374116632963601 : Rat)/12552779786341830789702310474687207538022162255366223585462219048966207398039913414141381034446689567760139761907614557937732533405054635299059614669031784935682428853796733436909969343116037263746209283901767088697471762865228334421954360625569975293415095633245171564230614398410388102862935242311738971761129732273996968650723409870042700233370794640969669781241110474106269214020018101320417280,            reHi := (2077680839960016127119508265572778637526527940237914191276069630102535683427194236191080099270784562919351352776329219758309945686231280420432096340456060538206205859426692154936811998427334441370830920908744366280894181945302670540421508890224798931479989400222349004545124819622711096826881014701311903795953571049550206777563984472943604989135758365274608297666136829112886863062134146833053577 : Rat)/624798993890317369623191924079453768860831605470717011041105925514155119359452703871290458728115770341002431588161810576086234694369235241129664078549093367839396911274950533058867252372291447516779647615020081337883209916368831125074651433851899222749167655953379580120075829785132439509014876314158953345576593009112971290307500038780405893968682086202110260604761154819769055901448864771604480,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1346072088787342696507345300822724843739276438476678359377954116322017420665371995348941288951259773644688067006424847135956325014163596629163652074164597942432282199369308745161670322258656585784619948632537760533451279795487569316482185252823317684582310314015742571838265330613148800120194864149389590074077730188250732059942974903672054834447443844902409901800981684176092955230199316015625 : Rat)/3245709059170479842198399605607552046030294054393335122291459353320286334334819240889820564821380625148064579678762652343305115295424598655219034174281004508256607331298444327578531181154760766320933234363740682274717973591526395454933254201828047910385286524433140675948445869013675010436440915917708848548449833813573876832766233967690420228408738110140832522622135869193605485202331765047296, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N322.C322_d2
