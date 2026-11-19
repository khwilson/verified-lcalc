module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 }
def label : String := "112.a2"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 },   conductor := 112,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -4, 0, -1, 0, 1, 0, 0, 0, 0, 0, 8, 0, -2, 0, 2, 0, 2, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   finite := ((3008030843631027 : Rat)/9007199254740992, (5334132766546087 : Rat)/4503599627370496),   tail := (11811205609887788124074432197551727294921875 : Rat)/47133179186103571059895619727688494751940608,   box := { reLo := (8240382741953613776881793888472799714613955175971 : Rat)/98845440996495476255402218703161382146021749948416,            reHi := (70921978138287095637870473566621599434376616555351 : Rat)/49422720498247738127701109351580691073010874974208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 }
def label : String := "112.a1"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0],              kodaira := -7 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 },   conductor := 112,   policy := { precisionBits := 53 },   termLimit := 24,   stepsPerUnit := 1,   cutoff := 8,   coefficients := [1, 0, -2, 0, -4, 0, -1, 0, 1, 0, 0, 0, 0, 0, 8, 0, -2, 0, 2, 0, 2, 0, -8, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   finite := ((3008030843631027 : Rat)/9007199254740992, (5334132766546087 : Rat)/4503599627370496),   tail := (11811205609887788124074432197551727294921875 : Rat)/47133179186103571059895619727688494751940608,   box := { reLo := (8240382741953613776881793888472799714613955175971 : Rat)/98845440996495476255402218703161382146021749948416,            reHi := (70921978138287095637870473566621599434376616555351 : Rat)/49422720498247738127701109351580691073010874974208,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a2.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -2 }
def label : String := "112.b4"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -2 },   conductor := 112,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, -3, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   geometricUpper := (1243617669918357 : Rat)/2251799813685248,   tail := (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/1162598223803094879529139665734727376284046152541941330168458183961248946175639221827003488599114381772120415219576327913935549654429632504685494487779021533590742455771484067966638998907142668413829120,   box := { reLo := (196026222314447574742670933227788810493131689594602820561106273739677279653109584030454004532119749027633032909420228646141017461196287976218427478269018411615158795897815410321562864251954566690130743213 : Rat)/268560189698514917171231262784722023921614661237188447268913840495048506566572660242037805866395422189359815915722131748119111970173245108582349226676953974259461507283212819700293608747549956403594526720,            reHi := (28039511632659705050307756208762670813568815091928704184520233405758685648508881139487017179592086401963464055004974784572562619907760919376966173029771637874795904784244111108455765565783490366690445181 : Rat)/17904012646567661144748750852314801594774310749145896484594256033003233771104844016135853724426361479290654394381475449874607464678216340572156615111796931617297433818880854646686240583169997093572968448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/2325196447606189759058279331469454752568092305083882660336916367922497892351278443654006977198228763544240830439152655827871099308859265009370988975558043067181484911542968135933277997814285336827658240, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 12 = (List.range 12).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 12

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := -30 }
def label : String := "112.b3"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := -30 },   conductor := 112,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, -3, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   geometricUpper := (1243617669918357 : Rat)/2251799813685248,   tail := (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/1162598223803094879529139665734727376284046152541941330168458183961248946175639221827003488599114381772120415219576327913935549654429632504685494487779021533590742455771484067966638998907142668413829120,   box := { reLo := (196026222314447574742670933227788810493131689594602820561106273739677279653109584030454004532119749027633032909420228646141017461196287976218427478269018411615158795897815410321562864251954566690130743213 : Rat)/268560189698514917171231262784722023921614661237188447268913840495048506566572660242037805866395422189359815915722131748119111970173245108582349226676953974259461507283212819700293608747549956403594526720,            reHi := (28039511632659705050307756208762670813568815091928704184520233405758685648508881139487017179592086401963464055004974784572562619907760919376966173029771637874795904784244111108455765565783490366690445181 : Rat)/17904012646567661144748750852314801594774310749145896484594256033003233771104844016135853724426361479290654394381475449874607464678216340572156615111796931617297433818880854646686240583169997093572968448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/2325196447606189759058279331469454752568092305083882660336916367922497892351278443654006977198228763544240830439152655827871099308859265009370988975558043067181484911542968135933277997814285336827658240, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 12 = (List.range 12).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 12

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := -1990 }
def label : String := "112.b1"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := -1990 },   conductor := 112,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, -3, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   geometricUpper := (1243617669918357 : Rat)/2251799813685248,   tail := (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/1162598223803094879529139665734727376284046152541941330168458183961248946175639221827003488599114381772120415219576327913935549654429632504685494487779021533590742455771484067966638998907142668413829120,   box := { reLo := (196026222314447574742670933227788810493131689594602820561106273739677279653109584030454004532119749027633032909420228646141017461196287976218427478269018411615158795897815410321562864251954566690130743213 : Rat)/268560189698514917171231262784722023921614661237188447268913840495048506566572660242037805866395422189359815915722131748119111970173245108582349226676953974259461507283212819700293608747549956403594526720,            reHi := (28039511632659705050307756208762670813568815091928704184520233405758685648508881139487017179592086401963464055004974784572562619907760919376966173029771637874795904784244111108455765565783490366690445181 : Rat)/17904012646567661144748750852314801594774310749145896484594256033003233771104844016135853724426361479290654394381475449874607464678216340572156615111796931617297433818880854646686240583169997093572968448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/2325196447606189759058279331469454752568092305083882660336916367922497892351278443654006977198228763544240830439152655827871099308859265009370988975558043067181484911542968135933277997814285336827658240, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 12 = (List.range 12).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 12

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := 138 }
def label : String := "112.b2"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := 138 },   conductor := 112,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 12,   coefficients := [1, 0, 0, 0, 2, 0, 1, 0, -3, 0, 4, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/2272683070874307918548583984375,   alphaHi := (5397215081808807583452231630848 : Rat)/9090732283497231578826904296875,   geometricUpper := (1243617669918357 : Rat)/2251799813685248,   tail := (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/1162598223803094879529139665734727376284046152541941330168458183961248946175639221827003488599114381772120415219576327913935549654429632504685494487779021533590742455771484067966638998907142668413829120,   box := { reLo := (196026222314447574742670933227788810493131689594602820561106273739677279653109584030454004532119749027633032909420228646141017461196287976218427478269018411615158795897815410321562864251954566690130743213 : Rat)/268560189698514917171231262784722023921614661237188447268913840495048506566572660242037805866395422189359815915722131748119111970173245108582349226676953974259461507283212819700293608747549956403594526720,            reHi := (28039511632659705050307756208762670813568815091928704184520233405758685648508881139487017179592086401963464055004974784572562619907760919376966173029771637874795904784244111108455765565783490366690445181 : Rat)/17904012646567661144748750852314801594774310749145896484594256033003233771104844016135853724426361479290654394381475449874607464678216340572156615111796931617297433818880854646686240583169997093572968448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (486074571808328717415210006907579978789063943626715440765139266513209942801233710739954879050215940947277727923692756103051040737054764744736687875048878206432757714483051858139123635618642544783485877 : Rat)/2325196447606189759058279331469454752568092305083882660336916367922497892351278443654006977198228763544240830439152655827871099308859265009370988975558043067181484911542968135933277997814285336827658240, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 12 = (List.range 12).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 12

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := -16 }
def label : String := "112.c5"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1],              kodaira := -10 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c5

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -168, a6 := -784 }
def label : String := "112.c4"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c4

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 72, a6 := 368 }
def label : String := "112.c6"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -14 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c6

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -568, a6 := 4464 }
def label : String := "112.c3"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 0],              kodaira := -11 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c3

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2728, a6 := 55920 }
def label : String := "112.c2"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -26 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -43688, a6 := 3529328 }
def label : String := "112.c1"
def inputConductor : Nat := 112
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1.nonsingular
def localData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0],              kodaira := -17 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 112 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1.root_formula
end VerifiedLcalc.Certificates.ConductorRuns.Scda23290a1165b64_E2769e9f0e2788f6c.N112.C112_c1
