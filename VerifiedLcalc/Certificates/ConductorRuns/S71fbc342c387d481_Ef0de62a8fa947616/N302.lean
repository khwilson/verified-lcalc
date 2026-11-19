module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -39, a6 := 77 }
def label : String := "302.a1"
def inputConductor : Nat := 302
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 151, 151] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 302 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -39, a6 := 77 },   conductor := 302,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 2, 1, 2, -2, 4, -1, 1, -2, -4, 2, 0, -4, 4, 1, -6, -1, 0, 2, 8, 4, 0, -2],   alphaLo := (2698607540904403791717525880832 : Rat)/7463857387611505413055419921875,   alphaHi := (5397215081808807583452231630848 : Rat)/14927714775223010730743408203125,   geometricUpper := (3137167454779587 : Rat)/4503599627370496,   tail := (1012051373475143311207615131707791602278530976807023084501566187149470364998560252033376772579713958125088949845879564818534499960477094279440204900606178416687653403506622979471954542513176959385001581459533609973896605755255108408387698328013472596151468264302204852224134952892408829188427642259026643923883956537254241526212273833308181086181463153558568954959246799991314598925449338671875 : Rat)/1681819707573972061587241902217073028336128910905726008163524457144153765209938160918216748955935359375353870801853315836131142602250273949483665584613367026004878720553205702899173816480697387834968456347903890111170544698138303308674205840232784766453044506217436813886102463573839914468401386826882737488890051255871703503156536855813731899079886038205485584815330390942382524704450532081664,   box := { reLo := (19681789030937188001892700386456565923325056187085622340076628692668245986792970305066646450639412789904120492965441881726289888440777883835244327416152693965357808751841370516298033220557353366153305547080363090336881177559802220543484337220602309852089941349582810181879125823371169988828870465521651229596825884907593279975244463883816310671614272870188243269719686355983159546343024965226354417 : Rat)/19813517974928964857559296850019337346827934699380358102174481629615275507938281473777511519449874468801043951916633913865460990997110477398867064252330076933363476206837316385855166731959095926083763384234655729399700187088767351279490819003782437333583317327747623104392173123363408032352236738207505530356613693845424538970687160698341575503060137416098825674709407335692208523543131718454083584,            reHi := (217638717463792757709061142676456922894594961017161390571187255487002703702012866187917639455148877607387778972828862925815662877403135628409115056948127268533320534130103570829542677805236230225081630035648789631909347102414864085362385599323196652781331327865646225896474125259355344012142206787709316953559158530595108842787442141471486199229210764087423534613426471400361220964285530882966441291 : Rat)/99067589874644824287796484250096686734139673496901790510872408148076377539691407368887557597249372344005219759583169569327304954985552386994335321261650384666817381034186581929275833659795479630418816921173278646998500935443836756397454095018912186667916586638738115521960865616817040161761183691037527651783068469227122694853435803491707877515300687080494128373547036678461042617715658592270417920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1012051373475143311207615131707791602278530976807023084501566187149470364998560252033376772579713958125088949845879564818534499960477094279440204900606178416687653403506622979471954542513176959385001581459533609973896605755255108408387698328013472596151468264302204852224134952892408829188427642259026643923883956537254241526212273833308181086181463153558568954959246799991314598925449338671875 : Rat)/3363639415147944123174483804434146056672257821811452016327048914288307530419876321836433497911870718750707741603706631672262285204500547898967331169226734052009757441106411405798347632961394775669936912695807780222341089396276606617348411680465569532906089012434873627772204927147679828936802773653765474977780102511743407006313073711627463798159772076410971169630660781884765049408901064163328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 1, a6 := 5 }
def label : String := "302.a2"
def inputConductor : Nat := 302
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 151] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 302 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 1, a6 := 5 },   conductor := 302,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, -1, 2, 1, 2, -2, 4, -1, 1, -2, -4, 2, 0, -4, 4, 1, -6, -1, 0, 2, 8, 4, 0, -2],   alphaLo := (2698607540904403791717525880832 : Rat)/7463857387611505413055419921875,   alphaHi := (5397215081808807583452231630848 : Rat)/14927714775223010730743408203125,   geometricUpper := (3137167454779587 : Rat)/4503599627370496,   tail := (1012051373475143311207615131707791602278530976807023084501566187149470364998560252033376772579713958125088949845879564818534499960477094279440204900606178416687653403506622979471954542513176959385001581459533609973896605755255108408387698328013472596151468264302204852224134952892408829188427642259026643923883956537254241526212273833308181086181463153558568954959246799991314598925449338671875 : Rat)/1681819707573972061587241902217073028336128910905726008163524457144153765209938160918216748955935359375353870801853315836131142602250273949483665584613367026004878720553205702899173816480697387834968456347903890111170544698138303308674205840232784766453044506217436813886102463573839914468401386826882737488890051255871703503156536855813731899079886038205485584815330390942382524704450532081664,   box := { reLo := (19681789030937188001892700386456565923325056187085622340076628692668245986792970305066646450639412789904120492965441881726289888440777883835244327416152693965357808751841370516298033220557353366153305547080363090336881177559802220543484337220602309852089941349582810181879125823371169988828870465521651229596825884907593279975244463883816310671614272870188243269719686355983159546343024965226354417 : Rat)/19813517974928964857559296850019337346827934699380358102174481629615275507938281473777511519449874468801043951916633913865460990997110477398867064252330076933363476206837316385855166731959095926083763384234655729399700187088767351279490819003782437333583317327747623104392173123363408032352236738207505530356613693845424538970687160698341575503060137416098825674709407335692208523543131718454083584,            reHi := (217638717463792757709061142676456922894594961017161390571187255487002703702012866187917639455148877607387778972828862925815662877403135628409115056948127268533320534130103570829542677805236230225081630035648789631909347102414864085362385599323196652781331327865646225896474125259355344012142206787709316953559158530595108842787442141471486199229210764087423534613426471400361220964285530882966441291 : Rat)/99067589874644824287796484250096686734139673496901790510872408148076377539691407368887557597249372344005219759583169569327304954985552386994335321261650384666817381034186581929275833659795479630418816921173278646998500935443836756397454095018912186667916586638738115521960865616817040161761183691037527651783068469227122694853435803491707877515300687080494128373547036678461042617715658592270417920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1012051373475143311207615131707791602278530976807023084501566187149470364998560252033376772579713958125088949845879564818534499960477094279440204900606178416687653403506622979471954542513176959385001581459533609973896605755255108408387698328013472596151468264302204852224134952892408829188427642259026643923883956537254241526212273833308181086181463153558568954959246799991314598925449338671875 : Rat)/3363639415147944123174483804434146056672257821811452016327048914288307530419876321836433497911870718750707741603706631672262285204500547898967331169226734052009757441106411405798347632961394775669936912695807780222341089396276606617348411680465569532906089012434873627772204927147679828936802773653765474977780102511743407006313073711627463798159772076410971169630660781884765049408901064163328, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 3 }
def label : String := "302.b1"
def inputConductor : Nat := 302
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 151] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 302 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 3 },   conductor := 302,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -3, 1, 0, -3, -2, 1, 6, 0, -6, -3, -2, -2, 0, 1, -5, 6, -8, 0, 6, -6, 6, -3, -5, -2, -9, -2, 8,                    0, 9, 1, 18, -5, 0, 6, 2, -8, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7463857387611505413055419921875,   alphaHi := (5397215081808807583452231630848 : Rat)/14927714775223010730743408203125,   finite := ((11916968286956411 : Rat)/9007199254740992, (1812140561982973 : Rat)/562949953421312),   tail := (41326623289506052060245819248981475830078125 : Rat)/148182619706719546012938795953881589068333056,   box := { reLo := (324484531122468948140452557718135035329083250770321 : Rat)/310761477283186309360126621812274682277832805056512,            reHi := (67938248721727046075836933725926769835146930694103 : Rat)/19422592330199144335007913863267167642364550316032,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -230, a6 := 1251 }
def label : String := "302.c1"
def inputConductor : Nat := 302
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 151] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 302 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -230, a6 := 1251 },   conductor := 302,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, -2, 1, -2, -4, 2, -1, -6, -2, 4, 1, 3, -2, 0, -4, 2, 2, -6, -1, 11, -6, 5, -2,                    0, 4, -3, 1, -2, 3, 8, -2, -2, 0, 6, -4],   alphaLo := (2698607540904403791717525880832 : Rat)/7463857387611505413055419921875,   alphaHi := (5397215081808807583452231630848 : Rat)/14927714775223010730743408203125,   finite := ((6613053551482821 : Rat)/4503599627370496, (16175683432510187 : Rat)/4503599627370496),   tail := (41326623289506052060245819248981475830078125 : Rat)/148182619706719546012938795953881589068333056,   box := { reLo := (184825862355634950859555124093745594726966638198831 : Rat)/155380738641593154680063310906137341138916402528256,            reHi := (601418714929148839648673858429554265830784644018657 : Rat)/155380738641593154680063310906137341138916402528256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 1650, a6 := -27389 }
def label : String := "302.c2"
def inputConductor : Nat := 302
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 151, 151, 151, 151, 151] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 302 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 1650, a6 := -27389 },   conductor := 302,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -4, -1, -2, 1, -2, -4, 2, -1, -6, -2, 4, 1, 3, -2, 0, -4, 2, 2, -6, -1, 11, -6, 5, -2,                    0, 4, -3, 1, -2, 3, 8, -2, -2, 0, 6, -4],   alphaLo := (2698607540904403791717525880832 : Rat)/7463857387611505413055419921875,   alphaHi := (5397215081808807583452231630848 : Rat)/14927714775223010730743408203125,   finite := ((6613053551482821 : Rat)/4503599627370496, (16175683432510187 : Rat)/4503599627370496),   tail := (41326623289506052060245819248981475830078125 : Rat)/148182619706719546012938795953881589068333056,   box := { reLo := (184825862355634950859555124093745594726966638198831 : Rat)/155380738641593154680063310906137341138916402528256,            reHi := (601418714929148839648673858429554265830784644018657 : Rat)/155380738641593154680063310906137341138916402528256,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N302.C302_c2
