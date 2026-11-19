module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -54, a6 := 146 }
def label : String := "370.a1"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -54, a6 := 146 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -2, 1, -1, 2, -1, -1, 1, 1, 3, -2, -4, 1, 2, 1, 3, -1, 2, -1, 2, -3, 6, 2, 1, 4, 4, -1, 3, -2,                    5, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/18285138548613156673794723816501771734678803553078338045398529043763053837155305035712109753048707323377282140699455975326966687473051754806051444716757301493591027399300889785441950615378532158021989496016511864459558423355254955989332357695553626302486271716470894582789996079684525472195567454624173768502990010856560248488418134714781006063641699808565079411735810946703503905559312298413993505487930084077021300294616771132672315876282981578756412960678312791311528363437664789440860553222732158299275264,   box := { reLo := (2266142849578567868690996157117320078843721896769445094998166022260276653186227411279359731073376423742293192868206735530499641628998384898426794152236021601171596385727720527382354309134289867953622862558449142733170791013356664560989062947283305614847777617130902185876877600593905317681293329994823011995376184080146830765464631535401333360054088770396522200950080253717611520585638766013784244592890348071894481848072909146646054006180130057516144519518364958560256050602640879200637359029228566178619704362627141557 : Rat)/6347209066277558424685529427078887632708663543951229334238191651112197052786347431928596340544272696702925580271885885177577429348461561537850836073362882828134072611685848283157717958990800331891482965720971099803985093185288414953651671230384310291601837814897275212045252171042454361600021973695405275695238364717494557897001075873267618651085832995540241440265568626518243549958866184077081967692627869645179904984200822532688683530666434048484293541051719514650384001310402576318484648236539810487680489912428134400,            reHi := (3232051274358316992309555413766826627195181600916477000788151392583597355689583385730610672460292125036451355722314258540708450518910931517186230669129442806551264638200323383867054714169940390592127895420554319859606612387638866427147046512396975197637764886354649869206414059236067202617707186645932251962560555976614752982159554746605161315073152164167744524086544252526415557506767151128194499897088388376564326267714414245232204664077500611970153278792196427425664949874297271141718278400118211310647160660602866901 : Rat)/4342827255874118922153256976422396801326980319545577965531394287603082194011711400793250127740818160902001712817606131963605609554210542104845308892300919829775944418521896193739491235098968648136277818651190752497463484810986810231445880315526107041622310083877083039820435695976416142147383455686329925475689407438285750140053367702762054866532412049580165195971178533933535060498171599631687662105482226599333619199716352259208046626245454875278727159666965983708157474580801762744226338267106186123149808887450828800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/36570277097226313347589447633003543469357607106156676090797058087526107674310610071424219506097414646754564281398911950653933374946103509612102889433514602987182054798601779570883901230757064316043978992033023728919116846710509911978664715391107252604972543432941789165579992159369050944391134909248347537005980021713120496976836269429562012127283399617130158823471621893407007811118624596827987010975860168154042600589233542265344631752565963157512825921356625582623056726875329578881721106445464316598550528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -19, a6 := 342 }
def label : String := "370.a2"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 5, 5, 5, 37, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -19, a6 := 342 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -2, 1, -1, 2, -1, -1, 1, 1, 3, -2, -4, 1, 2, 1, 3, -1, 2, -1, 2, -3, 6, 2, 1, 4, 4, -1, 3, -2,                    5, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/18285138548613156673794723816501771734678803553078338045398529043763053837155305035712109753048707323377282140699455975326966687473051754806051444716757301493591027399300889785441950615378532158021989496016511864459558423355254955989332357695553626302486271716470894582789996079684525472195567454624173768502990010856560248488418134714781006063641699808565079411735810946703503905559312298413993505487930084077021300294616771132672315876282981578756412960678312791311528363437664789440860553222732158299275264,   box := { reLo := (2266142849578567868690996157117320078843721896769445094998166022260276653186227411279359731073376423742293192868206735530499641628998384898426794152236021601171596385727720527382354309134289867953622862558449142733170791013356664560989062947283305614847777617130902185876877600593905317681293329994823011995376184080146830765464631535401333360054088770396522200950080253717611520585638766013784244592890348071894481848072909146646054006180130057516144519518364958560256050602640879200637359029228566178619704362627141557 : Rat)/6347209066277558424685529427078887632708663543951229334238191651112197052786347431928596340544272696702925580271885885177577429348461561537850836073362882828134072611685848283157717958990800331891482965720971099803985093185288414953651671230384310291601837814897275212045252171042454361600021973695405275695238364717494557897001075873267618651085832995540241440265568626518243549958866184077081967692627869645179904984200822532688683530666434048484293541051719514650384001310402576318484648236539810487680489912428134400,            reHi := (3232051274358316992309555413766826627195181600916477000788151392583597355689583385730610672460292125036451355722314258540708450518910931517186230669129442806551264638200323383867054714169940390592127895420554319859606612387638866427147046512396975197637764886354649869206414059236067202617707186645932251962560555976614752982159554746605161315073152164167744524086544252526415557506767151128194499897088388376564326267714414245232204664077500611970153278792196427425664949874297271141718278400118211310647160660602866901 : Rat)/4342827255874118922153256976422396801326980319545577965531394287603082194011711400793250127740818160902001712817606131963605609554210542104845308892300919829775944418521896193739491235098968648136277818651190752497463484810986810231445880315526107041622310083877083039820435695976416142147383455686329925475689407438285750140053367702762054866532412049580165195971178533933535060498171599631687662105482226599333619199716352259208046626245454875278727159666965983708157474580801762744226338267106186123149808887450828800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/36570277097226313347589447633003543469357607106156676090797058087526107674310610071424219506097414646754564281398911950653933374946103509612102889433514602987182054798601779570883901230757064316043978992033023728919116846710509911978664715391107252604972543432941789165579992159369050944391134909248347537005980021713120496976836269429562012127283399617130158823471621893407007811118624596827987010975860168154042600589233542265344631752565963157512825921356625582623056726875329578881721106445464316598550528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 166, a6 := -9204 }
def label : String := "370.a3"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 166, a6 := -9204 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, -2, 1, -1, 2, -1, -1, 1, 1, 3, -2, -4, 1, 2, 1, 3, -1, 2, -1, 2, -3, 6, 2, 1, 4, 4, -1, 3, -2,                    5, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/18285138548613156673794723816501771734678803553078338045398529043763053837155305035712109753048707323377282140699455975326966687473051754806051444716757301493591027399300889785441950615378532158021989496016511864459558423355254955989332357695553626302486271716470894582789996079684525472195567454624173768502990010856560248488418134714781006063641699808565079411735810946703503905559312298413993505487930084077021300294616771132672315876282981578756412960678312791311528363437664789440860553222732158299275264,   box := { reLo := (2266142849578567868690996157117320078843721896769445094998166022260276653186227411279359731073376423742293192868206735530499641628998384898426794152236021601171596385727720527382354309134289867953622862558449142733170791013356664560989062947283305614847777617130902185876877600593905317681293329994823011995376184080146830765464631535401333360054088770396522200950080253717611520585638766013784244592890348071894481848072909146646054006180130057516144519518364958560256050602640879200637359029228566178619704362627141557 : Rat)/6347209066277558424685529427078887632708663543951229334238191651112197052786347431928596340544272696702925580271885885177577429348461561537850836073362882828134072611685848283157717958990800331891482965720971099803985093185288414953651671230384310291601837814897275212045252171042454361600021973695405275695238364717494557897001075873267618651085832995540241440265568626518243549958866184077081967692627869645179904984200822532688683530666434048484293541051719514650384001310402576318484648236539810487680489912428134400,            reHi := (3232051274358316992309555413766826627195181600916477000788151392583597355689583385730610672460292125036451355722314258540708450518910931517186230669129442806551264638200323383867054714169940390592127895420554319859606612387638866427147046512396975197637764886354649869206414059236067202617707186645932251962560555976614752982159554746605161315073152164167744524086544252526415557506767151128194499897088388376564326267714414245232204664077500611970153278792196427425664949874297271141718278400118211310647160660602866901 : Rat)/4342827255874118922153256976422396801326980319545577965531394287603082194011711400793250127740818160902001712817606131963605609554210542104845308892300919829775944418521896193739491235098968648136277818651190752497463484810986810231445880315526107041622310083877083039820435695976416142147383455686329925475689407438285750140053367702762054866532412049580165195971178533933535060498171599631687662105482226599333619199716352259208046626245454875278727159666965983708157474580801762744226338267106186123149808887450828800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/36570277097226313347589447633003543469357607106156676090797058087526107674310610071424219506097414646754564281398911950653933374946103509612102889433514602987182054798601779570883901230757064316043978992033023728919116846710509911978664715391107252604972543432941789165579992159369050944391134909248347537005980021713120496976836269429562012127283399617130158823471621893407007811118624596827987010975860168154042600589233542265344631752565963157512825921356625582623056726875329578881721106445464316598550528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_a3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -395, a6 := -2925 }
def label : String := "370.b1"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 5, 5, 5, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -395, a6 := -2925 },   conductor := 370,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, 0, -1, -3, 1, -4, 0, 2, 0, 0, 1, -2, 3, -4, -1, 0, 4, 0, 0, 1, -2, 0, 0, -6, 0,                    -4, -1, 0, 2, 0, -3, -1, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   finite := ((2330730471443157 : Rat)/2251799813685248, (28263182709529103 : Rat)/9007199254740992),   tail := (399827739831130492974706862470340728759765625 : Rat)/726939836801029520286912345615574950517669888,   box := { reLo := (92430133195610447977391056584151124644583531216173 : Rat)/190562916578369082566092349929049279828504055119872,            reHi := (2811076299587089950048125091315592136468409529250967 : Rat)/762251666313476330264369399716197119314016220479488,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -25, a6 := -39 }
def label : String := "370.b2"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -25, a6 := -39 },   conductor := 370,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, 0, -1, -3, 1, -4, 0, 2, 0, 0, 1, -2, 3, -4, -1, 0, 4, 0, 0, 1, -2, 0, 0, -6, 0,                    -4, -1, 0, 2, 0, -3, -1, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   finite := ((2330730471443157 : Rat)/2251799813685248, (28263182709529103 : Rat)/9007199254740992),   tail := (399827739831130492974706862470340728759765625 : Rat)/726939836801029520286912345615574950517669888,   box := { reLo := (92430133195610447977391056584151124644583531216173 : Rat)/190562916578369082566092349929049279828504055119872,            reHi := (2811076299587089950048125091315592136468409529250967 : Rat)/762251666313476330264369399716197119314016220479488,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := 5 }
def label : String := "370.b3"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := 5 },   conductor := 370,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, 0, -1, -3, 1, -4, 0, 2, 0, 0, 1, -2, 3, -4, -1, 0, 4, 0, 0, 1, -2, 0, 0, -6, 0,                    -4, -1, 0, 2, 0, -3, -1, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   finite := ((2330730471443157 : Rat)/2251799813685248, (28263182709529103 : Rat)/9007199254740992),   tail := (399827739831130492974706862470340728759765625 : Rat)/726939836801029520286912345615574950517669888,   box := { reLo := (92430133195610447977391056584151124644583531216173 : Rat)/190562916578369082566092349929049279828504055119872,            reHi := (2811076299587089950048125091315592136468409529250967 : Rat)/762251666313476330264369399716197119314016220479488,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 25, a6 := -209 }
def label : String := "370.b4"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 5, 37, 37, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 25, a6 := -209 },   conductor := 370,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, 0, -1, -3, 1, -4, 0, 2, 0, 0, 1, -2, 3, -4, -1, 0, 4, 0, 0, 1, -2, 0, 0, -6, 0,                    -4, -1, 0, 2, 0, -3, -1, 4, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   finite := ((2330730471443157 : Rat)/2251799813685248, (28263182709529103 : Rat)/9007199254740992),   tail := (399827739831130492974706862470340728759765625 : Rat)/726939836801029520286912345615574950517669888,   box := { reLo := (92430133195610447977391056584151124644583531216173 : Rat)/190562916578369082566092349929049279828504055119872,            reHi := (2811076299587089950048125091315592136468409529250967 : Rat)/762251666313476330264369399716197119314016220479488,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_b4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 13, a6 := -19 }
def label : String := "370.c1"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 13, a6 := -19 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 2, 1, 1, -2, 1, -1, 1, -1, 3, 2, 0, -1, 2, 1, 3, -1, -6, 1, 2, -3, 2, -2, 1, 0, -4, 1, -3, -2,                    3, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/18285138548613156673794723816501771734678803553078338045398529043763053837155305035712109753048707323377282140699455975326966687473051754806051444716757301493591027399300889785441950615378532158021989496016511864459558423355254955989332357695553626302486271716470894582789996079684525472195567454624173768502990010856560248488418134714781006063641699808565079411735810946703503905559312298413993505487930084077021300294616771132672315876282981578756412960678312791311528363437664789440860553222732158299275264,   box := { reLo := (66159960423809469243045043348745812289173030192443935788842838681562870562636942576864153150139264920300189754947832828244109003706729716096656449502598152146799619078677706954875605605955846768683985105994129887439233684578559580573916487701225695170329303534409386787618251065123918022762175005831317589648218895495549616386658072665520425121022243063712082049642800726611255114667659290423097223698544930535773487978540393303285371024911952017131447448386008516813470981338021095665449082034205364574552044564091249 : Rat)/47723376438177131012673153587059305509087695819182175445399937226407496637491334074651100304844155614307711129863803647951709995101214748404893504310999119008526861741998859271862541045043611517981074930232865412060038294626228683862042640829957220237607803119528385052971820834905671891729488524025603576655927554266876375165421623107275328203652879665716101054628335537731154510968918677271292990170134358234435375821058816035253259629070932695370628128208417403386345874514305085101388332605562484869778119642316800,            reHi := (11256899133927169531901062582388968911220381075415659378507646293246024271063913556017643065010001553700157829219458820244714179996398697323852214182495249438603067482314694660091375115210698833110980058440596685866044396002873343375796141606347293111259426878734429570940051623347903044459250181579767402592052250986475783145291826224473408196297896925449857641241621092351195687181331896257425773984087686891030483743632849340576089059469784810396337705339481657786996083198572258447721352117726089801658909841859637323 : Rat)/6347209066277558424685529427078887632708663543951229334238191651112197052786347431928596340544272696702925580271885885177577429348461561537850836073362882828134072611685848283157717958990800331891482965720971099803985093185288414953651671230384310291601837814897275212045252171042454361600021973695405275695238364717494557897001075873267618651085832995540241440265568626518243549958866184077081967692627869645179904984200822532688683530666434048484293541051719514650384001310402576318484648236539810487680489912428134400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (3539981284734993080533372854721536448540144390078359806531748784860762052722268214063660774374228232603290551975927430859019542622177035563682846443218732782228428818578924234554805609268054177039448144670153254869428673867419867085117546840484710940121392840340475053413349530674972042088511666700835836814387287060400699916750752665523711854389588509072218910450213300733784504971999052893904632654418452447571357716777453236583169942814695407448295651599947691163741198799963411533069874593100500183861011 : Rat)/36570277097226313347589447633003543469357607106156676090797058087526107674310610071424219506097414646754564281398911950653933374946103509612102889433514602987182054798601779570883901230757064316043978992033023728919116846710509911978664715391107252604972543432941789165579992159369050944391134909248347537005980021713120496976836269429562012127283399617130158823471621893407007811118624596827987010975860168154042600589233542265344631752565963157512825921356625582623056726875329578881721106445464316598550528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5275, a6 := -147903 }
def label : String := "370.d1"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 37, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5275, a6 := -147903 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, -2, 1, 1, -2, 2, 1, 1, 1, 0, -2, 2, 2, -2, 1, 6, 1, 2, 1, -4, 0, 0, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/44681061175941257230909540505612356712861437655645015743399210606631603943914080050165971276915210085493148715199635759524492637802655899149148809307827073203175708385103729972059320649013521962862140911201828317780316644154885724735894736541020750286499731785453023745355722941709388582410880010454381495007594178069289070232451262087142282059337270875603492221088684922602902442213376,   box := { reLo := (182385529240261188000555498027721401876844247501120781227005449279161413867930788868600638117920061256744248187727377438293522956499918635317979703300148769331442471404062109941733408613020640019408437204230704434638095353279752328776674700050225997408581040850971116005071878890127594095361852188332396763015867404019246299815331241363169262303864844475279040788332868326397899683083795039 : Rat)/2814236638166660086688837408745994287559577650740801316597999280058691574407428331959703700876504507234785971826849058313650168792000281807909137754253488205702021992635758432290156311078116680830871945292047156595393243832095477372490329981036191956795185606506758700601230209483565839863149277458469218463053319305694172088590942742558656635507358006099885957545270819850143810322809487360,            reHi := (227835509173521048828954107761086533546005177409901467645469647360103984853027222827837141406585337361736234704048702075366004984241114616555651697076422329248615738317098050436418640058250614816712230828014734423708020079211636861952996993656402153011069633422617612119362017173520389049205826928836362302743067097343971119709182962556616816417466903952069802255326325357922228516856416083 : Rat)/69121601639181124936217059162182315834796644053282839355038578808459091301235081837606757565387830002257901062413836519984390110680708675983733207999208482245312820871755470266775769044023918476547731989629228407606149848507608216166429157428959100693215085072095827734065303390824424136989631376172928172776748193473190191649602102448809110345794758044558602466024195575266690078104092672,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/89362122351882514461819081011224713425722875311290031486798421213263207887828160100331942553830420170986297430399271519048985275605311798298297618615654146406351416770207459944118641298027043925724281822403656635560633288309771449471789473082041500572999463570906047490711445883418777164821760020908762990015188356138578140464902524174284564118674541751206984442177369845205804884426752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5255, a6 := -149075 }
def label : String := "370.d2"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 5, 5, 37, 37, 37, 37, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5255, a6 := -149075 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, -2, 1, 1, -2, 2, 1, 1, 1, 0, -2, 2, 2, -2, 1, 6, 1, 2, 1, -4, 0, 0, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/44681061175941257230909540505612356712861437655645015743399210606631603943914080050165971276915210085493148715199635759524492637802655899149148809307827073203175708385103729972059320649013521962862140911201828317780316644154885724735894736541020750286499731785453023745355722941709388582410880010454381495007594178069289070232451262087142282059337270875603492221088684922602902442213376,   box := { reLo := (182385529240261188000555498027721401876844247501120781227005449279161413867930788868600638117920061256744248187727377438293522956499918635317979703300148769331442471404062109941733408613020640019408437204230704434638095353279752328776674700050225997408581040850971116005071878890127594095361852188332396763015867404019246299815331241363169262303864844475279040788332868326397899683083795039 : Rat)/2814236638166660086688837408745994287559577650740801316597999280058691574407428331959703700876504507234785971826849058313650168792000281807909137754253488205702021992635758432290156311078116680830871945292047156595393243832095477372490329981036191956795185606506758700601230209483565839863149277458469218463053319305694172088590942742558656635507358006099885957545270819850143810322809487360,            reHi := (227835509173521048828954107761086533546005177409901467645469647360103984853027222827837141406585337361736234704048702075366004984241114616555651697076422329248615738317098050436418640058250614816712230828014734423708020079211636861952996993656402153011069633422617612119362017173520389049205826928836362302743067097343971119709182962556616816417466903952069802255326325357922228516856416083 : Rat)/69121601639181124936217059162182315834796644053282839355038578808459091301235081837606757565387830002257901062413836519984390110680708675983733207999208482245312820871755470266775769044023918476547731989629228407606149848507608216166429157428959100693215085072095827734065303390824424136989631376172928172776748193473190191649602102448809110345794758044558602466024195575266690078104092672,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/89362122351882514461819081011224713425722875311290031486798421213263207887828160100331942553830420170986297430399271519048985275605311798298297618615654146406351416770207459944118641298027043925724281822403656635560633288309771449471789473082041500572999463570906047490711445883418777164821760020908762990015188356138578140464902524174284564118674541751206984442177369845205804884426752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -75, a6 := -143 }
def label : String := "370.d3"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -75, a6 := -143 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, -2, 1, 1, -2, 2, 1, 1, 1, 0, -2, 2, 2, -2, 1, 6, 1, 2, 1, -4, 0, 0, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/44681061175941257230909540505612356712861437655645015743399210606631603943914080050165971276915210085493148715199635759524492637802655899149148809307827073203175708385103729972059320649013521962862140911201828317780316644154885724735894736541020750286499731785453023745355722941709388582410880010454381495007594178069289070232451262087142282059337270875603492221088684922602902442213376,   box := { reLo := (182385529240261188000555498027721401876844247501120781227005449279161413867930788868600638117920061256744248187727377438293522956499918635317979703300148769331442471404062109941733408613020640019408437204230704434638095353279752328776674700050225997408581040850971116005071878890127594095361852188332396763015867404019246299815331241363169262303864844475279040788332868326397899683083795039 : Rat)/2814236638166660086688837408745994287559577650740801316597999280058691574407428331959703700876504507234785971826849058313650168792000281807909137754253488205702021992635758432290156311078116680830871945292047156595393243832095477372490329981036191956795185606506758700601230209483565839863149277458469218463053319305694172088590942742558656635507358006099885957545270819850143810322809487360,            reHi := (227835509173521048828954107761086533546005177409901467645469647360103984853027222827837141406585337361736234704048702075366004984241114616555651697076422329248615738317098050436418640058250614816712230828014734423708020079211636861952996993656402153011069633422617612119362017173520389049205826928836362302743067097343971119709182962556616816417466903952069802255326325357922228516856416083 : Rat)/69121601639181124936217059162182315834796644053282839355038578808459091301235081837606757565387830002257901062413836519984390110680708675983733207999208482245312820871755470266775769044023918476547731989629228407606149848507608216166429157428959100693215085072095827734065303390824424136989631376172928172776748193473190191649602102448809110345794758044558602466024195575266690078104092672,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/89362122351882514461819081011224713425722875311290031486798421213263207887828160100331942553830420170986297430399271519048985275605311798298297618615654146406351416770207459944118641298027043925724281822403656635560633288309771449471789473082041500572999463570906047490711445883418777164821760020908762990015188356138578140464902524174284564118674541751206984442177369845205804884426752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 245, a6 := -975 }
def label : String := "370.d4"
def inputConductor : Nat := 370
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 37, 37] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 370 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 245, a6 := -975 },   conductor := 370,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, -2, 1, 1, -2, 2, 1, 1, 1, 0, -2, 2, 2, -2, 1, 6, 1, 2, 1, -4, 0, 0, -2],   alphaLo := (5397215081808807583435051761664 : Rat)/16523069094175614643096923828125,   alphaHi := (1349303770452201895863057907712 : Rat)/4130767273543903636932373046875,   geometricUpper := (1624309112128953 : Rat)/2251799813685248,   tail := (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/44681061175941257230909540505612356712861437655645015743399210606631603943914080050165971276915210085493148715199635759524492637802655899149148809307827073203175708385103729972059320649013521962862140911201828317780316644154885724735894736541020750286499731785453023745355722941709388582410880010454381495007594178069289070232451262087142282059337270875603492221088684922602902442213376,   box := { reLo := (182385529240261188000555498027721401876844247501120781227005449279161413867930788868600638117920061256744248187727377438293522956499918635317979703300148769331442471404062109941733408613020640019408437204230704434638095353279752328776674700050225997408581040850971116005071878890127594095361852188332396763015867404019246299815331241363169262303864844475279040788332868326397899683083795039 : Rat)/2814236638166660086688837408745994287559577650740801316597999280058691574407428331959703700876504507234785971826849058313650168792000281807909137754253488205702021992635758432290156311078116680830871945292047156595393243832095477372490329981036191956795185606506758700601230209483565839863149277458469218463053319305694172088590942742558656635507358006099885957545270819850143810322809487360,            reHi := (227835509173521048828954107761086533546005177409901467645469647360103984853027222827837141406585337361736234704048702075366004984241114616555651697076422329248615738317098050436418640058250614816712230828014734423708020079211636861952996993656402153011069633422617612119362017173520389049205826928836362302743067097343971119709182962556616816417466903952069802255326325357922228516856416083 : Rat)/69121601639181124936217059162182315834796644053282839355038578808459091301235081837606757565387830002257901062413836519984390110680708675983733207999208482245312820871755470266775769044023918476547731989629228407606149848507608216166429157428959100693215085072095827734065303390824424136989631376172928172776748193473190191649602102448809110345794758044558602466024195575266690078104092672,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (72190001485355511651104294886142146004286357852191374165379794155263231007950651978048624048892820944656706134943526130203038032757131613640918252705332587828544986705437988554820892856706646709862517116702971440002044154288780981667027253029976152934496128028836171672971761230058676291107336066545335537296336308805721177862021872302047473000940749861848671318843814894247844997265625 : Rat)/89362122351882514461819081011224713425722875311290031486798421213263207887828160100331942553830420170986297430399271519048985275605311798298297618615654146406351416770207459944118641298027043925724281822403656635560633288309771449471789473082041500572999463570906047490711445883418777164821760020908762990015188356138578140464902524174284564118674541751206984442177369845205804884426752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N370.C370_d4
