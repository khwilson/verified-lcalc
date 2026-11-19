module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1998, a6 := -35148 }
def label : String := "570.a1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1998, a6 := -35148 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, -1, 1, -1, 1, -2, -1, 1, 1, 4, -1, -6, 2, 1, 1, 4, -1, 1, -1, 2, -4, 4, 1, 1, 6, -1, -2, 6,                    -1, -6, -1, -4, -4, 2, 1, 10, -1, 6, 1, 4, -2, 12, 4, -1, -4, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (215951671233755340830273087392472802741121235247233507749921918205445349485341193141772821058208925013827784484136940069029917026278025886277977723336816319248787774215869171289506522227825841925075937041802110845572888495938131965533526062154797494072510001269753813004110750900091330459280365628810213081239355282015913199049036305938954424256610435013568227572091959513226167682000263920800205201031688828971906129840136710171304106404010588113776101064572683411414629422681693117456309450952697842951005871475999703077191934664816044695677118650802898675808233147180018939161733943540399464386123774265412658343347991684538714374040210782960521710757487667199230263497985753775587787229079166268653221087372275110229281681189410198998059803439205040500765445236681811 : Rat)/330298540419524959276229493802049203369742609050730174104163941526830113186251271877887566363660817578524972090560011147326478084568412365189316489042796106546237480507509501907651953333501438716668450978533352235672191379138003786630694416563821096835385757697921463331103949854424354618429347742537545732333803248623079306189586917779503448369067902098737581654912359336110139439054993645595058866713724927915400308852184875738096241818529788602376446638445501331692503735685390462986148509678451964200342753733632562349932261108920632624384698230982553300903279273698359867286089892132757180633138763552416622088598422985859243499559819050326033091286086033850014975343334070594198750373875557906402436002331427405862554063300362564328825644657022680800109939340083200,            reHi := (48862271592604814962176206284254803678365866272140639157347055069891409462789189738507877397217694153546263919765507096959918137960533687133397613891469359742705113845385325224220619860593734928259191903075858218516304495115860767373914713319779287738233536800741001145881682780755649829388886109219059865243348025355286398606490824287224081692866909965879285318199395496024638211546498192122219385721472174220828063505792379444868085964427284979181166772967284139323377118712633412823367457848325111640247956185970827710651490487496810204677314952280506822685510020262573431813226805609808915050984621949787453611145387911823813736359781697819724321222889257625523511265559534834959338706043886025058846628379675081297785096583560332660850420705043714802953028370613 : Rat)/63090023563015295420230125443925758781200484869410601676057426387974426401571573599443698702062155468308496820704488595684881377036921048170451796201475644220694567124275699513826622247722210516548844020124122066116417269978382988648687150499263588568685271860593306554182168150079370215090829447120125363194510794559525715500084017058814604580557008749098761678335188466577593178323107515366299263313146186835673815468221063668359188221649266932286149513528763976121308339306880123490348700177904556032020166216916142065244754989850122522382218963008319076362689718687117198052421075788551500216439803826823098341661028423945878579931876314373350440465426934252988781933199393266383285090683076419465415130612400601113059618162786525922068695398584123477285299814400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -78, a6 := -972 }
def label : String := "570.a2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -78, a6 := -972 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, -1, 1, -1, 1, -2, -1, 1, 1, 4, -1, -6, 2, 1, 1, 4, -1, 1, -1, 2, -4, 4, 1, 1, 6, -1, -2, 6,                    -1, -6, -1, -4, -4, 2, 1, 10, -1, 6, 1, 4, -2, 12, 4, -1, -4, 4, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (215951671233755340830273087392472802741121235247233507749921918205445349485341193141772821058208925013827784484136940069029917026278025886277977723336816319248787774215869171289506522227825841925075937041802110845572888495938131965533526062154797494072510001269753813004110750900091330459280365628810213081239355282015913199049036305938954424256610435013568227572091959513226167682000263920800205201031688828971906129840136710171304106404010588113776101064572683411414629422681693117456309450952697842951005871475999703077191934664816044695677118650802898675808233147180018939161733943540399464386123774265412658343347991684538714374040210782960521710757487667199230263497985753775587787229079166268653221087372275110229281681189410198998059803439205040500765445236681811 : Rat)/330298540419524959276229493802049203369742609050730174104163941526830113186251271877887566363660817578524972090560011147326478084568412365189316489042796106546237480507509501907651953333501438716668450978533352235672191379138003786630694416563821096835385757697921463331103949854424354618429347742537545732333803248623079306189586917779503448369067902098737581654912359336110139439054993645595058866713724927915400308852184875738096241818529788602376446638445501331692503735685390462986148509678451964200342753733632562349932261108920632624384698230982553300903279273698359867286089892132757180633138763552416622088598422985859243499559819050326033091286086033850014975343334070594198750373875557906402436002331427405862554063300362564328825644657022680800109939340083200,            reHi := (48862271592604814962176206284254803678365866272140639157347055069891409462789189738507877397217694153546263919765507096959918137960533687133397613891469359742705113845385325224220619860593734928259191903075858218516304495115860767373914713319779287738233536800741001145881682780755649829388886109219059865243348025355286398606490824287224081692866909965879285318199395496024638211546498192122219385721472174220828063505792379444868085964427284979181166772967284139323377118712633412823367457848325111640247956185970827710651490487496810204677314952280506822685510020262573431813226805609808915050984621949787453611145387911823813736359781697819724321222889257625523511265559534834959338706043886025058846628379675081297785096583560332660850420705043714802953028370613 : Rat)/63090023563015295420230125443925758781200484869410601676057426387974426401571573599443698702062155468308496820704488595684881377036921048170451796201475644220694567124275699513826622247722210516548844020124122066116417269978382988648687150499263588568685271860593306554182168150079370215090829447120125363194510794559525715500084017058814604580557008749098761678335188466577593178323107515366299263313146186835673815468221063668359188221649266932286149513528763976121308339306880123490348700177904556032020166216916142065244754989850122522382218963008319076362689718687117198052421075788551500216439803826823098341661028423945878579931876314373350440465426934252988781933199393266383285090683076419465415130612400601113059618162786525922068695398584123477285299814400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1618, a6 := 24388 }
def label : String := "570.b1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1618, a6 := 24388 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 2, -1, 1, 1, -6, -1, 0, -2, 1, 1, 2, -1, -1, -1, -2, 6, 4, 1, 1, 0, -1, 2, -8,                    -1, -8, -1, 6, -2, -2, 1, -4, 1, 0, 1, -4, 2, -6, -6, -1, -4, -12, -1, -3, -1, -2, 0, 6, 1, 6, -2, 1,                    8, -4, 1, 2, 8, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1157444921970725 : Rat)/562949953421312, (6719156324067129 : Rat)/2251799813685248),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (818706726927917525173139568084447884764153125675 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (1765649187734815774103505550374542339134407047747927 : Rat)/350981163555875997621775520539360536080432941236224,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -98, a6 := 372 }
def label : String := "570.b2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -98, a6 := 372 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, 1, -1, 1, 2, -1, 1, 1, -6, -1, 0, -2, 1, 1, 2, -1, -1, -1, -2, 6, 4, 1, 1, 0, -1, 2, -8,                    -1, -8, -1, 6, -2, -2, 1, -4, 1, 0, 1, -4, 2, -6, -6, -1, -4, -12, -1, -3, -1, -2, 0, 6, 1, 6, -2, 1,                    8, -4, 1, 2, 8, 2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1157444921970725 : Rat)/562949953421312, (6719156324067129 : Rat)/2251799813685248),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (818706726927917525173139568084447884764153125675 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (1765649187734815774103505550374542339134407047747927 : Rat)/350981163555875997621775520539360536080432941236224,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -397, a6 := 2881 }
def label : String := "570.c1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -397, a6 := 2881 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, 1, 1, 1, -2, -1, 1, -1, -2, -1, 0, 2, -1, 1, -2, -1, 1, 1, 2, 2, -8, 1, 1, 0, -1, -2, 0,                    1, 0, -1, 2, 2, -2, 1, 4, -1, 0, -1, -8, -2, -6, -2, 1, 8, -8, -1, -3, -1, 2, 0, -10, 1, -2, 2, -1,                    0, -8, -1, 2, 0, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((19131810721915347 : Rat)/9007199254740992, (13823306867910639 : Rat)/4503599627370496),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (108597734871008162892515661220473710545477211335261 : Rat)/1403924654223503990487102082157442144321731764944896,            reHi := (3591306249348196691221514441820531371428766929261057 : Rat)/701962327111751995243551041078721072160865882472448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -17, a6 := 69 }
def label : String := "570.c2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -17, a6 := 69 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, -1, 1, 1, 1, -2, -1, 1, -1, -2, -1, 0, 2, -1, 1, -2, -1, 1, 1, 2, 2, -8, 1, 1, 0, -1, -2, 0,                    1, 0, -1, 2, 2, -2, 1, 4, -1, 0, -1, -8, -2, -6, -2, 1, 8, -8, -1, -3, -1, 2, 0, -10, 1, -2, 2, -1,                    0, -8, -1, 2, 0, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((19131810721915347 : Rat)/9007199254740992, (13823306867910639 : Rat)/4503599627370496),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (108597734871008162892515661220473710545477211335261 : Rat)/1403924654223503990487102082157442144321731764944896,            reHi := (3591306249348196691221514441820531371428766929261057 : Rat)/701962327111751995243551041078721072160865882472448,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1233444, a6 := -527363678 }
def label : String := "570.d1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1233444, a6 := -527363678 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, 2, -4, -1, 1, -2, -1, -1, -1, 4, 0, 0, -1, 1, -2, 1, 4, 10,                    1, 0, -1, 0, 2, -4, 1, 2, 1, 2, 1, 2, -4, -4, 0, -1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (2322545937758649660088064607324290754612139251035557068771033277762139524643470539519699228162108250004003977378815762079263365018631867323193759983946677794211564409931397214042983608082635038392432366556397933009708938414621201058303044960340093575333328203891614277213556853526125288568450894995607321878291971055559438559932573644606191056511314080095664907319541581629772336393947006360336567363444523474976921002160956021778716496169778843157667536083755328380415273619785984888440532549351656830801443008369081712696757958266054214342836460084627291407933438591155519866829841416242373867326465819613721998469953590591187475391571700875573374569468729660067023257933997473759786876970201089576544421567223277516230678623700660318660162327894413893010982673783 : Rat)/1692516820839448258267043143269053658330077762454123449218931882748620134732262381483688494319891312285796861980046410060001443047243950413453378436487320705273027240151707017484710495082279468066527730419611045251966790776478359547467092844106053717383786201625537363618208026227846194484397829756229080048696404294381355919983752539043130002623638532584518120880407461175532101916161071180039480699427603532131859989434237600723789508258861000033578479086340569202144257021183648086235071512635737395863630731073606031352541993252223453421909666907716237941274747309830156099463655132162806203771280583698306986039010013223339943402427764215381279161422184175149560292380002224537571940453107508015260905446586140085364226574209814293931537619388473247771761049600,            reHi := (46128093438309926758832018365423151545892582515570523915575629755764644014698401976158823287266750015725499720685021581809630112840530661553462445660477730690573150288583536875836622839813037228585300479050996954037722267408846602576101631937966054964638260306664119715881094333247632305643584922711279152266639659509543479186929472353864242197310432335761055218988221937741077198944911806793251295303515834351913633842685357392321081502671092366396043176313074463648957581402817134215935054895096347806679775868202368570638804458676486459706046963728775366422413511946365024869528744679575050198659747684718958307112858846292787480005828824472340185758098944018781029090643941709073261302394153377183812562102191617935788158920582988859738167058083887942769851381 : Rat)/30897872997069035140777663873065888285944624466708135989797945121171564325741098242095733162026413408868502551359873611643028372059220190103611371051492670075978184911491608838463274758094351344013690819019268574579515450280538003909135569162179479627695894147322183108648828065011390974360203788653269209813930301520146456957107044323302576112804760229737653322360379615780504903134786289290781594918556656773198255385209205692726380475313892495542000632407840005718657836086516902182790352157650378423473989005400515785340523203387446411353320491215915094262622161842741186399945022696684088912660294631409255323227363324564015193959127541457264731141581455530113676737160284017927276803403585339020990160282505599935655251861842451613354642138937645496847564800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -233764, a6 := 33569186 }
def label : String := "570.d2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5, 5, 19, 19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -233764, a6 := 33569186 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, 2, -4, -1, 1, -2, -1, -1, -1, 4, 0, 0, -1, 1, -2, 1, 4, 10,                    1, 0, -1, 0, 2, -4, 1, 2, 1, 2, 1, 2, -4, -4, 0, -1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (2322545937758649660088064607324290754612139251035557068771033277762139524643470539519699228162108250004003977378815762079263365018631867323193759983946677794211564409931397214042983608082635038392432366556397933009708938414621201058303044960340093575333328203891614277213556853526125288568450894995607321878291971055559438559932573644606191056511314080095664907319541581629772336393947006360336567363444523474976921002160956021778716496169778843157667536083755328380415273619785984888440532549351656830801443008369081712696757958266054214342836460084627291407933438591155519866829841416242373867326465819613721998469953590591187475391571700875573374569468729660067023257933997473759786876970201089576544421567223277516230678623700660318660162327894413893010982673783 : Rat)/1692516820839448258267043143269053658330077762454123449218931882748620134732262381483688494319891312285796861980046410060001443047243950413453378436487320705273027240151707017484710495082279468066527730419611045251966790776478359547467092844106053717383786201625537363618208026227846194484397829756229080048696404294381355919983752539043130002623638532584518120880407461175532101916161071180039480699427603532131859989434237600723789508258861000033578479086340569202144257021183648086235071512635737395863630731073606031352541993252223453421909666907716237941274747309830156099463655132162806203771280583698306986039010013223339943402427764215381279161422184175149560292380002224537571940453107508015260905446586140085364226574209814293931537619388473247771761049600,            reHi := (46128093438309926758832018365423151545892582515570523915575629755764644014698401976158823287266750015725499720685021581809630112840530661553462445660477730690573150288583536875836622839813037228585300479050996954037722267408846602576101631937966054964638260306664119715881094333247632305643584922711279152266639659509543479186929472353864242197310432335761055218988221937741077198944911806793251295303515834351913633842685357392321081502671092366396043176313074463648957581402817134215935054895096347806679775868202368570638804458676486459706046963728775366422413511946365024869528744679575050198659747684718958307112858846292787480005828824472340185758098944018781029090643941709073261302394153377183812562102191617935788158920582988859738167058083887942769851381 : Rat)/30897872997069035140777663873065888285944624466708135989797945121171564325741098242095733162026413408868502551359873611643028372059220190103611371051492670075978184911491608838463274758094351344013690819019268574579515450280538003909135569162179479627695894147322183108648828065011390974360203788653269209813930301520146456957107044323302576112804760229737653322360379615780504903134786289290781594918556656773198255385209205692726380475313892495542000632407840005718657836086516902182790352157650378423473989005400515785340523203387446411353320491215915094262622161842741186399945022696684088912660294631409255323227363324564015193959127541457264731141581455530113676737160284017927276803403585339020990160282505599935655251861842451613354642138937645496847564800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -78244, a6 := -7985758 }
def label : String := "570.d3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -78244, a6 := -7985758 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, 2, -4, -1, 1, -2, -1, -1, -1, 4, 0, 0, -1, 1, -2, 1, 4, 10,                    1, 0, -1, 0, 2, -4, 1, 2, 1, 2, 1, 2, -4, -4, 0, -1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (2322545937758649660088064607324290754612139251035557068771033277762139524643470539519699228162108250004003977378815762079263365018631867323193759983946677794211564409931397214042983608082635038392432366556397933009708938414621201058303044960340093575333328203891614277213556853526125288568450894995607321878291971055559438559932573644606191056511314080095664907319541581629772336393947006360336567363444523474976921002160956021778716496169778843157667536083755328380415273619785984888440532549351656830801443008369081712696757958266054214342836460084627291407933438591155519866829841416242373867326465819613721998469953590591187475391571700875573374569468729660067023257933997473759786876970201089576544421567223277516230678623700660318660162327894413893010982673783 : Rat)/1692516820839448258267043143269053658330077762454123449218931882748620134732262381483688494319891312285796861980046410060001443047243950413453378436487320705273027240151707017484710495082279468066527730419611045251966790776478359547467092844106053717383786201625537363618208026227846194484397829756229080048696404294381355919983752539043130002623638532584518120880407461175532101916161071180039480699427603532131859989434237600723789508258861000033578479086340569202144257021183648086235071512635737395863630731073606031352541993252223453421909666907716237941274747309830156099463655132162806203771280583698306986039010013223339943402427764215381279161422184175149560292380002224537571940453107508015260905446586140085364226574209814293931537619388473247771761049600,            reHi := (46128093438309926758832018365423151545892582515570523915575629755764644014698401976158823287266750015725499720685021581809630112840530661553462445660477730690573150288583536875836622839813037228585300479050996954037722267408846602576101631937966054964638260306664119715881094333247632305643584922711279152266639659509543479186929472353864242197310432335761055218988221937741077198944911806793251295303515834351913633842685357392321081502671092366396043176313074463648957581402817134215935054895096347806679775868202368570638804458676486459706046963728775366422413511946365024869528744679575050198659747684718958307112858846292787480005828824472340185758098944018781029090643941709073261302394153377183812562102191617935788158920582988859738167058083887942769851381 : Rat)/30897872997069035140777663873065888285944624466708135989797945121171564325741098242095733162026413408868502551359873611643028372059220190103611371051492670075978184911491608838463274758094351344013690819019268574579515450280538003909135569162179479627695894147322183108648828065011390974360203788653269209813930301520146456957107044323302576112804760229737653322360379615780504903134786289290781594918556656773198255385209205692726380475313892495542000632407840005718657836086516902182790352157650378423473989005400515785340523203387446411353320491215915094262622161842741186399945022696684088912660294631409255323227363324564015193959127541457264731141581455530113676737160284017927276803403585339020990160282505599935655251861842451613354642138937645496847564800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 3676, a6 := -514654 }
def label : String := "570.d4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 19,              19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 3676, a6 := -514654 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, -1, -1, 4, -1, 1, 1, 0, 1, 2, -4, -1, 1, -2, -1, -1, -1, 4, 0, 0, -1, 1, -2, 1, 4, 10,                    1, 0, -1, 0, 2, -4, 1, 2, 1, 2, 1, 2, -4, -4, 0, -1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (2322545937758649660088064607324290754612139251035557068771033277762139524643470539519699228162108250004003977378815762079263365018631867323193759983946677794211564409931397214042983608082635038392432366556397933009708938414621201058303044960340093575333328203891614277213556853526125288568450894995607321878291971055559438559932573644606191056511314080095664907319541581629772336393947006360336567363444523474976921002160956021778716496169778843157667536083755328380415273619785984888440532549351656830801443008369081712696757958266054214342836460084627291407933438591155519866829841416242373867326465819613721998469953590591187475391571700875573374569468729660067023257933997473759786876970201089576544421567223277516230678623700660318660162327894413893010982673783 : Rat)/1692516820839448258267043143269053658330077762454123449218931882748620134732262381483688494319891312285796861980046410060001443047243950413453378436487320705273027240151707017484710495082279468066527730419611045251966790776478359547467092844106053717383786201625537363618208026227846194484397829756229080048696404294381355919983752539043130002623638532584518120880407461175532101916161071180039480699427603532131859989434237600723789508258861000033578479086340569202144257021183648086235071512635737395863630731073606031352541993252223453421909666907716237941274747309830156099463655132162806203771280583698306986039010013223339943402427764215381279161422184175149560292380002224537571940453107508015260905446586140085364226574209814293931537619388473247771761049600,            reHi := (46128093438309926758832018365423151545892582515570523915575629755764644014698401976158823287266750015725499720685021581809630112840530661553462445660477730690573150288583536875836622839813037228585300479050996954037722267408846602576101631937966054964638260306664119715881094333247632305643584922711279152266639659509543479186929472353864242197310432335761055218988221937741077198944911806793251295303515834351913633842685357392321081502671092366396043176313074463648957581402817134215935054895096347806679775868202368570638804458676486459706046963728775366422413511946365024869528744679575050198659747684718958307112858846292787480005828824472340185758098944018781029090643941709073261302394153377183812562102191617935788158920582988859738167058083887942769851381 : Rat)/30897872997069035140777663873065888285944624466708135989797945121171564325741098242095733162026413408868502551359873611643028372059220190103611371051492670075978184911491608838463274758094351344013690819019268574579515450280538003909135569162179479627695894147322183108648828065011390974360203788653269209813930301520146456957107044323302576112804760229737653322360379615780504903134786289290781594918556656773198255385209205692726380475313892495542000632407840005718657836086516902182790352157650378423473989005400515785340523203387446411353320491215915094262622161842741186399945022696684088912660294631409255323227363324564015193959127541457264731141581455530113676737160284017927276803403585339020990160282505599935655251861842451613354642138937645496847564800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_d4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -968, a6 := -11662 }
def label : String := "570.e1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -968, a6 := -11662 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 1, -1, -4, -1, 1, -1, -4, 1, -6, 4, 1, 1, -6, -1, -1, 1, -4, 4, 4, -1, 1, 6, 1, -4, 6,                    -1, -8, -1, -4, 6, -4, 1, 2, 1, -6, -1, 10, 4, -8, -4, 1, -4, 12, 1, 9, -1, -6, -6, 2, -1, -4, 4, -1,                    -6, -4, 1, -2, 8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1241997747692619 : Rat)/562949953421312, (40382040052099891 : Rat)/9007199254740992),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (13997697582797874872317111762919496476532483581797 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (9167644524945767622684861366140576656418205745518333 : Rat)/1403924654223503990487102082157442144321731764944896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -448, a6 := 3506 }
def label : String := "570.e2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -448, a6 := 3506 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 1, -1, -4, -1, 1, -1, -4, 1, -6, 4, 1, 1, -6, -1, -1, 1, -4, 4, 4, -1, 1, 6, 1, -4, 6,                    -1, -8, -1, -4, 6, -4, 1, 2, 1, -6, -1, 10, 4, -8, -4, 1, -4, 12, 1, 9, -1, -6, -6, 2, -1, -4, 4, -1,                    -6, -4, 1, -2, 8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1241997747692619 : Rat)/562949953421312, (40382040052099891 : Rat)/9007199254740992),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (13997697582797874872317111762919496476532483581797 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (9167644524945767622684861366140576656418205745518333 : Rat)/1403924654223503990487102082157442144321731764944896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -68, a6 := -142 }
def label : String := "570.e3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -68, a6 := -142 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 1, -1, -4, -1, 1, -1, -4, 1, -6, 4, 1, 1, -6, -1, -1, 1, -4, 4, 4, -1, 1, 6, 1, -4, 6,                    -1, -8, -1, -4, 6, -4, 1, 2, 1, -6, -1, 10, 4, -8, -4, 1, -4, 12, 1, 9, -1, -6, -6, 2, -1, -4, 4, -1,                    -6, -4, 1, -2, 8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1241997747692619 : Rat)/562949953421312, (40382040052099891 : Rat)/9007199254740992),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (13997697582797874872317111762919496476532483581797 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (9167644524945767622684861366140576656418205745518333 : Rat)/1403924654223503990487102082157442144321731764944896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 12, a6 := -14 }
def label : String := "570.e4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 12, a6 := -14 },   conductor := 570,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 1, 1, 1, -1, -4, -1, 1, -1, -4, 1, -6, 4, 1, 1, -6, -1, -1, 1, -4, 4, 4, -1, 1, 6, 1, -4, 6,                    -1, -8, -1, -4, 6, -4, 1, 2, 1, -6, -1, 10, 4, -8, -4, 1, -4, 12, 1, 9, -1, -6, -6, 2, -1, -4, 4, -1,                    -6, -4, 1, -2, 8, -4, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   finite := ((1241997747692619 : Rat)/562949953421312, (40382040052099891 : Rat)/9007199254740992),   tail := (2740306095442047594998549924442577362060546875 : Rat)/1338886884902481070029356081159059662172061696,   box := { reLo := (13997697582797874872317111762919496476532483581797 : Rat)/87745290888968999405443880134840134020108235309056,            reHi := (9167644524945767622684861366140576656418205745518333 : Rat)/1403924654223503990487102082157442144321731764944896,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_e4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -7478, a6 := -240952 }
def label : String := "570.f1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -7478, a6 := -240952 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 2, -2, 1, 1, 0, -1, 1, 1, 2, 0, 0, -1, 1, -2, 1, 2, -6, -1,                    2, -1, 0, 0, 2, 1, 2, -1, 2, -1, 0, -2, 8, 0, 1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (17746653498759425217414344557349638340054940422532307716970737738387954971787127805012929489095064519727424690145691953122511538584497430862479194760273946188989842010891893480874595129982719995203665125941828941437223814950056366946213806510717897863410755584907974968334078678608163628643179279276413260419228642930371286109374931365499903317154770059726759284315846159388328212143288083049474619557829462160264460551053370617599172191822219648006584067338292365256120427844798792848814541855925770072762656497057715097905624379963082164177682788176098364921836161208064659371510470447257229953091703950269164487417412105783557729277429060545576493784473021723760756361092020053313379915982910643969470787207124146704470748943268386144615558440186568744022573 : Rat)/11962010451826959016948379354651911841248402813282282613162193233128751190763104236196567232685409759530972726039440035479298634169268366280918068544906182762670609721831826882873896538170480582273980185450742769872053987719914054939657595494455857385867554838297399577486964020523186594796826863590115838100631165900172844350409231251762514948821045385109428309082609220201511770474172005145482615144621237620285813157262565115263794221956597946396438494931413087773386696123312776687104278806678427573934955093070273242485684554156967251782160468918279169284793713450538593263625637900380986803197946043906022192499947086552077117289635130258329357778390033112703707602462363150571922881689347789013159179358306465325456930647248335893671948176127621175705600,            reHi := (155267889667322370170327136637732648290599130974391347534430209870879044254756546736014681243590784222785624494130547855895793400151799530710663731973379396661520690267759497279988861841841471918766004413774542861896278188205295515690167987596233694978318830210238981621077760760449831098504164543770094201062975465805725297588228968166270240281254131345826606202138656504338170068679648397354628770196675839045476251544174818355818332751187068519895029926391990474173712306050730714714832402464879617407361640911709242700667677768578851706242790331690501814638726613251724480993800092914150545028395406887700209327363520987951002737566236047020695232737111342162729010487445770358712913205337636685119300678051131179755218919575986543984200292735041390722192419777 : Rat)/96784626565731925406129337358488618707540827162266948623095305449244725884464276375066425479657650364365100326385109327063005249063550351578908092596835924732767903259341311309332696890337358391178773680481959751034788814641824618516769605145642342109054386196664259981447025890053102738501126153307627246072206763298298483639161090058010508450911078210920384448787391200650431734906525693632099839135130433585732514255411414347599359049850833984293583862490063293174471758333723676175360719824835157500707721658031580804951673727684022034169460354017796758683265935528307758095995036251982564224674581441243625559517071877292855955990437838920142833784953757914885698211522980251277428035748512960905470920188057610948272025866886285715699732693048582932634009600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1103, a6 := 13898 }
def label : String := "570.f2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1103, a6 := 13898 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 2, -2, 1, 1, 0, -1, 1, 1, 2, 0, 0, -1, 1, -2, 1, 2, -6, -1,                    2, -1, 0, 0, 2, 1, 2, -1, 2, -1, 0, -2, 8, 0, 1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (17746653498759425217414344557349638340054940422532307716970737738387954971787127805012929489095064519727424690145691953122511538584497430862479194760273946188989842010891893480874595129982719995203665125941828941437223814950056366946213806510717897863410755584907974968334078678608163628643179279276413260419228642930371286109374931365499903317154770059726759284315846159388328212143288083049474619557829462160264460551053370617599172191822219648006584067338292365256120427844798792848814541855925770072762656497057715097905624379963082164177682788176098364921836161208064659371510470447257229953091703950269164487417412105783557729277429060545576493784473021723760756361092020053313379915982910643969470787207124146704470748943268386144615558440186568744022573 : Rat)/11962010451826959016948379354651911841248402813282282613162193233128751190763104236196567232685409759530972726039440035479298634169268366280918068544906182762670609721831826882873896538170480582273980185450742769872053987719914054939657595494455857385867554838297399577486964020523186594796826863590115838100631165900172844350409231251762514948821045385109428309082609220201511770474172005145482615144621237620285813157262565115263794221956597946396438494931413087773386696123312776687104278806678427573934955093070273242485684554156967251782160468918279169284793713450538593263625637900380986803197946043906022192499947086552077117289635130258329357778390033112703707602462363150571922881689347789013159179358306465325456930647248335893671948176127621175705600,            reHi := (155267889667322370170327136637732648290599130974391347534430209870879044254756546736014681243590784222785624494130547855895793400151799530710663731973379396661520690267759497279988861841841471918766004413774542861896278188205295515690167987596233694978318830210238981621077760760449831098504164543770094201062975465805725297588228968166270240281254131345826606202138656504338170068679648397354628770196675839045476251544174818355818332751187068519895029926391990474173712306050730714714832402464879617407361640911709242700667677768578851706242790331690501814638726613251724480993800092914150545028395406887700209327363520987951002737566236047020695232737111342162729010487445770358712913205337636685119300678051131179755218919575986543984200292735041390722192419777 : Rat)/96784626565731925406129337358488618707540827162266948623095305449244725884464276375066425479657650364365100326385109327063005249063550351578908092596835924732767903259341311309332696890337358391178773680481959751034788814641824618516769605145642342109054386196664259981447025890053102738501126153307627246072206763298298483639161090058010508450911078210920384448787391200650431734906525693632099839135130433585732514255411414347599359049850833984293583862490063293174471758333723676175360719824835157500707721658031580804951673727684022034169460354017796758683265935528307758095995036251982564224674581441243625559517071877292855955990437838920142833784953757914885698211522980251277428035748512960905470920188057610948272025866886285715699732693048582932634009600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -23, a6 := 506 }
def label : String := "570.f3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -23, a6 := 506 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 2, -2, 1, 1, 0, -1, 1, 1, 2, 0, 0, -1, 1, -2, 1, 2, -6, -1,                    2, -1, 0, 0, 2, 1, 2, -1, 2, -1, 0, -2, 8, 0, 1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (17746653498759425217414344557349638340054940422532307716970737738387954971787127805012929489095064519727424690145691953122511538584497430862479194760273946188989842010891893480874595129982719995203665125941828941437223814950056366946213806510717897863410755584907974968334078678608163628643179279276413260419228642930371286109374931365499903317154770059726759284315846159388328212143288083049474619557829462160264460551053370617599172191822219648006584067338292365256120427844798792848814541855925770072762656497057715097905624379963082164177682788176098364921836161208064659371510470447257229953091703950269164487417412105783557729277429060545576493784473021723760756361092020053313379915982910643969470787207124146704470748943268386144615558440186568744022573 : Rat)/11962010451826959016948379354651911841248402813282282613162193233128751190763104236196567232685409759530972726039440035479298634169268366280918068544906182762670609721831826882873896538170480582273980185450742769872053987719914054939657595494455857385867554838297399577486964020523186594796826863590115838100631165900172844350409231251762514948821045385109428309082609220201511770474172005145482615144621237620285813157262565115263794221956597946396438494931413087773386696123312776687104278806678427573934955093070273242485684554156967251782160468918279169284793713450538593263625637900380986803197946043906022192499947086552077117289635130258329357778390033112703707602462363150571922881689347789013159179358306465325456930647248335893671948176127621175705600,            reHi := (155267889667322370170327136637732648290599130974391347534430209870879044254756546736014681243590784222785624494130547855895793400151799530710663731973379396661520690267759497279988861841841471918766004413774542861896278188205295515690167987596233694978318830210238981621077760760449831098504164543770094201062975465805725297588228968166270240281254131345826606202138656504338170068679648397354628770196675839045476251544174818355818332751187068519895029926391990474173712306050730714714832402464879617407361640911709242700667677768578851706242790331690501814638726613251724480993800092914150545028395406887700209327363520987951002737566236047020695232737111342162729010487445770358712913205337636685119300678051131179755218919575986543984200292735041390722192419777 : Rat)/96784626565731925406129337358488618707540827162266948623095305449244725884464276375066425479657650364365100326385109327063005249063550351578908092596835924732767903259341311309332696890337358391178773680481959751034788814641824618516769605145642342109054386196664259981447025890053102738501126153307627246072206763298298483639161090058010508450911078210920384448787391200650431734906525693632099839135130433585732514255411414347599359049850833984293583862490063293174471758333723676175360719824835157500707721658031580804951673727684022034169460354017796758683265935528307758095995036251982564224674581441243625559517071877292855955990437838920142833784953757914885698211522980251277428035748512960905470920188057610948272025866886285715699732693048582932634009600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 202, a6 := -13624 }
def label : String := "570.f4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 202, a6 := -13624 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, -1, 1, 1, 1, -1, 2, -1, 1, -1, 0, 1, 2, -2, 1, 1, 0, -1, 1, 1, 2, 0, 0, -1, 1, -2, 1, 2, -6, -1,                    2, -1, 0, 0, 2, 1, 2, -1, 2, -1, 0, -2, 8, 0, 1, 0, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (17746653498759425217414344557349638340054940422532307716970737738387954971787127805012929489095064519727424690145691953122511538584497430862479194760273946188989842010891893480874595129982719995203665125941828941437223814950056366946213806510717897863410755584907974968334078678608163628643179279276413260419228642930371286109374931365499903317154770059726759284315846159388328212143288083049474619557829462160264460551053370617599172191822219648006584067338292365256120427844798792848814541855925770072762656497057715097905624379963082164177682788176098364921836161208064659371510470447257229953091703950269164487417412105783557729277429060545576493784473021723760756361092020053313379915982910643969470787207124146704470748943268386144615558440186568744022573 : Rat)/11962010451826959016948379354651911841248402813282282613162193233128751190763104236196567232685409759530972726039440035479298634169268366280918068544906182762670609721831826882873896538170480582273980185450742769872053987719914054939657595494455857385867554838297399577486964020523186594796826863590115838100631165900172844350409231251762514948821045385109428309082609220201511770474172005145482615144621237620285813157262565115263794221956597946396438494931413087773386696123312776687104278806678427573934955093070273242485684554156967251782160468918279169284793713450538593263625637900380986803197946043906022192499947086552077117289635130258329357778390033112703707602462363150571922881689347789013159179358306465325456930647248335893671948176127621175705600,            reHi := (155267889667322370170327136637732648290599130974391347534430209870879044254756546736014681243590784222785624494130547855895793400151799530710663731973379396661520690267759497279988861841841471918766004413774542861896278188205295515690167987596233694978318830210238981621077760760449831098504164543770094201062975465805725297588228968166270240281254131345826606202138656504338170068679648397354628770196675839045476251544174818355818332751187068519895029926391990474173712306050730714714832402464879617407361640911709242700667677768578851706242790331690501814638726613251724480993800092914150545028395406887700209327363520987951002737566236047020695232737111342162729010487445770358712913205337636685119300678051131179755218919575986543984200292735041390722192419777 : Rat)/96784626565731925406129337358488618707540827162266948623095305449244725884464276375066425479657650364365100326385109327063005249063550351578908092596835924732767903259341311309332696890337358391178773680481959751034788814641824618516769605145642342109054386196664259981447025890053102738501126153307627246072206763298298483639161090058010508450911078210920384448787391200650431734906525693632099839135130433585732514255411414347599359049850833984293583862490063293174471758333723676175360719824835157500707721658031580804951673727684022034169460354017796758683265935528307758095995036251982564224674581441243625559517071877292855955990437838920142833784953757914885698211522980251277428035748512960905470920188057610948272025866886285715699732693048582932634009600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_f4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -621, a6 := -6207 }
def label : String := "570.g1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -621, a6 := -6207 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, -1, -1, 0, 1, 1, -1, 4, -1, 2, 0, 1, 1, 2, 1, -1, -1, 0, 4, 4, -1, 1, 2, -1, 0, 6, 1, 4,                    1, -4, 2, 0, 1, -6, -1, -2, -1, 10, 0, -4, 4, -1, 4, -12, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (47937271560055774301107950284933505411571185279186985964174794664079672523239375416699881360486897154594569134660855028652272843542558513844798304633356344374498235645314531507389010895257543418099352448320439748030202671526969535993280805288581544768756140899217912247490349723355677841035015152442684108857400929248946657299815452708757757370709416500720258671389976093407593301421152282545936222992624704006311158378032987980449133402267102480029632973231226966383474606544065931352343636284861576679464617611570832953870953222907276728603450982648107745539008536806476261150631537616236165053117289159041830954367703476643358878979252441692964515504024919836039721375603668476395195521432505270401660950760966784475894187529706782477274309048526478249153991790709691 : Rat)/25875922521345273307354384307072979065832370294296833915994410165696368314130283972000408424802921192787670624606083822601613490496142904185338158127776653508230586030542219043456604639030066627573104454539479207402890568872562508630054401297626537540099345073109054731008143536982553126789395906097411416818777213025771189885820173282265247107254167445523220682642903726792038573566520239516663597853148957486459932029894667684551318483479292194656219321905868767920610891735721833505827302601537711481132842458395177695616813082265671680251335806113840581176754597478673353658357272655561622445914096683829873619844116086449802486140630985509412730653748675462904398990030779723969487356478730342897886691426886017970799166249337159417465603498476431214755156538163200,            reHi := (18193761168426406431955940738064990366468486605258520729764708145901483724728661939307218820403277233439197372651367284137403004463533823917771793747794504569732421165839445366416622647793192440553279673955915307598608283856213926103247814131119887538753764707630470682262145655418543230659397003368048820931976060651666376400100978488736811963377307318993071591592697553262537669630115292335395467433682847684294546431953047985007073431058885826157696018427842263324895658253974733235601724748688972536588120844394184717816951621090345133425584454249613470594704023660450263864888119150440538019055175771258790244639390737550461322285535419136602262551641822735059548857684587271996599961737053662638414101586574788443015825403623859778320609198492377823674580665432477 : Rat)/9220156300709235316413631189876578747595442288772435073515249599271119744115388541747271967458512149154227463940098833340804806958395747468338883930587083433967220309733434371806376365631403051204209633226710981948156409598269399626800993565820950157966433301912421800704051145361599390005416932057698320935426363262056400993797992778738191497987117135761147599562413971615553974489219855459960592338478364161842044746284306876104492792963885724532675850334275078224585490158705480904375245754570908688679518577129316190392197764945239334342429999879644345017004511745274413372518108647384026388773988473548575657645604582528090541038615638514848214370875964820115360559666139901644300092538398168159017096945212259276951427054361516574039467913250222616751837387161600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -51, a6 := -51 }
def label : String := "570.g2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -51, a6 := -51 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, -1, -1, 0, 1, 1, -1, 4, -1, 2, 0, 1, 1, 2, 1, -1, -1, 0, 4, 4, -1, 1, 2, -1, 0, 6, 1, 4,                    1, -4, 2, 0, 1, -6, -1, -2, -1, 10, 0, -4, 4, -1, 4, -12, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (47937271560055774301107950284933505411571185279186985964174794664079672523239375416699881360486897154594569134660855028652272843542558513844798304633356344374498235645314531507389010895257543418099352448320439748030202671526969535993280805288581544768756140899217912247490349723355677841035015152442684108857400929248946657299815452708757757370709416500720258671389976093407593301421152282545936222992624704006311158378032987980449133402267102480029632973231226966383474606544065931352343636284861576679464617611570832953870953222907276728603450982648107745539008536806476261150631537616236165053117289159041830954367703476643358878979252441692964515504024919836039721375603668476395195521432505270401660950760966784475894187529706782477274309048526478249153991790709691 : Rat)/25875922521345273307354384307072979065832370294296833915994410165696368314130283972000408424802921192787670624606083822601613490496142904185338158127776653508230586030542219043456604639030066627573104454539479207402890568872562508630054401297626537540099345073109054731008143536982553126789395906097411416818777213025771189885820173282265247107254167445523220682642903726792038573566520239516663597853148957486459932029894667684551318483479292194656219321905868767920610891735721833505827302601537711481132842458395177695616813082265671680251335806113840581176754597478673353658357272655561622445914096683829873619844116086449802486140630985509412730653748675462904398990030779723969487356478730342897886691426886017970799166249337159417465603498476431214755156538163200,            reHi := (18193761168426406431955940738064990366468486605258520729764708145901483724728661939307218820403277233439197372651367284137403004463533823917771793747794504569732421165839445366416622647793192440553279673955915307598608283856213926103247814131119887538753764707630470682262145655418543230659397003368048820931976060651666376400100978488736811963377307318993071591592697553262537669630115292335395467433682847684294546431953047985007073431058885826157696018427842263324895658253974733235601724748688972536588120844394184717816951621090345133425584454249613470594704023660450263864888119150440538019055175771258790244639390737550461322285535419136602262551641822735059548857684587271996599961737053662638414101586574788443015825403623859778320609198492377823674580665432477 : Rat)/9220156300709235316413631189876578747595442288772435073515249599271119744115388541747271967458512149154227463940098833340804806958395747468338883930587083433967220309733434371806376365631403051204209633226710981948156409598269399626800993565820950157966433301912421800704051145361599390005416932057698320935426363262056400993797992778738191497987117135761147599562413971615553974489219855459960592338478364161842044746284306876104492792963885724532675850334275078224585490158705480904375245754570908688679518577129316190392197764945239334342429999879644345017004511745274413372518108647384026388773988473548575657645604582528090541038615638514848214370875964820115360559666139901644300092538398168159017096945212259276951427054361516574039467913250222616751837387161600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -31, a6 := 53 }
def label : String := "570.g3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -31, a6 := 53 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, -1, -1, 0, 1, 1, -1, 4, -1, 2, 0, 1, 1, 2, 1, -1, -1, 0, 4, 4, -1, 1, 2, -1, 0, 6, 1, 4,                    1, -4, 2, 0, 1, -6, -1, -2, -1, 10, 0, -4, 4, -1, 4, -12, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (47937271560055774301107950284933505411571185279186985964174794664079672523239375416699881360486897154594569134660855028652272843542558513844798304633356344374498235645314531507389010895257543418099352448320439748030202671526969535993280805288581544768756140899217912247490349723355677841035015152442684108857400929248946657299815452708757757370709416500720258671389976093407593301421152282545936222992624704006311158378032987980449133402267102480029632973231226966383474606544065931352343636284861576679464617611570832953870953222907276728603450982648107745539008536806476261150631537616236165053117289159041830954367703476643358878979252441692964515504024919836039721375603668476395195521432505270401660950760966784475894187529706782477274309048526478249153991790709691 : Rat)/25875922521345273307354384307072979065832370294296833915994410165696368314130283972000408424802921192787670624606083822601613490496142904185338158127776653508230586030542219043456604639030066627573104454539479207402890568872562508630054401297626537540099345073109054731008143536982553126789395906097411416818777213025771189885820173282265247107254167445523220682642903726792038573566520239516663597853148957486459932029894667684551318483479292194656219321905868767920610891735721833505827302601537711481132842458395177695616813082265671680251335806113840581176754597478673353658357272655561622445914096683829873619844116086449802486140630985509412730653748675462904398990030779723969487356478730342897886691426886017970799166249337159417465603498476431214755156538163200,            reHi := (18193761168426406431955940738064990366468486605258520729764708145901483724728661939307218820403277233439197372651367284137403004463533823917771793747794504569732421165839445366416622647793192440553279673955915307598608283856213926103247814131119887538753764707630470682262145655418543230659397003368048820931976060651666376400100978488736811963377307318993071591592697553262537669630115292335395467433682847684294546431953047985007073431058885826157696018427842263324895658253974733235601724748688972536588120844394184717816951621090345133425584454249613470594704023660450263864888119150440538019055175771258790244639390737550461322285535419136602262551641822735059548857684587271996599961737053662638414101586574788443015825403623859778320609198492377823674580665432477 : Rat)/9220156300709235316413631189876578747595442288772435073515249599271119744115388541747271967458512149154227463940098833340804806958395747468338883930587083433967220309733434371806376365631403051204209633226710981948156409598269399626800993565820950157966433301912421800704051145361599390005416932057698320935426363262056400993797992778738191497987117135761147599562413971615553974489219855459960592338478364161842044746284306876104492792963885724532675850334275078224585490158705480904375245754570908688679518577129316190392197764945239334342429999879644345017004511745274413372518108647384026388773988473548575657645604582528090541038615638514848214370875964820115360559666139901644300092538398168159017096945212259276951427054361516574039467913250222616751837387161600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 199, a6 := -151 }
def label : String := "570.g4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 5, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 199, a6 := -151 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 48,   coefficients := [1, 1, -1, 1, -1, -1, 0, 1, 1, -1, 4, -1, 2, 0, 1, 1, 2, 1, -1, -1, 0, 4, 4, -1, 1, 2, -1, 0, 6, 1, 4,                    1, -4, 2, 0, 1, -6, -1, -2, -1, 10, 0, -4, 4, -1, 4, -12, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/45050411267590468004701551095572589553708324313274767397277820292359480993364482576768919057284284943154025896015215273436771054210595485475635320760403663544564955171196033830614430046777066499478317241128868354663606017210861707709848773164319206801120628333668767827839051014116134431020909005141195134547146844553894527258861618498305300626385633688388770583118761774603189042365773487036936692004975944337767868024715432126028789085610010154962577892595473449857402113259816501975724616539604284244176462077281887741213386890714498641491989337795985949664979619435226789430846955655328073828068716858698887835420194281337264352846756916517575963763826506403177507211985173337998014807228501229688952751561270936165923851416056250423394965355908562944,   box := { reLo := (47937271560055774301107950284933505411571185279186985964174794664079672523239375416699881360486897154594569134660855028652272843542558513844798304633356344374498235645314531507389010895257543418099352448320439748030202671526969535993280805288581544768756140899217912247490349723355677841035015152442684108857400929248946657299815452708757757370709416500720258671389976093407593301421152282545936222992624704006311158378032987980449133402267102480029632973231226966383474606544065931352343636284861576679464617611570832953870953222907276728603450982648107745539008536806476261150631537616236165053117289159041830954367703476643358878979252441692964515504024919836039721375603668476395195521432505270401660950760966784475894187529706782477274309048526478249153991790709691 : Rat)/25875922521345273307354384307072979065832370294296833915994410165696368314130283972000408424802921192787670624606083822601613490496142904185338158127776653508230586030542219043456604639030066627573104454539479207402890568872562508630054401297626537540099345073109054731008143536982553126789395906097411416818777213025771189885820173282265247107254167445523220682642903726792038573566520239516663597853148957486459932029894667684551318483479292194656219321905868767920610891735721833505827302601537711481132842458395177695616813082265671680251335806113840581176754597478673353658357272655561622445914096683829873619844116086449802486140630985509412730653748675462904398990030779723969487356478730342897886691426886017970799166249337159417465603498476431214755156538163200,            reHi := (18193761168426406431955940738064990366468486605258520729764708145901483724728661939307218820403277233439197372651367284137403004463533823917771793747794504569732421165839445366416622647793192440553279673955915307598608283856213926103247814131119887538753764707630470682262145655418543230659397003368048820931976060651666376400100978488736811963377307318993071591592697553262537669630115292335395467433682847684294546431953047985007073431058885826157696018427842263324895658253974733235601724748688972536588120844394184717816951621090345133425584454249613470594704023660450263864888119150440538019055175771258790244639390737550461322285535419136602262551641822735059548857684587271996599961737053662638414101586574788443015825403623859778320609198492377823674580665432477 : Rat)/9220156300709235316413631189876578747595442288772435073515249599271119744115388541747271967458512149154227463940098833340804806958395747468338883930587083433967220309733434371806376365631403051204209633226710981948156409598269399626800993565820950157966433301912421800704051145361599390005416932057698320935426363262056400993797992778738191497987117135761147599562413971615553974489219855459960592338478364161842044746284306876104492792963885724532675850334275078224585490158705480904375245754570908688679518577129316190392197764945239334342429999879644345017004511745274413372518108647384026388773988473548575657645604582528090541038615638514848214370875964820115360559666139901644300092538398168159017096945212259276951427054361516574039467913250222616751837387161600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (2718283044366125296972305959552579311601934039205744138516496961211104169345570224291315821160774311432749753426170250485562007485770531448607401214361228861297164168607551310176854416756249301473289128565247965711473038550963179313596521956020727262988983459281633458416448516958652403669635327204256599919650862618074968775758341548053107161576869998078219722574814769993245282072000469381329180889992062720177959902265617826695106006809499689381773734621714534868548217126930725093866705772263221304831828852838171751383788491107220615710568212110221883827516581691011752508648168931732103323461660358377729837417481355537854192930373043799200810537555536875763345197193555097070417676619610916047517984161648304495073043826008342471568349916184655847 : Rat)/90100822535180936009403102191145179107416648626549534794555640584718961986728965153537838114568569886308051792030430546873542108421190970951270641520807327089129910342392067661228860093554132998956634482257736709327212034421723415419697546328638413602241256667337535655678102028232268862041818010282390269094293689107789054517723236996610601252771267376777541166237523549206378084731546974073873384009951888675535736049430864252057578171220020309925155785190946899714804226519633003951449233079208568488352924154563775482426773781428997282983978675591971899329959238870453578861693911310656147656137433717397775670840388562674528705693513833035151927527653012806355014423970346675996029614457002459377905503122541872331847702832112500846789930711817125888, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 48 = (List.range 48).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 48

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_g4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -30, a6 := -75 }
def label : String := "570.h1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -30, a6 := -75 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, -2, 1, 1, 1, 0, -1, 6, -2, -1, 1, 8, 1, 1, 1, 2, 0, -4, -1, 1, 6, -1, -2, 2, -1,                    -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (144017707646567472098647864360621485097597863136834315289723871079847683562182708499361992254240031263474610625237806038827420982083373166202602180633507759179050912977548382829630760313483866391914197548486817882653677008395278412580076679755308225768979402216283597029230868332804845092944106624782247351171166794665253793085672902134423242082607900952959555365351957267626221085903407067772871409818563040551521317306919183888344830102661513236066393363985658383799605337482373732690285525202434520052818913444683483 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1767246126695911618520085872525044582438198724210202627241216260925823951838398318860766914326830427797702335223129774259885875875650692845759144886141942406641652309908700981453569762394108764008474078155090728481264915624849743500628744521128752535097838670412000669240393862822994557185415474807186981922338811980391559755000393799868768680939117798629531808999423729056006332504581817090416910248991553868374438424380363458077412812811267798058495086155196050087389689580870067946263952327486281509807759639883327 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := -3 }
def label : String := "570.h2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := -3 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, -2, 1, 1, 1, 0, -1, 6, -2, -1, 1, 8, 1, 1, 1, 2, 0, -4, -1, 1, 6, -1, -2, 2, -1,                    -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (144017707646567472098647864360621485097597863136834315289723871079847683562182708499361992254240031263474610625237806038827420982083373166202602180633507759179050912977548382829630760313483866391914197548486817882653677008395278412580076679755308225768979402216283597029230868332804845092944106624782247351171166794665253793085672902134423242082607900952959555365351957267626221085903407067772871409818563040551521317306919183888344830102661513236066393363985658383799605337482373732690285525202434520052818913444683483 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1767246126695911618520085872525044582438198724210202627241216260925823951838398318860766914326830427797702335223129774259885875875650692845759144886141942406641652309908700981453569762394108764008474078155090728481264915624849743500628744521128752535097838670412000669240393862822994557185415474807186981922338811980391559755000393799868768680939117798629531808999423729056006332504581817090416910248991553868374438424380363458077412812811267798058495086155196050087389689580870067946263952327486281509807759639883327 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_h2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -492480, a6 := 132819117 }
def label : String := "570.i1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -492480, a6 := 132819117 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 4, 1, 1, 1, 0, -1, -6, 4, -1, 1, 2, 1, 1, 1, -4, 0, 8, -1, 1, -6, -1, 4, 2, -1,                    -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (936851369464764953717411841263103748995789409153858812417505167638399542426492730036851057333997826436695260986985981946928775822461534022666181287534535679173755921166915894469856462520852473613556129403080375085286902055332646655028021402323062143987026446646417142286408685211860778758579835693886640463378055458217674331421532542989737732466587086241892372100649227221307936934637949396602857210408126294303808116568004652364022841560707152797839719332255131754123848645414685051107059516836093487442140038139928283 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1865235702992809154112187452273651685160759737632991288264426752610302145305961960767749641349987564220422081561485326600507101019143509774861870100606461578955029516710691218418358996971624967461716644071474782824454661452913066408894731258333471924265807869165542843110309851716943800202702145235895350604200072866584377253124580390957339271636593785571635723301555773114394823444479729582359885919914940994361075432203706659762239041132083886774806729474982362138851250786659377660219821980113661370498772872113727 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -31160, a6 := 2011565 }
def label : String := "570.i2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -31160, a6 := 2011565 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 4, 1, 1, 1, 0, -1, -6, 4, -1, 1, 2, 1, 1, 1, -4, 0, 8, -1, 1, -6, -1, 4, 2, -1,                    -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (936851369464764953717411841263103748995789409153858812417505167638399542426492730036851057333997826436695260986985981946928775822461534022666181287534535679173755921166915894469856462520852473613556129403080375085286902055332646655028021402323062143987026446646417142286408685211860778758579835693886640463378055458217674331421532542989737732466587086241892372100649227221307936934637949396602857210408126294303808116568004652364022841560707152797839719332255131754123848645414685051107059516836093487442140038139928283 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1865235702992809154112187452273651685160759737632991288264426752610302145305961960767749641349987564220422081561485326600507101019143509774861870100606461578955029516710691218418358996971624967461716644071474782824454661452913066408894731258333471924265807869165542843110309851716943800202702145235895350604200072866584377253124580390957339271636593785571635723301555773114394823444479729582359885919914940994361075432203706659762239041132083886774806729474982362138851250786659377660219821980113661370498772872113727 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -30780, a6 := 2065677 }
def label : String := "570.i3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -30780, a6 := 2065677 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 4, 1, 1, 1, 0, -1, -6, 4, -1, 1, 2, 1, 1, 1, -4, 0, 8, -1, 1, -6, -1, 4, 2, -1,                    -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (936851369464764953717411841263103748995789409153858812417505167638399542426492730036851057333997826436695260986985981946928775822461534022666181287534535679173755921166915894469856462520852473613556129403080375085286902055332646655028021402323062143987026446646417142286408685211860778758579835693886640463378055458217674331421532542989737732466587086241892372100649227221307936934637949396602857210408126294303808116568004652364022841560707152797839719332255131754123848645414685051107059516836093487442140038139928283 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1865235702992809154112187452273651685160759737632991288264426752610302145305961960767749641349987564220422081561485326600507101019143509774861870100606461578955029516710691218418358996971624967461716644071474782824454661452913066408894731258333471924265807869165542843110309851716943800202702145235895350604200072866584377253124580390957339271636593785571635723301555773114394823444479729582359885919914940994361075432203706659762239041132083886774806729474982362138851250786659377660219821980113661370498772872113727 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1900, a6 := 32525 }
def label : String := "570.i4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1900, a6 := 32525 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, -1, 1, 1, -1, 4, 1, 1, 1, 0, -1, -6, 4, -1, 1, 2, 1, 1, 1, -4, 0, 8, -1, 1, -6, -1, 4, 2, -1,                    -8, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (936851369464764953717411841263103748995789409153858812417505167638399542426492730036851057333997826436695260986985981946928775822461534022666181287534535679173755921166915894469856462520852473613556129403080375085286902055332646655028021402323062143987026446646417142286408685211860778758579835693886640463378055458217674331421532542989737732466587086241892372100649227221307936934637949396602857210408126294303808116568004652364022841560707152797839719332255131754123848645414685051107059516836093487442140038139928283 : Rat)/3536777960332180166823232120116244187428768758563027198077272589646578622606145723172445980526617328729435615786863005737406050950197873405785036775060223228973468698527162244164457908549631880684679998951439261103676260006203482205266263707441668798597978317249618049336487691553170705827668363757970914496133608250449090595811588849730241527955501944886140454450995553769705875801425317804296670077733981049159169586346455856548509976530600565664792063989759821357454738205061573732017653326429241972143607644789145600,            reHi := (1865235702992809154112187452273651685160759737632991288264426752610302145305961960767749641349987564220422081561485326600507101019143509774861870100606461578955029516710691218418358996971624967461716644071474782824454661452913066408894731258333471924265807869165542843110309851716943800202702145235895350604200072866584377253124580390957339271636593785571635723301555773114394823444479729582359885919914940994361075432203706659762239041132083886774806729474982362138851250786659377660219821980113661370498772872113727 : Rat)/437124948749496992562505514783864069636481122056980249422478382109328713707347141660171299039255633262814932120487332312125330731701628155454830895446820322453771931594013378341917922203637607302518847973234366716558677543715669534701058423858814583932514932301275250196080545242018379165451534267454074217789347206828462562824321944102118592010320349139307929112717285103164735607641245557322539868710169453610081520992022723587753056053714073126287487824713857540162493907435616577928272565372542574730392738201600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_i4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -23326, a6 := -1373170 }
def label : String := "570.j1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -23326, a6 := -1373170 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, -4, 1, 6, 2, -1, 1, 4, 1, 1, -1, 2, -4, 0, 1, 1, 6, 1, 2, -10, -1,                    -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (4556801485537058895029372519172779022930257554531964500130683413305386288336697535829948329681642747686994280914921648345562640624079235004983120243971205126840984808408448209756953564201624744279412043744578575161343159618732142768020182333909830223303746494489651990717179762460877895694572064628600398417046470687237970312594438420441160853678275208989587733584907249041831342134498149549794110060259530507179891841023170054657924099962555060291486786573869710456191383833562927229518681800022256556340883891722931 : Rat)/6480852501025151063644103501795549902001741853105663697959353404316569190182842404613844042277659606200864863177660013844988599109141530478699884145537640432901575159719937478895391803106105395224301180820561697841152567061175796144915692284167642309608156170205863492037541996849055099800824921095732143837659452066456771040134512301687932168500836480717565383801591053051268471400246292828129830227398599290479904289490423858409730091926804301568001449922931540051974366192849793611893084556175522521002779292467200,            reHi := (256741875253337385517123825916662481504211790776040545438799213906017796448284057831109502424902871148274936336046572022768510800817435587280768099418990958086227268571169685629703728529116316404674984970633358083411163957401227271357118855199116081146796529648373965928835076969579345027408298821107188206322929367345993818441406155392168663059389672542663121290204392180930459857124059390207604733087367002337331660634695331041263625700442411965150914206110825891653428124328726205933128461359741381299834431158764639 : Rat)/54564596863469820245519710128020597562014665279373491134431975436342727697991027987232686936595779265110507396431266568178774979596320627578731282644687875902816487635061409096506363245506242198501374457876342036662607096869899444962032118908637246542184798723346141013606401973471076808000493690515680307794487644817587652950809926152920977289636074886041437586200492414399389388240783304133609215785517239187588871598612923453062566257835352345459625110641455869469848696010767617184003066747155205741345980494643200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1456, a6 := -21604 }
def label : String := "570.j2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1456, a6 := -21604 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, -4, 1, 6, 2, -1, 1, 4, 1, 1, -1, 2, -4, 0, 1, 1, 6, 1, 2, -10, -1,                    -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (4556801485537058895029372519172779022930257554531964500130683413305386288336697535829948329681642747686994280914921648345562640624079235004983120243971205126840984808408448209756953564201624744279412043744578575161343159618732142768020182333909830223303746494489651990717179762460877895694572064628600398417046470687237970312594438420441160853678275208989587733584907249041831342134498149549794110060259530507179891841023170054657924099962555060291486786573869710456191383833562927229518681800022256556340883891722931 : Rat)/6480852501025151063644103501795549902001741853105663697959353404316569190182842404613844042277659606200864863177660013844988599109141530478699884145537640432901575159719937478895391803106105395224301180820561697841152567061175796144915692284167642309608156170205863492037541996849055099800824921095732143837659452066456771040134512301687932168500836480717565383801591053051268471400246292828129830227398599290479904289490423858409730091926804301568001449922931540051974366192849793611893084556175522521002779292467200,            reHi := (256741875253337385517123825916662481504211790776040545438799213906017796448284057831109502424902871148274936336046572022768510800817435587280768099418990958086227268571169685629703728529116316404674984970633358083411163957401227271357118855199116081146796529648373965928835076969579345027408298821107188206322929367345993818441406155392168663059389672542663121290204392180930459857124059390207604733087367002337331660634695331041263625700442411965150914206110825891653428124328726205933128461359741381299834431158764639 : Rat)/54564596863469820245519710128020597562014665279373491134431975436342727697991027987232686936595779265110507396431266568178774979596320627578731282644687875902816487635061409096506363245506242198501374457876342036662607096869899444962032118908637246542184798723346141013606401973471076808000493690515680307794487644817587652950809926152920977289636074886041437586200492414399389388240783304133609215785517239187588871598612923453062566257835352345459625110641455869469848696010767617184003066747155205741345980494643200,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_j2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -463231, a6 := 77449961 }
def label : String := "570.k1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -463231, a6 := 77449961 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 6, 1, -4, 2, -1, 1, -6, 1, 1, -1, 2, 6, 0, 1, 1, -4, 1, 2, 0, -1, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (155220766123094792280419674394652980658964159512567397588313701052587034024880243176216765560342144901019679630094453458784306107659067814247790087690137555753465699131861374597932672279047942840383473730671303567860238850540452481199731655158020301438467378417352512822086867572231880384823043538506831279503968325655979074434511494170603328168192315226604019480569262093370526921911182569074351007826814679012532438435017929595656553557101738190867826350052483844914447696774915557722895535056921878426568849867501 : Rat)/209059758097585518182067854896630642000056188809860119289011400139244167425252980793994969105730955038737576231537419801451245132552952596087093036952827110738760489023223789641786832358261464362074231639372957994875889260037928907900506202715085235793811489361479467485081999898356616122607255519217165930247079098917960356133371364570578457048414080023147270445212614614557047464524073962197736458948341912596125944822271737368055809416993687147354885481384888388773366651382251406835260792134694274871057396531200,            reHi := (276743591856215398168833278813332792780124813470873235854739148995073357160122086159250487146823058664228347872815952731186154811897385908570267603380533000781660420491887915802670432520382674480009106677616267576772298227394857986486750405225789437633480400158181968841833285008863313508265288758461727256356773776973341815101938458376253730462042458347456243158453785584054168857011432684705398681835761013053083353124934723070847907180100622720604119398531563804471807853062445004295132016988538758302331836659306421 : Rat)/58327672509226359572796931516159949118015676677950973281634180638849122711645581641524596380498936455807783768598940124604897391982273774308298957309838763896114176437479437310058526227954948557018710627385055280570373103550582165304241230557508780786473405531852771428337877971641495898207424289861589294538935068598110939361210610715191389516507528326458088454214319477461416242602216635453168472046587393614319138605413814725687570827341238714112013049306383860467769295735648142507037761005579702689025013632204800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -414991, a6 := 102863225 }
def label : String := "570.k2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -414991, a6 := 102863225 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 6, 1, -4, 2, -1, 1, -6, 1, 1, -1, 2, 6, 0, 1, 1, -4, 1, 2, 0, -1, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (155220766123094792280419674394652980658964159512567397588313701052587034024880243176216765560342144901019679630094453458784306107659067814247790087690137555753465699131861374597932672279047942840383473730671303567860238850540452481199731655158020301438467378417352512822086867572231880384823043538506831279503968325655979074434511494170603328168192315226604019480569262093370526921911182569074351007826814679012532438435017929595656553557101738190867826350052483844914447696774915557722895535056921878426568849867501 : Rat)/209059758097585518182067854896630642000056188809860119289011400139244167425252980793994969105730955038737576231537419801451245132552952596087093036952827110738760489023223789641786832358261464362074231639372957994875889260037928907900506202715085235793811489361479467485081999898356616122607255519217165930247079098917960356133371364570578457048414080023147270445212614614557047464524073962197736458948341912596125944822271737368055809416993687147354885481384888388773366651382251406835260792134694274871057396531200,            reHi := (276743591856215398168833278813332792780124813470873235854739148995073357160122086159250487146823058664228347872815952731186154811897385908570267603380533000781660420491887915802670432520382674480009106677616267576772298227394857986486750405225789437633480400158181968841833285008863313508265288758461727256356773776973341815101938458376253730462042458347456243158453785584054168857011432684705398681835761013053083353124934723070847907180100622720604119398531563804471807853062445004295132016988538758302331836659306421 : Rat)/58327672509226359572796931516159949118015676677950973281634180638849122711645581641524596380498936455807783768598940124604897391982273774308298957309838763896114176437479437310058526227954948557018710627385055280570373103550582165304241230557508780786473405531852771428337877971641495898207424289861589294538935068598110939361210610715191389516507528326458088454214319477461416242602216635453168472046587393614319138605413814725687570827341238714112013049306383860467769295735648142507037761005579702689025013632204800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -25871, a6 := 1614201 }
def label : String := "570.k3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -25871, a6 := 1614201 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 6, 1, -4, 2, -1, 1, -6, 1, 1, -1, 2, 6, 0, 1, 1, -4, 1, 2, 0, -1, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (155220766123094792280419674394652980658964159512567397588313701052587034024880243176216765560342144901019679630094453458784306107659067814247790087690137555753465699131861374597932672279047942840383473730671303567860238850540452481199731655158020301438467378417352512822086867572231880384823043538506831279503968325655979074434511494170603328168192315226604019480569262093370526921911182569074351007826814679012532438435017929595656553557101738190867826350052483844914447696774915557722895535056921878426568849867501 : Rat)/209059758097585518182067854896630642000056188809860119289011400139244167425252980793994969105730955038737576231537419801451245132552952596087093036952827110738760489023223789641786832358261464362074231639372957994875889260037928907900506202715085235793811489361479467485081999898356616122607255519217165930247079098917960356133371364570578457048414080023147270445212614614557047464524073962197736458948341912596125944822271737368055809416993687147354885481384888388773366651382251406835260792134694274871057396531200,            reHi := (276743591856215398168833278813332792780124813470873235854739148995073357160122086159250487146823058664228347872815952731186154811897385908570267603380533000781660420491887915802670432520382674480009106677616267576772298227394857986486750405225789437633480400158181968841833285008863313508265288758461727256356773776973341815101938458376253730462042458347456243158453785584054168857011432684705398681835761013053083353124934723070847907180100622720604119398531563804471807853062445004295132016988538758302331836659306421 : Rat)/58327672509226359572796931516159949118015676677950973281634180638849122711645581641524596380498936455807783768598940124604897391982273774308298957309838763896114176437479437310058526227954948557018710627385055280570373103550582165304241230557508780786473405531852771428337877971641495898207424289861589294538935068598110939361210610715191389516507528326458088454214319477461416242602216635453168472046587393614319138605413814725687570827341238714112013049306383860467769295735648142507037761005579702689025013632204800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 85489, a6 := 8420985 }
def label : String := "570.k4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 85489, a6 := 8420985 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, -1, 1, 2, 1, 1, -1, 6, 1, -4, 2, -1, 1, -6, 1, 1, -1, 2, 6, 0, 1, 1, -4, 1, 2, 0, -1, 8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (155220766123094792280419674394652980658964159512567397588313701052587034024880243176216765560342144901019679630094453458784306107659067814247790087690137555753465699131861374597932672279047942840383473730671303567860238850540452481199731655158020301438467378417352512822086867572231880384823043538506831279503968325655979074434511494170603328168192315226604019480569262093370526921911182569074351007826814679012532438435017929595656553557101738190867826350052483844914447696774915557722895535056921878426568849867501 : Rat)/209059758097585518182067854896630642000056188809860119289011400139244167425252980793994969105730955038737576231537419801451245132552952596087093036952827110738760489023223789641786832358261464362074231639372957994875889260037928907900506202715085235793811489361479467485081999898356616122607255519217165930247079098917960356133371364570578457048414080023147270445212614614557047464524073962197736458948341912596125944822271737368055809416993687147354885481384888388773366651382251406835260792134694274871057396531200,            reHi := (276743591856215398168833278813332792780124813470873235854739148995073357160122086159250487146823058664228347872815952731186154811897385908570267603380533000781660420491887915802670432520382674480009106677616267576772298227394857986486750405225789437633480400158181968841833285008863313508265288758461727256356773776973341815101938458376253730462042458347456243158453785584054168857011432684705398681835761013053083353124934723070847907180100622720604119398531563804471807853062445004295132016988538758302331836659306421 : Rat)/58327672509226359572796931516159949118015676677950973281634180638849122711645581641524596380498936455807783768598940124604897391982273774308298957309838763896114176437479437310058526227954948557018710627385055280570373103550582165304241230557508780786473405531852771428337877971641495898207424289861589294538935068598110939361210610715191389516507528326458088454214319477461416242602216635453168472046587393614319138605413814725687570827341238714112013049306383860467769295735648142507037761005579702689025013632204800,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_k4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -52823445, a6 := -147775056075 }
def label : String := "570.l1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 5, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -52823445, a6 := -147775056075 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, -2, 1, 1, 1, 2, 1, 4, -2, 1, 1, -2, 1, -1, 1, -2, 2, 4, 1, 1, 4, 1, -2, 0, 1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (39696163971095466848092169580008049405932033061761698674150040143025388249780526620649127931693610844286613902742717253489796627275739593572682075042842091455629609536251582598746908034249863884236645398612609013154690316921588478286253235608897224203833281506260409410254147166170882466547948758790175560881712622596690087266854424608035557687212305371169318648148448786642466280196538519738745118036241814315431284632737243019826271927923363755014569087658981024556624567902363590806767954440704219332272958880653831 : Rat)/49686535841192824821271460180432549248680020873810088351021709433093697124735125102039470990795390314206630617695393439478245926503418400336699111782455243318912076224519520671531337157146808030052975719624306350115503014135681103777686974178618591040329197304911620105621155309176089098472991061733946436088722465842835244641031260979607479958506413018834667942478864740059724947401888245015662031743389261227012599552759916247807930704772166312021344449409141807065136807478515084357846981597345672661021307908915200,            reHi := (207769270441955880643659328932186800376731447756074411692779579671665110878989937984806716804741959646855821366565691044870539080593007087493885821691365483336545559971490478537968491990215669049819483148802238615085786693561786659474593567969384844314277908942131477922845715374085968679904438659815253034015998885944392690346630899655602559313726899716138472313084655646809080061728224039336094408630866729260922559050643618246136461805155128442924958471524315130304949506116821554032099328715894565255533025089118813 : Rat)/43275369926200202263688045963602542894011631083641044692825359828823542657027367024356958604886307693018678279928245898900407742438461187390028258649235211922923421227807324455849874298160123122949365949350202304939309076827851283935404783962022643809318978297826249769411973978959819537379701892477953347561145373476017793719607872466109740609021714564791484982159011225213308825156483310174931447002306775907398070578210249635187552549317693239502461294646671896476086896836126041214898983971881714898308881081958400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3301465, a6 := -2309192023 }
def label : String := "570.l2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 5, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3301465, a6 := -2309192023 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, -2, 1, 1, 1, 2, 1, 4, -2, 1, 1, -2, 1, -1, 1, -2, 2, 4, 1, 1, 4, 1, -2, 0, 1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (39696163971095466848092169580008049405932033061761698674150040143025388249780526620649127931693610844286613902742717253489796627275739593572682075042842091455629609536251582598746908034249863884236645398612609013154690316921588478286253235608897224203833281506260409410254147166170882466547948758790175560881712622596690087266854424608035557687212305371169318648148448786642466280196538519738745118036241814315431284632737243019826271927923363755014569087658981024556624567902363590806767954440704219332272958880653831 : Rat)/49686535841192824821271460180432549248680020873810088351021709433093697124735125102039470990795390314206630617695393439478245926503418400336699111782455243318912076224519520671531337157146808030052975719624306350115503014135681103777686974178618591040329197304911620105621155309176089098472991061733946436088722465842835244641031260979607479958506413018834667942478864740059724947401888245015662031743389261227012599552759916247807930704772166312021344449409141807065136807478515084357846981597345672661021307908915200,            reHi := (207769270441955880643659328932186800376731447756074411692779579671665110878989937984806716804741959646855821366565691044870539080593007087493885821691365483336545559971490478537968491990215669049819483148802238615085786693561786659474593567969384844314277908942131477922845715374085968679904438659815253034015998885944392690346630899655602559313726899716138472313084655646809080061728224039336094408630866729260922559050643618246136461805155128442924958471524315130304949506116821554032099328715894565255533025089118813 : Rat)/43275369926200202263688045963602542894011631083641044692825359828823542657027367024356958604886307693018678279928245898900407742438461187390028258649235211922923421227807324455849874298160123122949365949350202304939309076827851283935404783962022643809318978297826249769411973978959819537379701892477953347561145373476017793719607872466109740609021714564791484982159011225213308825156483310174931447002306775907398070578210249635187552549317693239502461294646671896476086896836126041214898983971881714898308881081958400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -87945, a6 := -8655975 }
def label : String := "570.l3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -87945, a6 := -8655975 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, -2, 1, 1, 1, 2, 1, 4, -2, 1, 1, -2, 1, -1, 1, -2, 2, 4, 1, 1, 4, 1, -2, 0, 1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (39696163971095466848092169580008049405932033061761698674150040143025388249780526620649127931693610844286613902742717253489796627275739593572682075042842091455629609536251582598746908034249863884236645398612609013154690316921588478286253235608897224203833281506260409410254147166170882466547948758790175560881712622596690087266854424608035557687212305371169318648148448786642466280196538519738745118036241814315431284632737243019826271927923363755014569087658981024556624567902363590806767954440704219332272958880653831 : Rat)/49686535841192824821271460180432549248680020873810088351021709433093697124735125102039470990795390314206630617695393439478245926503418400336699111782455243318912076224519520671531337157146808030052975719624306350115503014135681103777686974178618591040329197304911620105621155309176089098472991061733946436088722465842835244641031260979607479958506413018834667942478864740059724947401888245015662031743389261227012599552759916247807930704772166312021344449409141807065136807478515084357846981597345672661021307908915200,            reHi := (207769270441955880643659328932186800376731447756074411692779579671665110878989937984806716804741959646855821366565691044870539080593007087493885821691365483336545559971490478537968491990215669049819483148802238615085786693561786659474593567969384844314277908942131477922845715374085968679904438659815253034015998885944392690346630899655602559313726899716138472313084655646809080061728224039336094408630866729260922559050643618246136461805155128442924958471524315130304949506116821554032099328715894565255533025089118813 : Rat)/43275369926200202263688045963602542894011631083641044692825359828823542657027367024356958604886307693018678279928245898900407742438461187390028258649235211922923421227807324455849874298160123122949365949350202304939309076827851283935404783962022643809318978297826249769411973978959819537379701892477953347561145373476017793719607872466109740609021714564791484982159011225213308825156483310174931447002306775907398070578210249635187552549317693239502461294646671896476086896836126041214898983971881714898308881081958400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 9335, a6 := -737383 }
def label : String := "570.l4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 9335, a6 := -737383 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, -2, 1, 1, 1, 2, 1, 4, -2, 1, 1, -2, 1, -1, 1, -2, 2, 4, 1, 1, 4, 1, -2, 0, 1, -8,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (39696163971095466848092169580008049405932033061761698674150040143025388249780526620649127931693610844286613902742717253489796627275739593572682075042842091455629609536251582598746908034249863884236645398612609013154690316921588478286253235608897224203833281506260409410254147166170882466547948758790175560881712622596690087266854424608035557687212305371169318648148448786642466280196538519738745118036241814315431284632737243019826271927923363755014569087658981024556624567902363590806767954440704219332272958880653831 : Rat)/49686535841192824821271460180432549248680020873810088351021709433093697124735125102039470990795390314206630617695393439478245926503418400336699111782455243318912076224519520671531337157146808030052975719624306350115503014135681103777686974178618591040329197304911620105621155309176089098472991061733946436088722465842835244641031260979607479958506413018834667942478864740059724947401888245015662031743389261227012599552759916247807930704772166312021344449409141807065136807478515084357846981597345672661021307908915200,            reHi := (207769270441955880643659328932186800376731447756074411692779579671665110878989937984806716804741959646855821366565691044870539080593007087493885821691365483336545559971490478537968491990215669049819483148802238615085786693561786659474593567969384844314277908942131477922845715374085968679904438659815253034015998885944392690346630899655602559313726899716138472313084655646809080061728224039336094408630866729260922559050643618246136461805155128442924958471524315130304949506116821554032099328715894565255533025089118813 : Rat)/43275369926200202263688045963602542894011631083641044692825359828823542657027367024356958604886307693018678279928245898900407742438461187390028258649235211922923421227807324455849874298160123122949365949350202304939309076827851283935404783962022643809318978297826249769411973978959819537379701892477953347561145373476017793719607872466109740609021714564791484982159011225213308825156483310174931447002306775907398070578210249635187552549317693239502461294646671896476086896836126041214898983971881714898308881081958400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_l4

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3040, a6 := 64262 }
def label : String := "570.m1"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3040, a6 := 64262 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, 4, 1, 1, 1, -4, 1, -2, 4, 1, 1, -2, 1, -1, 1, 4, -4, -8, 1, 1, -2, 1, 4, 6, 1, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (139439320493420557507373915378351640629888096433386137640982493089052416747488418612205896950936930876156749201355963231639068858994782140322128310058370475899579475515295200986825837246061043228559984105894141437232051429365625616856388527285503244317601031928481797731600430333981168091213511720524874134209457114915524504695987760481607693813830786758269352367730909749620122540177652872692689709325221204954954036124472214772098707425464803456649865019650493559423079779915237581018606463718487233042640547417481087 : Rat)/139442858651089540627439259216052638214037477936176699565770603892875859672643738189594644393522547010837963346435459007567980503412819381590091055647535682862753246178490267691071817182960396729503512503461762982582218136445298581569637637210961852274472263404106804812549693932203862953779039431317849675474801758978279557540958700168575830851292191375439229386956813947909550658837557332785890218118544055701616005196455248824493224881134789327285708616083720555311835556471961688359118948353841081338995283486310400,            reHi := (6710553384676376875192763153597128437443992882522168288833942924773078240132205830719554574954358991690762594338503771841372901712057304430986105865319199342162867303977399361596362540239620834196493383379089293760499158794282074306923074674894764775536221655244267032828163148407633153247824157303255867271946568847322922478749567629311644862205790083752242533925249368924987538233991742793387776230232871714163854280071592334408324045534169935976365991624997348621985845058248633559134507223826633977517547284618209603 : Rat)/1341536467712206270174329424871678829714360563592872385477586154693529822367848377755065716751475538483579026677775622865912640015592296809090876018126291569610626058062027058131346103242963816811430344429856271453118581381663389801997548302822701958088888327232613742851771193347754405658770758666816553774395506577756551605307844046449401958879673151508536034446929347981612573579850982615422874857071510053129340187924517738690814129028848490424576300134046828790758693801919907277661868503128333161847575313540710400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -220, a6 := 650 }
def label : String := "570.m2"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 5, 5, 5, 5, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -220, a6 := 650 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, 4, 1, 1, 1, -4, 1, -2, 4, 1, 1, -2, 1, -1, 1, 4, -4, -8, 1, 1, -2, 1, 4, 6, 1, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (139439320493420557507373915378351640629888096433386137640982493089052416747488418612205896950936930876156749201355963231639068858994782140322128310058370475899579475515295200986825837246061043228559984105894141437232051429365625616856388527285503244317601031928481797731600430333981168091213511720524874134209457114915524504695987760481607693813830786758269352367730909749620122540177652872692689709325221204954954036124472214772098707425464803456649865019650493559423079779915237581018606463718487233042640547417481087 : Rat)/139442858651089540627439259216052638214037477936176699565770603892875859672643738189594644393522547010837963346435459007567980503412819381590091055647535682862753246178490267691071817182960396729503512503461762982582218136445298581569637637210961852274472263404106804812549693932203862953779039431317849675474801758978279557540958700168575830851292191375439229386956813947909550658837557332785890218118544055701616005196455248824493224881134789327285708616083720555311835556471961688359118948353841081338995283486310400,            reHi := (6710553384676376875192763153597128437443992882522168288833942924773078240132205830719554574954358991690762594338503771841372901712057304430986105865319199342162867303977399361596362540239620834196493383379089293760499158794282074306923074674894764775536221655244267032828163148407633153247824157303255867271946568847322922478749567629311644862205790083752242533925249368924987538233991742793387776230232871714163854280071592334408324045534169935976365991624997348621985845058248633559134507223826633977517547284618209603 : Rat)/1341536467712206270174329424871678829714360563592872385477586154693529822367848377755065716751475538483579026677775622865912640015592296809090876018126291569610626058062027058131346103242963816811430344429856271453118581381663389801997548302822701958088888327232613742851771193347754405658770758666816553774395506577756551605307844046449401958879673151508536034446929347981612573579850982615422874857071510053129340187924517738690814129028848490424576300134046828790758693801919907277661868503128333161847575313540710400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -190, a6 := 992 }
def label : String := "570.m3"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 5, 5, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -190, a6 := 992 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, 4, 1, 1, 1, -4, 1, -2, 4, 1, 1, -2, 1, -1, 1, 4, -4, -8, 1, 1, -2, 1, 4, 6, 1, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (139439320493420557507373915378351640629888096433386137640982493089052416747488418612205896950936930876156749201355963231639068858994782140322128310058370475899579475515295200986825837246061043228559984105894141437232051429365625616856388527285503244317601031928481797731600430333981168091213511720524874134209457114915524504695987760481607693813830786758269352367730909749620122540177652872692689709325221204954954036124472214772098707425464803456649865019650493559423079779915237581018606463718487233042640547417481087 : Rat)/139442858651089540627439259216052638214037477936176699565770603892875859672643738189594644393522547010837963346435459007567980503412819381590091055647535682862753246178490267691071817182960396729503512503461762982582218136445298581569637637210961852274472263404106804812549693932203862953779039431317849675474801758978279557540958700168575830851292191375439229386956813947909550658837557332785890218118544055701616005196455248824493224881134789327285708616083720555311835556471961688359118948353841081338995283486310400,            reHi := (6710553384676376875192763153597128437443992882522168288833942924773078240132205830719554574954358991690762594338503771841372901712057304430986105865319199342162867303977399361596362540239620834196493383379089293760499158794282074306923074674894764775536221655244267032828163148407633153247824157303255867271946568847322922478749567629311644862205790083752242533925249368924987538233991742793387776230232871714163854280071592334408324045534169935976365991624997348621985845058248633559134507223826633977517547284618209603 : Rat)/1341536467712206270174329424871678829714360563592872385477586154693529822367848377755065716751475538483579026677775622865912640015592296809090876018126291569610626058062027058131346103242963816811430344429856271453118581381663389801997548302822701958088888327232613742851771193347754405658770758666816553774395506577756551605307844046449401958879673151508536034446929347981612573579850982615422874857071510053129340187924517738690814129028848490424576300134046828790758693801919907277661868503128333161847575313540710400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -10, a6 := 20 }
def label : String := "570.m4"
def inputConductor : Nat := 570
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 5, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.local_data_valid
theorem conductor_formula : wildLevel equation localData = 570 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -10, a6 := 20 },   conductor := 570,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 1, 1, 1, 1, 1, 4, 1, 1, 1, -4, 1, -2, 4, 1, 1, -2, 1, -1, 1, 4, -4, -8, 1, 1, -2, 1, 4, 6, 1, 4,                    1],   alphaLo := (5397215081808807583435051761664 : Rat)/20508187752226616001129150390625,   alphaHi := (337325942613050473965764476928 : Rat)/1281761734514163494110107421875,   geometricUpper := (1730752251408167 : Rat)/2251799813685248,   tail := (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/43106482392238415492055489380924677386608476932739112134307673779109263785802016516815479485577571043762754527523543494988240888637255952733972536638351763971582697802347041945007898676815746557276414326514137667260683436282588187437022462102414661869361080480196679993913619898853801744717048796243419311389761755049483098147130756667600398991805734002457247694557787849829643517375106619324480773910989302255252682265571732162173390988164299507995592741909254499633156657868911564562426385200907302165544960,   box := { reLo := (139439320493420557507373915378351640629888096433386137640982493089052416747488418612205896950936930876156749201355963231639068858994782140322128310058370475899579475515295200986825837246061043228559984105894141437232051429365625616856388527285503244317601031928481797731600430333981168091213511720524874134209457114915524504695987760481607693813830786758269352367730909749620122540177652872692689709325221204954954036124472214772098707425464803456649865019650493559423079779915237581018606463718487233042640547417481087 : Rat)/139442858651089540627439259216052638214037477936176699565770603892875859672643738189594644393522547010837963346435459007567980503412819381590091055647535682862753246178490267691071817182960396729503512503461762982582218136445298581569637637210961852274472263404106804812549693932203862953779039431317849675474801758978279557540958700168575830851292191375439229386956813947909550658837557332785890218118544055701616005196455248824493224881134789327285708616083720555311835556471961688359118948353841081338995283486310400,            reHi := (6710553384676376875192763153597128437443992882522168288833942924773078240132205830719554574954358991690762594338503771841372901712057304430986105865319199342162867303977399361596362540239620834196493383379089293760499158794282074306923074674894764775536221655244267032828163148407633153247824157303255867271946568847322922478749567629311644862205790083752242533925249368924987538233991742793387776230232871714163854280071592334408324045534169935976365991624997348621985845058248633559134507223826633977517547284618209603 : Rat)/1341536467712206270174329424871678829714360563592872385477586154693529822367848377755065716751475538483579026677775622865912640015592296809090876018126291569610626058062027058131346103242963816811430344429856271453118581381663389801997548302822701958088888327232613742851771193347754405658770758666816553774395506577756551605307844046449401958879673151508536034446929347981612573579850982615422874857071510053129340187924517738690814129028848490424576300134046828790758693801919907277661868503128333161847575313540710400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (86259638142103522161330529886024951775543285722290595171257263391387363770127008583031864919677275062450439627294513160363556490290156173333929140266346203785926598202308160872387910030189381008723599650466287016232117596676912988090108045324653745571169445475322939321263067745207095459552862680335201429460710814462336890805453051812944698047588322486121916857117101784427655576994586228303224718877697289171070685590559393267495117918455230906448788481235522868352548179262411477809929720509563020067081127 : Rat)/86212964784476830984110978761849354773216953865478224268615347558218527571604033033630958971155142087525509055047086989976481777274511905467945073276703527943165395604694083890015797353631493114552828653028275334521366872565176374874044924204829323738722160960393359987827239797707603489434097592486838622779523510098966196294261513335200797983611468004914495389115575699659287034750213238648961547821978604510505364531143464324346781976328599015991185483818508999266313315737823129124852770401814604331089920, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N570.C570_m4
