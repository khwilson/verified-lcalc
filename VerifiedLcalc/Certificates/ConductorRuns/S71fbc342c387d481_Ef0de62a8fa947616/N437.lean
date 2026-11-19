module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 19, a6 := 100 }
def label : String := "437.a1"
def inputConductor : Nat := 437
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 23, 23, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 437 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 19, a6 := 100 },   conductor := 437,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 2, -2, -1, 0, -5, 0, 1, 0, -1, -4, 0, 0, -2, 4, -7, 0, 1, 2, -10, 0, 1, 0, -4, 0, -4, 10, 6, 0,                    4, 0, -2, 0, 5, -2, 2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17956867388507466602325439453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4489216847126866626739501953125,   finite := ((10304290180339621 : Rat)/9007199254740992, (49539200694147701 : Rat)/9007199254740992),   tail := (87939902053384862805924971409397125244140625 : Rat)/94670807158303202030628761892007780158537728,   box := { reLo := (21353276484749002382381888647474940960573117259789 : Rat)/99269536286824938372468584629673950087518856675328,            reHi := (638189764685158279623020977845766994420765327068509 : Rat)/99269536286824938372468584629673950087518856675328,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 0, a6 := -5 }
def label : String := "437.b1"
def inputConductor : Nat := 437
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 23, 23] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 437 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 0, a6 := -5 },   conductor := 437,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 2, 2, 1, 4, -3, 0, 1, 2, 5, 4, -2, -6, 2, -4, 3, 2, -1, 2, -6, 10, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/17956867388507466602325439453125,   alphaHi := (1349303770452201895863057907712 : Rat)/4489216847126866626739501953125,   geometricUpper := (1667231221565875 : Rat)/2251799813685248,   tail := (1108526004452991869554465009910288869280550443611281775933173651791423198757623397143943688436886353443838890645648615356856320866330057169728994230584799589191506637806911598244863465524555084481826626486274612170845886017026112406808200594343008172252162076745886805247353245123365575933588684106983770294709823595123046503308659265385577807026817875879487473866902291774749755859375 : Rat)/323920891647444366058916241146202817662308693985314607935007336717663487604625346311028862583664009523925708572523508709131952419436382115904583690408151955707499234500945034679818244722913185893329180850623511174750898188185815646176190960572131691736809807260293658274469499264147185742292070150597770780917119278596318416747558364850435035205164755931633275971726371994459862728704,   box := { reLo := (76102713190256366664087734019604337935717042619531116074245617281198352785647416785977102572841084223157599834515920033576535084566580542594203865063723418718978816971183949047722009824030047070767814817280830375014722720552468912043871309533160392272301954851194542027567766919358317742869887203357800557491453647325485188797950128136198241879386146391211203103393447007433163111191304217 : Rat)/281549771573717110867847584390591465692355080651177560014852832023636079781527118636122110155682671430129558411277426105416529119307167280469452811616932822837268382133579917528455259585443080786180470691096001548515257448883793658946821949592572861535792926801996425716560967473901884816900071330408528178377693657120969793608060497819444179555082769702484122041692760452980551464750415872,            reHi := (3954934810191800725329660260909692390514267638568804320153264044181307979476310886438248545846122433899355771857828688580534235309558921620184341009304815168554030861140033785420670308812094836898232480473002423374268195498357559999043035940635111194380611350535988121813701608065790575237825544857280483412519833109259443241248640457823983748032991535355692964986508546822371444967076732301 : Rat)/555880318235287629149340102514757509187470287439504413362658155533845593414809952179010320050963223079999384555599020772232634415042355912721740166525739163037683728827837273069001409950746595398356313928574156903478841629847490044587315131246874624057847573429582686671158833217703721305161679293370683839361087476879863438662068162361466713480548032489519933261803655253320575968866205696,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1108526004452991869554465009910288869280550443611281775933173651791423198757623397143943688436886353443838890645648615356856320866330057169728994230584799589191506637806911598244863465524555084481826626486274612170845886017026112406808200594343008172252162076745886805247353245123365575933588684106983770294709823595123046503308659265385577807026817875879487473866902291774749755859375 : Rat)/647841783294888732117832482292405635324617387970629215870014673435326975209250692622057725167328019047851417145047017418263904838872764231809167380816303911414998469001890069359636489445826371786658361701247022349501796376371631292352381921144263383473619614520587316548938998528294371484584140301195541561834238557192636833495116729700870070410329511863266551943452743988919725457408, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N437.C437_b1
