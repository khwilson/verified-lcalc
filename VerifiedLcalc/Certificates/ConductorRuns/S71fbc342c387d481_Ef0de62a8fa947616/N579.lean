module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := 0 }
def label : String := "579.a1"
def inputConductor : Nat := 579
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 193] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 579 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := 0 },   conductor := 579,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, 1, -1, 0, -1, 0, 3, 1, 0, -6, -1, -6, 0, 0, -1, 4, -1, 0, 0, 0, 6, 0, 3, -5, 6, 1, 0, 0, 0, 0,                    -5, -6, -4, 0, -1, -10, 0, -6, 0, 0, 0, -4, 6, 0, 0, -6, -1, -7, 5, 4, 6, 4, -1, 0, 0, 0, 0, 0, 0,                    -10, 0, 0, 7],   alphaLo := (2698607540904403791717525880832 : Rat)/10334730194193668651580810546875,   alphaHi := (5397215081808807583452231630848 : Rat)/20669460388387337207794189453125,   finite := ((2758369993465181 : Rat)/1125899906842624, (15634421898264461 : Rat)/4503599627370496),   tail := (1427050801533433505402162548191928863525390625 : Rat)/666432522000620686579958127327107681508917248,   box := { reLo := (53912193246570295205603317813368894479365455265003 : Rat)/174701287047330709262816543330037316061473603059712,            reHi := (3922300570110523845018286010773770236581675645187643 : Rat)/698805148189322837051266173320149264245894412238848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 12, a6 := 3 }
def label : String := "579.a2"
def inputConductor : Nat := 579
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.nonsingular
def minimality : MinimalityWitness := { primes := [3, 193, 193] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 579 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 12, a6 := 3 },   conductor := 579,   policy := { precisionBits := 53 },   termLimit := 64,   stepsPerUnit := 2,   cutoff := 16,   coefficients := [1, -1, 1, -1, 0, -1, 0, 3, 1, 0, -6, -1, -6, 0, 0, -1, 4, -1, 0, 0, 0, 6, 0, 3, -5, 6, 1, 0, 0, 0, 0,                    -5, -6, -4, 0, -1, -10, 0, -6, 0, 0, 0, -4, 6, 0, 0, -6, -1, -7, 5, 4, 6, 4, -1, 0, 0, 0, 0, 0, 0,                    -10, 0, 0, 7],   alphaLo := (2698607540904403791717525880832 : Rat)/10334730194193668651580810546875,   alphaHi := (5397215081808807583452231630848 : Rat)/20669460388387337207794189453125,   finite := ((2758369993465181 : Rat)/1125899906842624, (15634421898264461 : Rat)/4503599627370496),   tail := (1427050801533433505402162548191928863525390625 : Rat)/666432522000620686579958127327107681508917248,   box := { reLo := (53912193246570295205603317813368894479365455265003 : Rat)/174701287047330709262816543330037316061473603059712,            reHi := (3922300570110523845018286010773770236581675645187643 : Rat)/698805148189322837051266173320149264245894412238848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 64 = (List.range 64).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 64

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -2, a6 := 11 }
def label : String := "579.b1"
def inputConductor : Nat := 579
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 193] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 579 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -2, a6 := 11 },   conductor := 579,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, 2, -1, 2, 2, -2, 1, 0, 1, 4, -1, -2, 6, 2, -2, -4, 7, 2, -6, 4, -1, -2, 4, 0, -1, 12, -1, 2, -5,                    -4, 0, -8],   alphaLo := (2698607540904403791717525880832 : Rat)/10334730194193668651580810546875,   alphaHi := (5397215081808807583452231630848 : Rat)/20669460388387337207794189453125,   geometricUpper := (1734309832914653 : Rat)/2251799813685248,   tail := (92307377065586782644407087812756188444052855755996942959045637512287088324144605158704018131089709562661823126872694243392294574041377402327015685559078765093311493103113480908406383470656644349960258211171822952034984482616354061389013649031228955305703377609201230625200843461337335209004431275891710272523552233034127818458743262809482861028198541762375516080303559140638083062559411985862766039696987982175171894466744426296641466392996289002297705838989670536074792132530019938822243336898502266672967133 : Rat)/42713805250743099897581952500088647986831522791400580344878906454368874881892579666448937028225726960117435021928870687053209502752456895381657006545995808170541031041522952827040095968380167215052922088286991531101922238415367733683699783139979009006793452881472296178296444082365053688289865747478826063366732102164972576393889691288349601333007337599066664709181778373381683973831401120025836804957857117608443378789302189363497424386829179064540182338263779059008932928943516670563834611485573579058184192,   box := { reLo := (190450144460797397829547907651303187336398628098642682468722777587160689452875828070846162999231346278796982686216972643721884524594721054598260363376322744518444471339985179367318693958045007311770767069589843274987103517311677517508198234927550914068696419582431476624163392743720512093995734318222790340266284575952030201953711634009797493113915699348232088908949753341111139220237544998900660790411789994821895515890008900762556488253754209741341056365908485106242515196103208906618044876224141180319344750208668179 : Rat)/230287680548559238230499709550004250233547526795095864062778438548028011455081226879383621693506920521416874471948430187977998474774363951597937167860578969774439994972134080662258891520982884914579870105256509504864533954885292128811562873610991947427800521762987755847732814343958958529762895586727208792092748073833659517192671624245854494681130456337505045823061058651356577509580427489704644835100565524248883265492894975790997746398254700800261125614025617776904886566591617379949150890639913022583003369229516800,            reHi := (32016172462054326608100829313274351629773704612126744946524521312930667858899379217249067465709814452570311668253518843547486397862971174087795412652473391397602471804441815289120671163291568697618522840131046229712446422128457390426515383892489401659588889575621395643763435238035364950088033868707779534180918044764368949234095862488951276075513703527550712857629315922260668425741562650063278792709736850485386353671431219858731278186993149247066901882256046573216724882453364271273009447256230713503108878979961182207 : Rat)/6217767374811099432223492157850114756305783223467588329695017840796756309287193125743357785724686854078255610742607615075405958818907826693144303532235632183909879864247620177880990071066537892693656492841925756631342416781902887477912197587496782580550614087600669407888785987286891880303598180841634637386504197993508806964202133854638071356390522321112636237222648583586627592758671542222025410547715269154719848168308164346356939152752876921607050391578691679976431937297973669258627074047277651609741090969196953600,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (92307377065586782644407087812756188444052855755996942959045637512287088324144605158704018131089709562661823126872694243392294574041377402327015685559078765093311493103113480908406383470656644349960258211171822952034984482616354061389013649031228955305703377609201230625200843461337335209004431275891710272523552233034127818458743262809482861028198541762375516080303559140638083062559411985862766039696987982175171894466744426296641466392996289002297705838989670536074792132530019938822243336898502266672967133 : Rat)/85427610501486199795163905000177295973663045582801160689757812908737749763785159332897874056451453920234870043857741374106419005504913790763314013091991616341082062083045905654080191936760334430105844176573983062203844476830735467367399566279958018013586905762944592356592888164730107376579731494957652126733464204329945152787779382576699202666014675198133329418363556746763367947662802240051673609915714235216886757578604378726994848773658358129080364676527558118017865857887033341127669222971147158116368384, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N579.C579_b1
