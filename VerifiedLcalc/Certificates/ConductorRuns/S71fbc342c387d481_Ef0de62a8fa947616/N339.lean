module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2, a6 := 2 }
def label : String := "339.a1"
def inputConductor : Nat := 339
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 113] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 339 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -2, a6 := 2 },   conductor := 339,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 1, 2, -3, -2, 1, 0, 1, 6, -2, 2, -2, -2, -3, -4, -2, -2, 0, -6, 1, 4, -5, 0, 4, 4, 1, 2, -5,                    6, -4, 8, -2, 4, -3, 2, -4, 0, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/988484180528096675872802734375,   alphaHi := (5397215081808807583452231630848 : Rat)/15815746888449546718597412109375,   finite := ((6106215846950217 : Rat)/9007199254740992, (22379206448207777 : Rat)/9007199254740992),   tail := (18933959554800379109094862270832061767578125 : Rat)/45859075124060452824718479693300735250792448,   box := { reLo := (203928844738238242079697031371537551944272173163543 : Rat)/769387608916589014098112073006120188261359071264768,            reHi := (2229272678711475071008463564927712308576163270062783 : Rat)/769387608916589014098112073006120188261359071264768,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -441, a6 := 3422 }
def label : String := "339.b1"
def inputConductor : Nat := 339
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 113] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 339 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -441, a6 := 3422 },   conductor := 339,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 1, -2, -1, 0, -3, 0, 1, 0, -4, -2, -2, 0, -1, 4, -2, 0, -2, 2, -3, 0, 1, 0, -4, 0, 1, 6, -7, 0,                    8, 0, -4, 0, 3, -2, 4, 0, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/988484180528096675872802734375,   alphaHi := (5397215081808807583452231630848 : Rat)/15815746888449546718597412109375,   finite := ((6427115699351503 : Rat)/4503599627370496, (981034271581431 : Rat)/281474976710656),   tail := (18933959554800379109094862270832061767578125 : Rat)/45859075124060452824718479693300735250792448,   box := { reLo := (390169412813972461528584588603179946501264596496337 : Rat)/384693804458294507049056036503060094130679535632384,            reHi := (93725994572897829415620814278783573368714584398249 : Rat)/24043362778643406690566002281441255883167470977024,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -112, a6 := 501 }
def label : String := "339.c1"
def inputConductor : Nat := 339
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 113] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 339 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -112, a6 := 501 },   conductor := 339,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, -1, 2, 2, -2, 3, 0, 1, 4, -6, -2, 5, 6, -2, -4, 3, 2, 0, 4, -3, -12, 3, 0],   alphaLo := (337325942613050473964690735104 : Rat)/988484180528096675872802734375,   alphaHi := (5397215081808807583452231630848 : Rat)/15815746888449546718597412109375,   geometricUpper := (1600752819932579 : Rat)/2251799813685248,   tail := (50103368367217518850579665302320621564067152942709858611987873598254148142572345573782519118203787451978017340357896229901445831553342277639502558870019580812214290428314884028944123842008654088910996414997299100046889388627457438867853980170924202043326269429951082912753480310326758396003113425197791603418279201136322715598072048046325271357292299530567160606912530416241794726171875 : Rat)/46981116729594020432803636400252388938269241357430212907464732196779009837787055679012575900552718060092448652298298863937501952915130274397993910634376481701313031714916673563070819254817451908232446551043096855071167424484849574861860665955685436102623022122660243331828431617949471343748242554730432583884740392277522978195201884637845892226891176531647969077457706701313633175994368,   box := { reLo := (141506743721974485337810376673334710439914489081615176399744312396612918923135425773350259324331288782330947772954307005235533121599844075474114580347268249032952061682889274216777066850319264291899491804562189138311166935419893483574972710255517589980299575666372724089719537460830838613913839404923464933323565487685511928714102520042400858010643613655149378463800214958435763417590017654607 : Rat)/91939931289562666256077240271655913794690683220629842300327644996147667197106567546322055471466144371288217852358417453276814134267028766134526173385496227747793043979664758912619255094811286599075027440296543606015796447182748799773792539545308392608208636258050576489438308396904307693504842008692493697196162134369459979793991304151455708022875822369491151325976246417669221011928058429440,            reHi := (202564090924866609908014648634909543037353534830799018460769826773907176588473104244328000873308841099984033051124427424888364068349652181164571720258676734554701864169613361956231339866717036800186286535853761130920612692097088254422887541414930541978567431581491210823103250301964688220441875771973213311888821538887942557279507815952728797064113742451813789882973739831032299984661103660343 : Rat)/55163958773737599753646344162993548276814409932377905380196586997688600318263940527793233282879686622772930711415050471966088480560217259680715704031297736648675826387798855347571553056886771959445016464177926163609477868309649279864275523727185035564925181754830345893662985038142584616102905205215496218317697280621675987876394782490873424813725493421694690795585747850601532607156835057664,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (50103368367217518850579665302320621564067152942709858611987873598254148142572345573782519118203787451978017340357896229901445831553342277639502558870019580812214290428314884028944123842008654088910996414997299100046889388627457438867853980170924202043326269429951082912753480310326758396003113425197791603418279201136322715598072048046325271357292299530567160606912530416241794726171875 : Rat)/93962233459188040865607272800504777876538482714860425814929464393558019675574111358025151801105436120184897304596597727875003905830260548795987821268752963402626063429833347126141638509634903816464893102086193710142334848969699149723721331911370872205246044245320486663656863235898942687496485109460865167769480784555045956390403769275691784453782353063295938154915413402627266351988736, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N339.C339_c1
