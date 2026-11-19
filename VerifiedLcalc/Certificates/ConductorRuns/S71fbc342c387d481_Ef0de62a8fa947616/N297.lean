module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -81, a6 := 290 }
def label : String := "297.a1"
def inputConductor : Nat := 297
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 297 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -81, a6 := 290 },   conductor := 297,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -2, 0, 2, -2, 0, 1, 0, 0, 4, 1, 0, -5, -2, 0, -4, -2, 0, 3, -4, 0, -2, -4, 0, -1, 10, 0, 2, -6, 0,                    -8, 8, 0, 4, -2, 0, -9, -6, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7401812609011212253570556640625,   alphaHi := (5397215081808807583452231630848 : Rat)/14803625218022424411773681640625,   finite := ((5538184399544299 : Rat)/9007199254740992, (9032203001388269 : Rat)/4503599627370496),   tail := (27887985837905442202347809638500213623046875 : Rat)/105971025825445418526701049096182917041750016,   box := { reLo := (78159951785294944226470983924167904525281497238229 : Rat)/222237348751884510354108158514158196839940129554432,            reHi := (252096946385802350651834707290109477837792220950099 : Rat)/111118674375942255177054079257079098419970064777216,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1, a6 := 0 }
def label : String := "297.b1"
def inputConductor : Nat := 297
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 297 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1, a6 := 0 },   conductor := 297,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, -1, 2, 0, -5, 3, 0, -2, -1, 0, -2, 5, 0, -1, -7, 0, 0, -2, 0, 1, 1, 0, -1, 2, 0, 5, -3, 0,                    -8, -5, 0, 7, -10, 0, -3, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/7401812609011212253570556640625,   alphaHi := (5397215081808807583452231630848 : Rat)/14803625218022424411773681640625,   finite := ((4418163418395757 : Rat)/4503599627370496, (2674832005738699 : Rat)/1125899906842624),   tail := (27887985837905442202347809638500213623046875 : Rat)/105971025825445418526701049096182917041750016,   box := { reLo := (79768008339253803201300689278270894104043664897747 : Rat)/111118674375942255177054079257079098419970064777216,            reHi := (73307606441851191793862191399421154836154097840629 : Rat)/27779668593985563794263519814269774604992516194304,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 12, a6 := -19 }
def label : String := "297.c1"
def inputConductor : Nat := 297
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 297 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 12, a6 := -19 },   conductor := 297,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, 0, -1, -2, 0, -5, -3, 0, -2, 1, 0, -2, -5, 0, -1, 7, 0, 0, 2, 0, 1, -1, 0, -1, -2, 0, 5, 3, 0,                    -8, 5, 0, 7, 10, 0, -3, 0, 0, 6],   alphaLo := (2698607540904403791717525880832 : Rat)/7401812609011212253570556640625,   alphaHi := (5397215081808807583452231630848 : Rat)/14803625218022424411773681640625,   finite := ((13355721238237591 : Rat)/9007199254740992, (259546361908911 : Rat)/70368744177664),   tail := (27887985837905442202347809638500213623046875 : Rat)/105971025825445418526701049096182917041750016,   box := { reLo := (271044400287632919078279458096044388795062903505961 : Rat)/222237348751884510354108158514158196839940129554432,            reHi := (6860782569695146594012179673921612014903643409681 : Rat)/1736229287124097737141469988391860912812032262144,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -9, a6 := -11 }
def label : String := "297.d1"
def inputConductor : Nat := 297
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.nonsingular
def minimality : MinimalityWitness := { primes := [3, 3, 3, 11, 11] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 297 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -9, a6 := -11 },   conductor := 297,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 2, 0, 1, 0, 0, 4, -1, 0, -5, 2, 0, -4, 2, 0, 3, 4, 0, -2, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7401812609011212253570556640625,   alphaHi := (5397215081808807583452231630848 : Rat)/14803625218022424411773681640625,   geometricUpper := (6255348042747987 : Rat)/9007199254740992,   tail := (31480889684100043795442167561135064694313328634591310902898780194582318046736898586998180500172598537477371146313534492801972442756295979248152743068448668422308190553030310621027347497597047232753499692699562483226690769453289087481020116625890550560910839564515819775673626691816113401463840532579155248999553241141622757789048929940911334268166480562261578036324773828749395819023746042953244921875 : Rat)/56954329541844995009600064232258301225834711448219200799344317308750555791252302314387020924461319887845703842385268000654577916083018444233501705880679651675488784152924054803648100315256230570185350266703703066141298202512022211992777937421683362243631828536127871337982151394749288004944973386890534287980371045859712305060488994573943332992381451393671703971520827684070688060951668870048303284224,   box := { reLo := (4652918094509633145988854415196196968651622015311482374876573317362816458185502955275953213638004367965618470949083850746943023996768679417944762135342128770670488947675814299022525307198028674110162455043277194896648683812548187193487987458908180315696549998541393011108221073810435213913319984350453953942368709553739268203866114888101122817004155907370080988427546525070032233136348306147524195745734554541 : Rat)/2117684139402664171971225980293141833632663987100846315905336311099972934260932836237373798131354842961262697894626180664198610989596623831164474285802783507147516918247724379697190194896402877214064370492365759442210340254041374129536208222013956919030243975245444250630196360571520265246624717492504945023157913380957472585043335567152574229106011021029953379466163285469130513732073789918122169717992980480,            reHi := (999138872062294291056068560785776347004453023983299562309847433384558553868915404609563065605946996006009296030087242043138129967900652257603410399873707621143403201049926629867563090593524113877498797620063971276966712077886918158075530900519603830556361601092080223578558278193853811468741121144672092119828843524105920102707170350184867043168884193249493856616750942852805905837234878066698810586845193813 : Rat)/302526305628952024567317997184734547661809141014406616557905187299996133465847548033910542590193548994466099699232311523456944427085231975880639183686111929592502416892532054242455742128057553887723481498909394206030048607720196304219458317430565274147177710749349178661456622938788609320946388213214992146165416197279638940720476509593224889872287288718564768495166183638447216247439112845446024245427568640,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (31480889684100043795442167561135064694313328634591310902898780194582318046736898586998180500172598537477371146313534492801972442756295979248152743068448668422308190553030310621027347497597047232753499692699562483226690769453289087481020116625890550560910839564515819775673626691816113401463840532579155248999553241141622757789048929940911334268166480562261578036324773828749395819023746042953244921875 : Rat)/113908659083689990019200128464516602451669422896438401598688634617501111582504604628774041848922639775691407684770536001309155832166036888467003411761359303350977568305848109607296200630512461140370700533407406132282596405024044423985555874843366724487263657072255742675964302789498576009889946773781068575960742091719424610120977989147886665984762902787343407943041655368141376121903337740096606568448, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N297.C297_d1
