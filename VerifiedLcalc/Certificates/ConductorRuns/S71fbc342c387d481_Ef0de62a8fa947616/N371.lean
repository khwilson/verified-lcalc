module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -35, a6 := -98 }
def label : String := "371.a1"
def inputConductor : Nat := 371
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.nonsingular
def minimality : MinimalityWitness := { primes := [7, 7, 7, 7, 53] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 371 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -35, a6 := -98 },   conductor := 371,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, -1, 0, -1, -1, -3, -2, 0, 0, 1, 1, -1, 0, -1, -7, -2, -7, 0, 1, 0, 1, 3, -5, 1, 5, 1, 9, 0,                    4, 5, 0, -7, 0, 2, -3, -7, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16545382499472465991973876953125,   alphaHi := (1349303770452201895863057907712 : Rat)/4136345624868116474151611328125,   finite := ((14268283063322559 : Rat)/9007199254740992, (39364302863240299 : Rat)/9007199254740992),   tail := (16127983467189232844864417741718292236328125 : Rat)/29068355611743158387811135522450083139289088,   box := { reLo := (31372481652946475912617252534913715026547007791051 : Rat)/30480380053939194049657449241588618377863194738688,            reHi := (150120294967569681025754797831832731339369750007911 : Rat)/30480380053939194049657449241588618377863194738688,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -31, a6 := -67 }
def label : String := "371.b1"
def inputConductor : Nat := 371
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.nonsingular
def minimality : MinimalityWitness := { primes := [7, 7, 7, 53] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 371 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -31, a6 := -67 },   conductor := 371,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 2, 0, 2, 3, 0, 1, 0, -3, 6, 3, 0, -6, 2, 0, -4, 6, -6, -5, 6, 0, 6, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16545382499472465991973876953125,   alphaHi := (1349303770452201895863057907712 : Rat)/4136345624868116474151611328125,   geometricUpper := (203128101799103 : Rat)/281474976710656,   tail := (1932014082655246225349945797494255713674146348802619957569862685519232142273354619453206704677238460371559889227247366322649780890972138906106146993338492910942604094461834487806486859088265457320365913671195209768398992291709435778248374942380502726222791459699997173518267113187066857335490059432372665295948167936399741730542718193216023993425008798354274609375 : Rat)/1180848087126320996182527968010530698175832074934093432798650645871153814201148967731263465856693028517606548621444612295153854497992569111047395218878522869719967735447130962500377533377358819319249865665034077900950350957542361844522286182061553286223659348509132775525152877128957268726752144935690347114203245343473081270301699164987229690608102165993022816256,   box := { reLo := (61377210735678411952123451322573024788782915005588130682799761953096243860970906268008416685282232348211214282618241948110433750440749308392394855645013613200405168949640972768307975145168334817740641236298437663840386181430822029530628527064573815361550598291396332685251463975353584124872669891253856712748720932602795741882453741093360017187875977922109214907380566497 : Rat)/43906464798503500596603201373122913946525023705850327461867184119124892436930180084784159220686109406830781743792103683827193415253261913609485350900647974727743949734716863281678600000779295336957149796387818514454431587104228941745495100552909073213594604326872108683828685424576072864602063632059854161500636627831590911389141972098934097504495592910766643342338949120,            reHi := (615150198787011573713805872750260781680984688632335967492027964981296916282989179868606796640359398506637566983718039480072509269713001072219017941417227252160605229906391391801569782974510394137425341922877054291747926667554020020978880086835403809585438616568542733779331680017696762645657334167825195492714165625675014484662339208811377554313455724275745472917461164637 : Rat)/131719394395510501789809604119368741839575071117550982385601552357374677310790540254352477662058328220492345231376311051481580245759785740828456052701943924183231849204150589845035800002337886010871449389163455543363294761312686825236485301658727219640783812980616326051486056273728218593806190896179562484501909883494772734167425916296802292513486778732299930027016847360,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (1932014082655246225349945797494255713674146348802619957569862685519232142273354619453206704677238460371559889227247366322649780890972138906106146993338492910942604094461834487806486859088265457320365913671195209768398992291709435778248374942380502726222791459699997173518267113187066857335490059432372665295948167936399741730542718193216023993425008798354274609375 : Rat)/2361696174252641992365055936021061396351664149868186865597301291742307628402297935462526931713386057035213097242889224590307708995985138222094790437757045739439935470894261925000755066754717638638499731330068155801900701915084723689044572364123106572447318697018265551050305754257914537453504289871380694228406490686946162540603398329974459381216204331986045632512, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N371.C371_b1
