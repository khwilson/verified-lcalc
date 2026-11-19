module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -7, a6 := -3 }
def label : String := "346.a1"
def inputConductor : Nat := 346
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 173] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 346 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -7, a6 := -3 },   conductor := 346,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 1, -1, 1, -3, -1, -2, 1, -2, -3, -4, -1, 0, -2, 3, 1, -2, -2, 7, -3, 2, -4, -3, -1, 4, 0, 5, -2,                    -4, 3, -7, 1, 4, -2, 6, -2, -4, 7, 0, -3],   alphaLo := (2698607540904403791717525880832 : Rat)/7989100981652131366729736328125,   alphaHi := (5397215081808807583452231630848 : Rat)/15978201963304262638092041015625,   finite := ((1805875491761563 : Rat)/1125899906842624, (9335387273454619 : Rat)/2251799813685248),   tail := (323526016574599925150993561412715911865234375 : Rat)/732269844067948184344309577272103542359851008,   box := { reLo := (223082083472018525963181401624915885900242772835549 : Rat)/191960146003348208836754689824418311008380782641152,            reHi := (1761256346220973967435347093529919368476941233171037 : Rat)/383920292006696417673509379648836622016761565282304,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -16, a6 := -26 }
def label : String := "346.b1"
def inputConductor : Nat := 346
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 173] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 346 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -16, a6 := -26 },   conductor := 346,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 1, 1, -1, 1, 4, 1, -2, -1, 4, 1, -6, 4, -1, 1, -4, -2, 5, -1, 4, 4, 5, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/7989100981652131366729736328125,   alphaHi := (5397215081808807583452231630848 : Rat)/15978201963304262638092041015625,   geometricUpper := (1606316514923953 : Rat)/2251799813685248,   tail := (54643454400761617725257416613112654407211755535891742135060058053576140659652172245764479643425236798253638744938587459266520949603816622786063436018117276321625445176978667914609511893181367423066158881809011429758246978521627180082463849419805744794134529999291178917874789115269748842099183371681528995109457264746559474482767649897778212367560787243870273933972296459642327419140625 : Rat)/46437873019715534851410957581421951085988969503245777907656096238545646771308611487365205319201573198032180969573887940691576860745157779692386567602224303986952164098798226020393803255274876652773367095219950281429736405658343921893893689466491224597186835484531334747553601503891006904630446441736003712700890991711942685586444710372326144338232617114221387744681355286607040794853376,   box := { reLo := (14862686705661819979668294727541823720503318374455778084956584520012221027025844824554464415913449930309161726829912194777240371069450012852165759201535249094653098039363636276713332175985863812315958706630780326626187668783979971614614769908878400428850507468352106048493631357374800435332239857717146953802556156936506314494337892276352846243237078020089769846485995788432840471545665566487 : Rat)/12284535615016488442987700485716618674434264025480128350357620730656149759941666157033129319525626569087839057148167594166727668010941803566484865433789610703796364634203786316756915531740650045094708211268199987598578179543641326066044954930397189081266013898571465700113587081034815293530224410357517214146755600274502182216981324347764041244803041833544783249814771683453166750748127526912,            reHi := (1006781707083679085938493943926398576171217149288623160482006307380303389232412988304462648658886216366411996391542064229041286749618989846983386091434706983456142171962208750640642402264867261856703453702559122663145117692047029995757216425263667902760559556223695764762585941425232324648736288062285746204100916730274936075537708776251589814564518953168829955211416587264583666289165234015471 : Rat)/282544319145379234188717111171482229511988072586042952058225276805091444478658321611761974349089411089020298314407854665834736364251661482029151904977161046187316386586687085285409057230034951037178288859168599714767298129503750499519033963399135348869118319667143711102612502863800751751195161438222895925375378806313550190990570459998572948630469962171530014745739748719422835267206933118976,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (54643454400761617725257416613112654407211755535891742135060058053576140659652172245764479643425236798253638744938587459266520949603816622786063436018117276321625445176978667914609511893181367423066158881809011429758246978521627180082463849419805744794134529999291178917874789115269748842099183371681528995109457264746559474482767649897778212367560787243870273933972296459642327419140625 : Rat)/92875746039431069702821915162843902171977939006491555815312192477091293542617222974730410638403146396064361939147775881383153721490315559384773135204448607973904328197596452040787606510549753305546734190439900562859472811316687843787787378932982449194373670969062669495107203007782013809260892883472007425401781983423885371172889420744652288676465234228442775489362710573214081589706752, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N346.C346_b1
