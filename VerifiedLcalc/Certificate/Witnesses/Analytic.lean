/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates
public import VerifiedLcalc.Certificate.Analytic.EnclosurePredicates
public import VerifiedLcalc.Certificate.Artifacts.ScanWitness
public import VerifiedLcalc.Certificate.Artifacts.Contracts
public import VerifiedLcalc.Certificate.Numerical.RankContracts
public import VerifiedLcalc.Certificate.Numerical.CentralFormula
public import VerifiedLcalc.Certificate.Numerical.Payloads
public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealizationData
public import VerifiedLcalc.EllipticCurve.PadicRegulator
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product

/-! # L-values, derivatives and analytic rank

* `VerifiedLcalc.Certificate` certifies a finite scan of given boxes.
  `AnalyticCertificate` also proves the exact analytic order for the specified function
  and center. `SpecialLValueFacts` bounds the error in a reported Taylor leading coefficient
  for any arithmetic modular realization of the given curve.
* `EllipticCurve.CentralSeriesEvidence` gives the convergent split Mellin series, its finite
  sum, and a summand bound used to enclose the central value.
* `Artifacts.Checked` certifies the finite exact-rank artifact contract.
  `NumericalRanks.Checked` certifies the finite cutoff contract. `Artifacts.AnalyticEvidence`
  and `NumericalRanks.Evidence` supply the function, analyticity, and actual derivative
  enclosures for their respective artifacts.
* `CentralCurveEnclosure` and `DerivativeCurveEnclosure` bind the central and scaled
  first-derivative bounds to the real parts of the corresponding values for any explicit
  arithmetic modular realization. `CentralNumericalFact` and `DerivativeNumericalFact`
  retain finite payload checks, zero exclusion, and optional actual containment.
* `ConditionalAnalyticRank` gives the exact order at 1 for any explicit arithmetic modular
  realization. `CurvePrecisionFact` gives a checked derivative prefix within a cutoff for a
  fixed realization. `AnalyticFacts` collects optional payloads, rank, and special values.
* `RealPeriodFact` encloses the full minimal real period. `TamagawaProductFact` identifies
  the intrinsic product over finite places. `ComplexPeriodAreaReport` retains a reported
  covolume pending a comparison with the curve's Néron differential.
* `AnalyticShaFact` encloses the BSD quotient obtained from the leading coefficient.
  `RoundedAnalyticShaFact` identifies its nearest integer and optional prime support.
  Finiteness and order of the cohomological Sha group require independent evidence.
* `PadicRegulatorReport` preserves the reported ball. `OrdinaryIwasawaInvariants` and
  `SupersingularIwasawaInvariants` retain source values in the entries of
  `IwasawaPrimeReport` and `IwasawaReport`. Identifying those reports with the curve's
  normalized p-adic heights or L-series requires additional mathematical evidence.
-/

@[expose] public section

/-! ## Orders of vanishing and reported special values -/

namespace VerifiedLcalc

open EllipticCurve Modularity

/-- A proof-carrying finite rank contract. Its proof is entirely about the
supplied rectangles; the executable scan equation is exposed by compatibility. -/
structure Certificate (bs : List Box) where
  /-- First derivative index whose box excludes zero. -/
  rank : Nat
  /-- Finite mathematical witness for this rank and these boxes. -/
  sound : Witness bs rank

/-- An analytic order is certified by a finite witness on these exact boxes. -/
structure AnalyticCertificate (f : ℂ → ℂ) (center : ℂ) (bs : List Box) where
  /-- Claimed order of vanishing. -/
  rank : ℕ
  /-- The same boxes witness the first nonzero derivative at this rank. -/
  sound : Witness bs rank
  /-- The function has this analytic order at the specified center. -/
  correct : analyticOrderAt f center = rank

/-- A proved enclosure for the Taylor leading coefficient at the analytic
order of the actual curve L-function. -/
structure SpecialLValueFacts (curve : WeierstrassCurve ℤ) where
  /-- The order used to normalize the derivative by its factorial. -/
  order : Nat
  /-- The exact reported value and claimed error radius. -/
  claim : SpecialLValueClaim
  /-- The checked order and normalized leading coefficient bound for every
  arithmetic modular realization of this same curve. -/
  correct : ∀ m : ArithmeticModularRealization curve,
    analyticOrderAt m.formL 1 = order ∧
      |(iteratedDeriv order m.formL 1).re / (order.factorial : ℝ) -
        (claim.reported : ℝ)| ≤ (claim.error : ℝ)

end VerifiedLcalc

/-! ## Enclosures and numerical evidence -/

namespace VerifiedLcalc.EllipticCurve

/-- Remaining analytic obligations for an actual central value. The series
must be the convergent split-Mellin exponential series, not the raw Dirichlet
series evaluated outside its convergence domain. -/
structure CentralSeriesEvidence (r : CentralResult) (value : ℝ) where
  /-- Summands of the split Mellin series. -/
  series : Nat → ℝ
  /-- The summands converge to the actual value. -/
  formula : HasSum series value
  /-- The initial series sum is the exact finite Mellin expression. -/
  finiteSum : (∑ j ∈ Finset.range r.termLimit, series j) =
    centralFiniteValue r.coefficients r.rootNumber (2 * Real.pi / Real.sqrt r.conductor)
  /-- A quadratic-times-geometric majorant for every summand. -/
  majorant : ∀ j, |series j| ≤ ((1 + r.rootNumber : Int).natAbs : ℝ) *
    (((j + 1 : Nat) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (j + 1))

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.Artifacts

/-- A checked artifact retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical contract. -/
  artifact : Artifact
  /-- Proof that its request and boxes satisfy the expected contract. -/
  contract : WitnessAccepts expected artifact

end VerifiedLcalc.Artifacts

namespace VerifiedLcalc.NumericalRanks

/-- A checked numerical observation retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical acceptance conditions. -/
  artifact : Artifact
  /-- Proof that request, bound, and boxes satisfy the expected conditions. -/
  contract : CutoffAccepts expected artifact

end VerifiedLcalc.NumericalRanks

namespace VerifiedLcalc.Artifacts

/-- Proof obligations connecting a finite artifact to its intended function. -/
structure AnalyticEvidence (expected : Request) (artifact : Artifact) where
  /-- Function whose derivatives are enclosed. -/
  function : ℂ → ℂ
  /-- The request's subject denotes this function. -/
  denotes : expected.subject.Denotes function
  /-- The function is analytic at the documented center. -/
  analytic : AnalyticAt ℂ function (expected.subject.center : ℂ)
  /-- Each supplied box encloses the corresponding derivative. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.subject.center : ℂ))

end VerifiedLcalc.Artifacts

namespace VerifiedLcalc.NumericalRanks

/-- The numerical request's subject, analyticity, and true-derivative boxes. -/
structure Evidence (expected : Request) (artifact : Artifact) where
  /-- Function whose derivatives are enclosed. -/
  function : ℂ → ℂ
  /-- The request's subject denotes this function. -/
  denotes : expected.computation.subject.Denotes function
  /-- The function is analytic at the documented center. -/
  analytic : AnalyticAt ℂ function (expected.computation.subject.center : ℂ)
  /-- Each supplied box encloses the corresponding derivative. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.computation.subject.center : ℂ))

end VerifiedLcalc.NumericalRanks

/-! ## Analytic certificate fields -/

namespace VerifiedLcalc

open EllipticCurve Modularity

/-- The central box encloses the real part of the actual central value. -/
structure CentralCurveEnclosure (curve : WeierstrassCurve ℤ) (r : CentralResult) : Type where
  /-- Containment for an explicit arithmetic realization. -/
  contains : ∀ m : ArithmeticModularRealization curve,
    r.box.Contains (Complex.ofReal (m.formL 1).re)

/-- The scaled first-derivative bounds enclose the actual raw derivative's real part. -/
structure DerivativeCurveEnclosure (curve : WeierstrassCurve ℤ) (r : DerivativeResult) : Type where
  /-- Containment after scaling the normalized integral enclosure. -/
  contains : ∀ m : ArithmeticModularRealization curve,
    r.realDerivativeBounds.Contains (deriv m.formL 1).re

/-- A central enclosure payload verified for this integral equation. -/
structure CentralNumericalFact (curve : WeierstrassCurve ℤ) where
  /-- The checked evaluator output. -/
  result : CentralResult
  /-- The output's equation is the subject of the fact. -/
  result_curve : result.equation = curve
  /-- The finite evaluator payload passes the mathematical checks. -/
  payload : CentralPayloadCorrect result
  /-- The enclosure excludes zero. -/
  excludes_zero : result.box.excludesZero = true
  /-- Actual scalar containment when arithmetic evidence is available. -/
  enclosure : Option (CentralCurveEnclosure curve result) := none

/-- A first-derivative enclosure payload verified for this integral equation. -/
structure DerivativeNumericalFact (curve : WeierstrassCurve ℤ) where
  /-- The checked evaluator output. -/
  result : DerivativeResult
  /-- The output's equation is the subject of the fact. -/
  result_curve : result.equation = curve
  /-- The finite evaluator payload passes the mathematical checks. -/
  payload : DerivativePayloadCorrect result
  /-- The enclosure excludes zero. -/
  excludes_zero : result.box.excludesZero = true
  /-- Actual scalar containment when arithmetic evidence is available. -/
  enclosure : Option (DerivativeCurveEnclosure curve result) := none

/-- An analytic rank that can be instantiated with any arithmetic realization. -/
structure ConditionalAnalyticRank (curve : WeierstrassCurve ℤ) where
  /-- The checked rank. -/
  val : Nat
  /-- The rank identification given an explicit arithmetic realization. -/
  correct : ∀ m : ArithmeticModularRealization curve, analyticOrderAt m.formL (1 : ℂ) = val

/-- Package a checked derivative prefix with its curve and supplied realization. -/
structure CurvePrecisionFact (curve : WeierstrassCurve ℤ) (m : ModularRealization curve) where
  /-- The curve, cutoff policy, derivative count and proposed gap. -/
  claim : Assumptions.CurvePrecisionClaim
  /-- The claim concerns the same curve as the realization. -/
  claim_curve : claim.equation = curve
  /-- The checked derivatives satisfy the claim's numerical cutoff. -/
  small : NumericalRanks.SmallDerivatives m.formL 1 claim.derivativeCount claim.policy.cutoff

/-! ## Periods and the BSD quotient -/

/-- A reported decimal with an error bound for the full real period of a global minimal model. -/
structure RealPeriodFact (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- Exact rational representation of the reported real period. -/
  reported : ℚ
  /-- Nonnegative rational enclosure radius. -/
  error : { ε : ℚ // 0 ≤ ε }
  /-- The full real period, including all real components, lies within this error. -/
  correct : |(curve.baseChange ℚ).minimalRealPeriod - (reported : ℝ)| ≤ (error.val : ℝ)

/-- A reported covolume of the complex period lattice for the Néron differential on this curve. -/
structure ComplexPeriodAreaReport (curve : WeierstrassCurve ℤ) where
  /-- Positive reported area represented as an exact rational decimal. -/
  reported : { a : ℚ // 0 < a }

/-- The product of all finite-place Tamagawa numbers of the given rational curve. -/
structure TamagawaProductFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The exact positive integer product. -/
  value : ℕ
  /-- Equality with the product over all rational finite places. -/
  correct : (curve.baseChange ℚ).tamagawaProduct (R := ℤ) = value

/-- An enclosure for the analytic BSD quotient using the intrinsic arithmetic factors. -/
structure AnalyticShaFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Order of the leading Taylor coefficient at the central point. -/
  order : ℕ
  /-- Exact rational representation of the reported analytic quotient. -/
  reported : ℚ
  /-- Nonnegative rational enclosure radius. -/
  error : { ε : ℚ // 0 ≤ ε }
  /-- The analytic order is identified for each explicit realization of this equation. -/
  order_correct : ∀ m : ArithmeticModularRealization curve, analyticOrderAt m.formL 1 = order
  /-- The denominator in the analytic BSD quotient is positive. -/
  denominator_pos :
    let E := curve.baseChange ℚ
    0 < E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ)
  /-- The true analytic quotient lies within the reported error for each realization. -/
  correct : ∀ m : ArithmeticModularRealization curve,
    let E := curve.baseChange ℚ
    |(iteratedDeriv order m.formL 1).re / (order.factorial : ℝ) *
      (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
      (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ)) -
      (reported : ℝ)| ≤ (error.val : ℝ)

/-- The analytic quotient's enclosure lies strictly in a single integer rounding cell. -/
structure RoundedAnalyticShaFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The analytic quotient and its checked enclosure. -/
  analytic : AnalyticShaFact curve
  /-- Unique nearest integer to the analytic quotient. -/
  value : ℕ
  /-- The reported positive integer has a finite prime factorization. -/
  value_pos : 0 < value
  /-- The entire closed error interval lies strictly within half of the integer. -/
  rounds : |analytic.reported - (value : ℚ)| + analytic.error.val < 1 / 2
  /-- Optional exact prime support of the rounded integer. -/
  primes : Option { ps : Finset ℕ // ps = value.primeFactors } := none

/-! ## Reported p-adic data -/

/-- A reported ball for a p-adic regulator on the curve used by the producer.

The LMFDB display looks up a stored positive-rank row only for curve number 1
in the class and displays one directly for rank zero. The ball has center
`p^val * unit` and additive error subgroup `p^prec ℤ_p`. The source's `prec` counts
absolute precision, so the unit has `prec - val` relative digits. -/
structure PadicRegulatorReport (curve : WeierstrassCurve ℤ) where
  /-- The rational prime of the reported regulator. -/
  p : Nat.Primes
  /-- The source's exponent of the absolute error subgroup. -/
  prec : ℤ
  /-- Valuation of the nonzero reported ball, allowing negative values. -/
  val : ℤ
  /-- The residue retains at least one digit of the unit. -/
  precise : val < prec
  /-- Unit representative of the reported residue. -/
  unit : ℤ
  /-- The representative is a p-adic unit. -/
  unit_not_dvd : ¬ ((p : ℕ) : ℤ) ∣ unit

/-- A normalized p-adic ball containing the empty ordinary height determinant of the
specified rational curve. The proof is independent of any catalogue class label. -/
structure RankZeroPadicRegulatorFact (curve : WeierstrassCurve ℤ) where
  /-- Prime, precision, valuation and unit supplied by the report. -/
  report : PadicRegulatorReport curve
  /-- The submitted equation is smooth after reduction at the reported prime. -/
  good : (curve.baseChange (ZMod (report.p : ℕ))).Δ ≠ 0
  /-- The reduced elliptic curve is ordinary at the reported prime. -/
  ordinary :
    letI : Fact (report.p : ℕ).Prime := ⟨report.p.property⟩
    (curve.baseChange (ZMod (report.p : ℕ))).IsOrdinary report.p
  /-- The unit representative lies in the canonical residue interval. -/
  normalized : 0 ≤ report.unit ∧
    report.unit < (report.p : ℕ) ^ (report.prec - report.val).toNat
  /-- Nonsingularity of the rational curve. -/
  elliptic : (curve.baseChange ℚ).IsElliptic
  /-- The rank of its rational point module is zero. -/
  rankZero :
    letI := elliptic
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 0
  /-- The determinant differs from the reported center by an element of `p^prec ℤ_p`. -/
  contains :
    letI := elliptic
    letI : Fact (report.p : ℕ).Prime := ⟨report.p.property⟩
    ‖rankZeroPadicRegulator (curve.baseChange ℚ) rankZero report.p -
      (report.p : ℚ_[(report.p : ℕ)]) ^ report.val * (report.unit : ℚ_[(report.p : ℕ)])‖ ≤
      ((report.p : ℕ) : ℝ) ^ (-report.prec)

/-- The reported analytic Iwasawa invariants at an ordinary or multiplicative prime. -/
structure OrdinaryIwasawaInvariants where
  /-- Index of the first coefficient of minimal valuation in the source normalization. -/
  lambda : ℕ
  /-- Minimal coefficient valuation in the source normalization. -/
  mu : ℕ

/-- The reported analytic Iwasawa invariants at a supersingular prime. -/
structure SupersingularIwasawaInvariants where
  /-- Lambda invariant of the plus branch. -/
  lambdaPlus : ℕ
  /-- Lambda invariant of the minus branch. -/
  lambdaMinus : ℕ
  /-- The single mu value the source reports for both branches. -/
  mu : ℕ

/-- One reported analytic Iwasawa entry for this curve. -/
structure IwasawaPrimeReport (curve : WeierstrassCurve ℤ) where
  /-- The prime indexing this entry. -/
  p : Nat.Primes
  /-- Outer `none` records additive reduction. The left branch records the
  ordinary or multiplicative case and the right branch the supersingular case.
  Inner `none` means the source lists the prime but lacks invariant values. -/
  data : Option (Sum (Option OrdinaryIwasawaInvariants)
    (Option SupersingularIwasawaInvariants))

/-- Prime-indexed Iwasawa data and any reported good-prime vanishing threshold. -/
structure IwasawaReport (curve : WeierstrassCurve ℤ) where
  /-- Entries present in the reported finite prime list. -/
  entries : List (IwasawaPrimeReport curve)
  /-- A prime appears at most once in the reported list. -/
  distinct : (entries.map IwasawaPrimeReport.p).Nodup
  /-- The source claims vanishing of the analytic invariants at every good
  prime greater than or equal to this prime when a threshold is supplied. -/
  vanishingThreshold : Option Nat.Primes := none

/-- Optional verified numerical and analytic results attached to the same equation. -/
structure AnalyticFacts (curve : WeierstrassCurve ℤ) where
  /-- A central payload, including when it only supports the finite numerical check. -/
  central : Option (CentralNumericalFact curve) := none
  /-- A first-derivative payload, including when it only supports the finite numerical check. -/
  derivative : Option (DerivativeNumericalFact curve) := none
  /-- A rank result available only with checked arithmetic witnesses and an explicit realization. -/
  rank : Option (ConditionalAnalyticRank curve) := none
  /-- A reported Taylor leading coefficient checked against the actual enclosure. -/
  specialValue : Option (SpecialLValueFacts curve) := none
  /-- A p-adic regulator enclosure supported by a checked rank-zero proof. -/
  padicRegulator : Option (RankZeroPadicRegulatorFact curve) := none

end VerifiedLcalc
