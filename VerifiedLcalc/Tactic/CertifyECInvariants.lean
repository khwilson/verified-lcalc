module

public import VerifiedLcalc.Verification.AbcQuality
public import VerifiedLcalc.Verification.Regulator
public import VerifiedLcalc.EllipticCurve.TorsionBound
public import VerifiedLcalc.EllipticCurve.TorsionStructure
public import VerifiedLcalc.EllipticCurve.TwoFactorTorsion
public import VerifiedLcalc.Certificate.Support.Torsion
public import VerifiedLcalc.Certificate.Support.TorsionPresentation
public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Verification.PadicRegulator
public meta import Lean

/-! Internal stored-invariant checks dispatched exclusively by `certify_ec`.
Absent evidence leaves prerequisite-dependent claims explicitly unverified.
Finite equation invariants and minimality use only standard Lean axioms;
conductor and global root-number identification retain the documented modularity axiom. -/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve NumberField

/-- Certify the stored regulator only when the checked algebraic rank is exactly zero. -/
private def certifyRankZeroRegulator (base : Name) : CommandElabM Unit := do
  let some claim ← bindStored base `regulator `regulator (← `(RegulatorClaim)) | return
  checked (base ++ `regulator_error_nonneg)
    (← `(0 ≤ ($claim).error.getD 0)) (← `(by decide +kernel))
  let rankName := base ++ `algebraic_rank
  unless (← getEnv).contains rankName do
    logInfo m!"Unverified {base} regulator: supply an exact algebraic rank of zero"
    return
  let rankValue := base ++ `mordell_weil_rank
  let isZero ← liftTermElabM do
    let rhs ← whnf (mkConst rankValue)
    Meta.isDefEq rhs (mkNatLit 0)
  unless isZero do
    logInfo m!"Unverified {base} regulator: the checked algebraic rank is nonzero"
    return
  let curve := rootIdent (base ++ `curve)
  let rankZero := rootIdent (base ++ `regulator_rank_zero)
  checked (base ++ `regulator_rank_zero)
    (← `(Module.finrank ℤ (($curve).baseChange ℚ).toAffine.Point = 0))
    (← `(by exact $(rootIdent rankName)))
  let valid := rootIdent (base ++ `regulator_value_valid)
  checked (base ++ `regulator_value_valid)
    (← `(Certification.rankZeroRegulatorValid ($claim).reported ($claim).error = true))
    (← `(by decide +kernel))
  let exact := rootIdent (base ++ `regulator_eq_one)
  checked (base ++ `regulator_eq_one)
    (← `(WeierstrassCurve.Affine.regulator
      (WeierstrassCurve.toAffine (($curve).baseChange ℚ)) = 1))
    (← `(Certification.regulator_eq_one_of_finrank_eq_zero
      (($curve).baseChange ℚ) $rankZero))
  checked (base ++ `regulator_within_error)
    (← `( |WeierstrassCurve.Affine.regulator
        (WeierstrassCurve.toAffine (($curve).baseChange ℚ)) -
        (($claim).reported : ℝ)| ≤ (Option.getD ($claim).error (0 : Rat) : ℝ)))
    (← `(Certification.regulator_within_error_of_valid (($curve).baseChange ℚ)
      ($claim).reported (Option.getD ($claim).error (0 : Rat)) $exact $valid))
  let fact := rootIdent (base ++ `regulator_facts)
  emit (← `(def $fact : RegulatorFacts (($curve).baseChange ℚ) :=
    Certification.rankZeroRegulatorFacts (($curve).baseChange ℚ) $claim $rankZero $valid))

/-- Check the submitted p-adic ball when an independent exact rank-zero proof is present. -/
private def certifyPadicRegulator (base : Name) (curve : Ident) : CommandElabM Unit := do
  let some claim ← bindStored base `padicRegulator `padic_regulator (← `(PadicRegulatorClaim)) |
    return
  let valid := rootIdent (base ++ `padic_regulator_valid)
  checked (base ++ `padic_regulator_valid)
    (← `(Certification.PadicRegulatorClaimValid $claim)) (← `(by decide +kernel))
  let prime := rootIdent (base ++ `padic_regulator_good_ordinary)
  checked (base ++ `padic_regulator_good_ordinary)
    (← `(Certification.goodOrdinaryPadicPrime $curve ($claim).p = true))
    (← `(by decide +kernel))
  let rankName := base ++ `algebraic_rank
  let rankValue := base ++ `mordell_weil_rank
  let isZero ← if (← getEnv).contains rankName then
    liftTermElabM do
      let rhs ← whnf (mkConst rankValue)
      Meta.isDefEq rhs (mkNatLit 0)
    else pure false
  unless isZero do
    logInfo m!"Unverified {base} padic_regulator: supply an exact algebraic rank of zero"
    return
  let center := rootIdent (base ++ `padic_regulator_center)
  checked (base ++ `padic_regulator_center)
    (← `(($claim).val = 0 ∧ ($claim).unit = 1)) (← `(by decide +kernel))
  let fact := rootIdent (base ++ `padic_regulator_fact)
  emit (← `(def $fact : RankZeroPadicRegulatorFact $curve :=
    Certification.rankZeroPadicRegulatorFact $curve $claim $valid $prime
      $(rootIdent rankName) $center))

/-- Check local signs with the validated minimal model and wild data. -/
private def certifyLocalRootNumbers (base : Name) (curve rows : Ident)
    (hasEvidence : Bool) : CommandElabM Unit := do
  let hasClaims := mkApp (mkConst ``hasLocalRootNumberClaim)
    (mkConst (base ++ `claimed_local_invariants))
  let hasClaims ← liftTermElabM <| whnf hasClaims
  unless hasClaims.isConstOf ``Bool.true do return
  checked (base ++ `local_root_number_inputs_valid)
    (← `(($rows).all LocalReductionClaim.checkRootNumberInput = true))
    (← `(by decide +kernel))
  unless hasEvidence do
    logInfo m!"Unverified {base} local root_number: supply minimality and localData evidence"
    return
  let d := rootIdent (base ++ `localData)
  let hd := rootIdent (base ++ `local_data_valid)
  let hv := rootIdent (base ++ `local_root_number_values_valid)
  checked (base ++ `local_root_number_values_valid)
    (← `(($rows).all (fun row => row.checkRootNumber $curve $d) = true))
    (← `(by decide +kernel))
  checked (base ++ `local_root_numbers)
    (← `(∀ row ∈ $rows, LocalReductionClaim.RootNumberSpec row $curve $d))
    (← `(by
      intro row hrow
      exact LocalReductionClaim.rootNumber_correct row $curve $d $hd
        (List.all_eq_true.mp $hv row hrow)))

private def certifyReductionInvariants (base : Name) (curve hn m hm : Ident)
    (hasMinimality hasLocalData : Bool) : CommandElabM Unit := do
  let hglobal := rootIdent (base ++ `global_minimal)
  if let some claim ← bindStored base `semistable `semistable (← `(Bool)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `semistable_value_valid)
      checked (base ++ `semistable_value_valid)
        (← `(decide (Int.gcd ($curve).Δ ($curve).c₄ = 1) = $claim)) (← `(by decide +kernel))
      checked (base ++ `semistable)
        (← `(WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
          (($curve).baseChange ℚ) ↔ $claim = true)) (← `(by
          rw [semistable_iff_coprime_of_isGlobalMinimal $curve $hglobal,
            ← $hv, decide_eq_true_eq]))
    else
      logInfo m!"Unverified {base} semistable: supply minimality evidence"
  if let some claim ← bindStored base `squarefreeDiscriminant `squarefree_discriminant
      (← `(Bool)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `squarefree_discriminant_value_valid)
      checked (base ++ `squarefree_discriminant_value_valid)
        (← `(decide ($m).primes.Nodup = $claim)) (← `(by decide +kernel))
      checked (base ++ `squarefree_discriminant)
        (← `(Squarefree ($curve).Δ.natAbs ↔ $claim = true)) (← `(by
          rw [Certification.squarefree_discriminant_iff_nodup $curve $m $hm,
            ← $hv, decide_eq_true_eq]))
    else
      logInfo m!"Unverified {base} squarefree_disc: supply minimality evidence"
  if let some rows ← bindStored base `localInvariants `local_invariants
      (← `(List LocalReductionClaim)) then
    let hagree := rootIdent (base ++ `local_invariants_agree_valid)
    checked (base ++ `local_invariants_agree_valid)
      (← `(localReductionClaimsAgree $rows = true)) (← `(by decide +kernel))
    checked (base ++ `local_invariants_agree)
      (← `(∀ a ∈ $rows, ∀ b ∈ $rows, LocalReductionClaim.Compatible a b))
      (← `(localReductionClaimsAgree_correct $rows $hagree))
    certifyLocalRootNumbers base curve rows (hasMinimality && hasLocalData)
    let hTam := rootIdent (base ++ `tamagawa_values_valid)
    checked (base ++ `tamagawa_values_valid)
      (← `(($rows).all (fun row => row.checkTamagawa $curve) = true)) (← `(by decide +kernel))
    checked (base ++ `tamagawa_numbers)
      (← `(∀ row ∈ $rows, LocalReductionClaim.TamagawaSpec row $curve)) (← `(by
        intro row hrow
        exact LocalReductionClaim.tamagawa_correct row $curve (List.all_eq_true.mp $hTam row hrow)))
    let unsupported := mkApp2 (mkConst ``hasUnsupportedTamagawaClaim) (mkConst (base ++ `curve))
      (mkConst (base ++ `claimed_local_invariants))
    let unsupported ← liftTermElabM <| whnf unsupported
    if unsupported.isConstOf ``Bool.true then
      logInfo m!"{base}: Tamagawa claims outside good or I₁ reduction are unverified."
    if hasMinimality then
      let hv := rootIdent (base ++ `local_invariants_value_valid)
      checked (base ++ `local_invariants_value_valid)
        (← `(($rows).all (fun row => row.check $curve) = true)) (← `(by decide +kernel))
      checked (base ++ `local_invariants)
        (← `(∀ row ∈ $rows, LocalReductionClaim.Spec row $curve)) (← `(by
          intro row hrow
          exact LocalReductionClaim.check_correct row $curve $hglobal
            (List.all_eq_true.mp $hv row hrow)))
      checked (base ++ `kodaira_symbols)
        (← `(∀ row ∈ $rows, LocalReductionClaim.KodairaSpec row $curve)) (← `(by
          intro row hrow
          exact LocalReductionClaim.kodaira_correct row $curve $hn $hglobal
            (List.all_eq_true.mp $hv row hrow)))
      let additive := mkApp (mkConst ``hasAdditiveKodairaClaim)
        (mkConst (base ++ `claimed_local_invariants))
      let additive ← liftTermElabM <| whnf additive
      if additive.isConstOf ``Bool.true then
        logInfo m!"{base}: additive Kodaira family verified. Exact additive codes unverified."
    else
      let needsMinimality := mkApp (mkConst ``hasMinimalityDependentLocalClaim)
        (mkConst (base ++ `claimed_local_invariants))
      let needsMinimality ← liftTermElabM <| whnf needsMinimality
      if needsMinimality.isConstOf ``Bool.true then
        logInfo m!"Unverified {base} local_invariants: supply minimality evidence"

private def certifyConductorValuations (base : Name) (curve hn : Ident)
    (checkedConductor : Option Ident) : CommandElabM Unit := do
  let some claims ← bindStored base `conductorValuations `conductor_valuations
      (← `(List (Nat × Nat))) | return
  let some n := checkedConductor |
    logInfo m!"Unverified {base} conductor_valuation: supply a checked conductor"
  let hv := rootIdent (base ++ `conductor_valuation_value_valid)
  let hN := rootIdent (base ++ `conductor)
  checked (base ++ `conductor_valuation_value_valid)
    (← `(($claims).all (fun row => isPrime row.1 && padicValNat row.1 $n == row.2) = true))
    (← `(by decide +kernel))
  checked (base ++ `conductor_valuation)
    (← `(∀ row ∈ $claims, row.1.Prime ∧
      (Modularity.modularWitness $curve $hn).level.factorization row.1 = row.2))
    (← `(by
      intro row hrow
      rw [$hN:term]
      exact Certification.factorization_of_prime_exponent_check _ _ _
        (List.all_eq_true.mp $hv row hrow))) true

/-- Certify the requested error on the actual abc quality of the curve. -/
private def certifyAbcQuality (base : Name) (curve : Ident) : CommandElabM Unit := do
  let some claim ← bindStored base `abcQuality `abc_quality (← `(AbcQualityClaim)) | return
  let valid := rootIdent (base ++ `abc_quality_valid)
  checked (base ++ `abc_quality_valid)
    (← `(Certification.abcQualityValid $curve $claim = true)) (← `(by decide +kernel))
  let defined := rootIdent (base ++ `abc_quality_defined)
  checked (base ++ `abc_quality_defined)
    (← `((($curve).baseChange ℚ).j ≠ 0 ∧ (($curve).baseChange ℚ).j ≠ 1728))
    (← `(Certification.abc_quality_defined_of_check $curve $claim $valid))
  checked (base ++ `abc_quality)
    (← `(|(($curve).baseChange ℚ).abcQuality $defined - (($claim).reported : ℝ)| ≤
      (($claim).error : ℝ)))
    (← `(Certification.abc_quality_of_check $curve $claim $valid $defined))

private def certifyTorsionInvariants (base : Name) (curve : Ident) : CommandElabM Unit := do
  let evidence ← bindStored base `torsionBound `torsion_bound (← `(TorsionBoundWitness))
  let claim ← bindStored base `torsion `torsion (← `(Nat))
  let some evidence := evidence |
    if claim.isSome then logInfo m!"Unverified {base} torsion: supply torsion_bound evidence"
    return
  let hcheck := rootIdent (base ++ `torsion_bound_value_valid)
  checked (base ++ `torsion_bound_value_valid)
    (← `(checkTorsionBound $curve ($evidence).firstPrime ($evidence).secondPrime
      ($evidence).bound = true)) (← `(by decide +kernel))
  let htorsion ← `(Nat.card (AddCommGroup.torsion (($curve).baseChange ℚ).toAffine.Point))
  let hbound := rootIdent (base ++ `torsion_bound)
  checked (base ++ `torsion_bound)
    (← `($htorsion ∣ ($evidence).bound ∧ 0 < ($evidence).bound))
    (← `(checkTorsionBound_correct $curve _ _ _ $hcheck))
  if let some value := claim then
    checked (base ++ `torsion_claim_consistent)
      (← `(0 < $value ∧ $value ∣ ($evidence).bound)) (← `(by decide +kernel))
  let bound := mkApp (mkConst ``TorsionBoundWitness.bound)
    (mkConst (base ++ `claimed_torsion_bound))
  let some n ← (liftTermElabM do (evalNat (← whnf bound)).run)
    | throwError "Expected a closed rational torsion bound"
  if n == 1 then
    let value ← match claim with
      | some value => `($value:ident)
      | none => `(1)
    checked (base ++ `torsion)
      (← `($htorsion = $value))
      (← `(by
        have h₁ : ($evidence).bound = 1 := by decide +kernel
        have hdiv : $htorsion ∣ 1 := h₁ ▸ ($hbound).1
        exact (Nat.dvd_one.mp hdiv).trans (by decide +kernel)))

/-- Verify a two-factor claim using the supplied points in invariant-factor order. -/
private def certifyTwoFactorTorsion (base : Name) (curve factors n orders : Ident) :
    CommandElabM Bool := do
  let some k ← (liftTermElabM do
    let expr ← Lean.Elab.Term.elabTerm (← `(List.getD $factors 1 0)) none
    (evalNat (← whnf expr)).run) | return false
  if k == 0 || k % 2 != 0 then return false
  let kTerm : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩
  let suitable ← liftTermElabM do
    let expected ← Lean.Elab.Term.elabTerm (← `([2, $kTerm]))
      (some (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)))
    let actual ← Lean.Elab.Term.elabTerm (← `($factors)) none
    let pointOrders ← Lean.Elab.Term.elabTerm (← `(($orders).take 2)) none
    let total ← Lean.Elab.Term.elabTerm (← `($n)) none
    return (← Meta.isDefEq actual expected) && (← Meta.isDefEq pointOrders expected) &&
      (← Meta.isDefEq total (mkNatLit (2 * k)))
  unless suitable do return false
  let point := rootIdent (base ++ `torsion_generators.point)
  let exactOrder := rootIdent (base ++ `torsion_generators.exact_order)
  let first ← `($point ⟨0, by decide +kernel⟩)
  let second ← `($point ⟨1, by decide +kernel⟩)
  let independent := rootIdent (base ++ `torsion_generators.independence_valid)
  checked (base ++ `torsion_generators.independence_valid)
    (← `(outsideCyclicCheck $first $second $kTerm = true)) (← `(by decide +kernel))
  let bound := rootIdent (base ++ `torsion_bound)
  let torsionType ← `(AddCommGroup.torsion (($curve).baseChange ℚ).toAffine.Point)
  let structureProof := rootIdent (base ++ `torsion_structure)
  checked (base ++ `torsion_structure)
    (← `($factors = [2, $kTerm] ∧
      ∃ e : ZMod 2 × ZMod $kTerm ≃+ $torsionType,
        (e (1, 0) : (($curve).baseChange ℚ).toAffine.Point) = $first ∧
        (e (0, 1) : (($curve).baseChange ℚ).toAffine.Point) = $second))
    (← `(by
      have hP : addOrderOf $first = 2 := $exactOrder ⟨0, by decide +kernel⟩
      have hQ : addOrderOf $second = $kTerm := $exactOrder ⟨1, by decide +kernel⟩
      have hk : 0 < $kTerm := by decide
      exact ⟨rfl, exists_torsion_addEquiv_two_factor hk hP hQ
        (outsideCyclicCheck_sound hk hQ $independent) ($bound).1⟩))
  checked (base ++ `torsion) (← `(Nat.card $torsionType = $n))
    (← `(by
      obtain ⟨e, -, -⟩ := ($structureProof).2
      calc
        Nat.card $torsionType = Nat.card (ZMod 2 × ZMod $kTerm) :=
          (Nat.card_congr e.toEquiv).symm
        _ = 2 * $kTerm := by simp only [Nat.card_prod, Nat.card_zmod]
        _ = $n := by decide +kernel))
  let secondOrder := rootIdent (base ++ `torsion_structure_second_order)
  emit (← `(def $secondOrder : Nat := $kTerm))
  checked (base ++ `torsion_structure_second_order_positive)
    (← `(0 < $secondOrder)) (← `(by decide +kernel))
  checked (base ++ `torsion_structure_first_factor_dvd_second)
    (← `(2 ∣ $secondOrder)) (← `(by decide +kernel))
  let firstGenerator := rootIdent (base ++ `torsion_structure_first_generator)
  let secondGenerator := rootIdent (base ++ `torsion_structure_second_generator)
  emit (← `(def $firstGenerator : (($curve).baseChange ℚ).toAffine.Point := $first))
  emit (← `(def $secondGenerator : (($curve).baseChange ℚ).toAffine.Point := $second))
  let equivalence := rootIdent (base ++ `torsion_structure_equiv)
  emit (← `(noncomputable def $equivalence : ZMod 2 × ZMod $kTerm ≃+
    $torsionType := Classical.choose ($structureProof).2))
  let imageWitness := rootIdent (base ++ `torsion_structure_image_witness)
  emit (← `(theorem $imageWitness :
    (($equivalence (1, 0) : (($curve).baseChange ℚ).toAffine.Point) = $firstGenerator) ∧
    (($equivalence (0, 1) : (($curve).baseChange ℚ).toAffine.Point) = $secondGenerator) :=
      Classical.choose_spec ($structureProof).2))
  checked (base ++ `torsion_structure_first_image)
    (← `(($equivalence (1, 0) : (($curve).baseChange ℚ).toAffine.Point) = $firstGenerator))
    (← `(by exact $imageWitness.1))
  checked (base ++ `torsion_structure_second_image)
    (← `(($equivalence (0, 1) : (($curve).baseChange ℚ).toAffine.Point) = $secondGenerator))
    (← `(by exact $imageWitness.2))
  let cardinality := rootIdent (base ++ `torsion)
  checked (base ++ `torsion_structure_cardinality)
    (← `(Nat.card $torsionType = 2 * $secondOrder))
    (← `(by rw [$cardinality:term]; rfl))
  return true

/-- Recover cyclic torsion when the verified bound matches an exact point order. -/
private def certifyCyclicTorsion (base : Name) (curve : Ident) : CommandElabM Unit := do
  let factors ← bindStored base `torsionStructure `torsion_structure (← `(List Nat))
  let orderName := base ++ `claimed_torsion
  let order := if (← getEnv).contains orderName then some (rootIdent orderName) else none
  let knownTrivial := (← getEnv).contains (base ++ `torsion)
  let some nInput ← (match order, factors with
    | some order, _ => pure (some (order : TSyntax `term))
    | none, some factors => some <$> `(($factors).prod)
    | none, none =>
      if knownTrivial then some <$> `(1) else pure none) | return
  let nName := base ++ `cyclic_torsion_order
  let n := rootIdent nName
  emit (← `(def $n : Nat := $nInput))
  if let some ofOrder := order then
    if let some factors := factors then
      checked (base ++ `torsion_structure_order_consistent)
        (← `(($factors).prod = $ofOrder)) (← `(by decide +kernel))
  let exponent ← if let some factors := factors then do
    checked (base ++ `torsion_structure_normalized)
      (← `((($factors).all (fun factor => decide (1 < factor)) = true) ∧
        ($factors).Pairwise (fun a b => a ∣ b))) (← `(by decide +kernel))
    `(($factors).getLastD 1)
  else `($n)
  let ordersName := base ++ `torsion_generators.orders
  if (← getEnv).contains ordersName then
    let orders := rootIdent ordersName
    checked (base ++ `torsion_point_orders_consistent)
      (← `(($orders).all (fun order => decide (order ∣ $exponent)) = true))
      (← `(by decide +kernel))
  unless (← getEnv).contains (base ++ `torsion_bound) do
    if factors.isSome then
      logInfo m!"Unverified {base} torsion_structure: supply a checked torsion bound"
    return
  let candidate := rootIdent (base ++ `claimed_torsion_bound)
  if factors.isSome then
    checked (base ++ `torsion_structure_divisor_consistent)
      (← `(0 < $n ∧ $n ∣ ($candidate).bound)) (← `(by decide +kernel))
  let equalBound ← liftTermElabM do
    let claimedBound ← Lean.Elab.Term.elabTerm (← `(($candidate).bound)) (some (mkConst ``Nat))
    Meta.isDefEq (mkConst nName) claimedBound
  unless equalBound do
    logInfo m!"Unverified {base} cyclic torsion: the verified bound must match the claimed order"
    return
  let trivial ← liftTermElabM <| Meta.isDefEq (mkConst nName) (mkNatLit 1)
  let pointOrder := base ++ `torsion_generators.exact_order
  unless trivial do
    unless (← getEnv).contains pointOrder do
      logInfo m!"Unverified {base} cyclic torsion: supply the exact order of the first point"
      return
    let orders := rootIdent (base ++ `torsion_generators.orders)
    let hasGeneratorOrder ← liftTermElabM do
      let observed ← Lean.Elab.Term.elabTerm (← `(($orders).head?)) none
      let expected ← Lean.Elab.Term.elabTerm (← `(some $n)) none
      Meta.isDefEq observed expected
    unless hasGeneratorOrder do
      if let some factors := factors then
        if ← certifyTwoFactorTorsion base curve factors n orders then return
      logInfo m!"Unverified {base} cyclic torsion: first point order must match the claimed order"
      return
  if let some factors := factors then
    checked (base ++ `torsion_structure_claim_valid)
      (← `($factors = if $n = 1 then [] else [$n])) (← `(by decide +kernel))
  let torsionType ← `(AddCommGroup.torsion (($curve).baseChange ℚ).toAffine.Point)
  let bound := rootIdent (base ++ `torsion_bound)
  let (point, orderProof) ← if trivial then
    pure (← `((0 : (($curve).baseChange ℚ).toAffine.Point)), ← `(addOrderOf_zero))
  else
    let first := rootIdent (base ++ `torsion_generators.point)
    let exactOrder := rootIdent pointOrder
    pure (← `($first ⟨0, by decide +kernel⟩), ← `($exactOrder ⟨0, by decide +kernel⟩))
  let generator := rootIdent (base ++ `cyclic_torsion_generator)
  emit (← `(def $generator : (($curve).baseChange ℚ).toAffine.Point := $point))
  let horder := rootIdent (base ++ `cyclic_torsion_order_valid)
  checked (base ++ `cyclic_torsion_order_valid)
    (← `(addOrderOf $generator = $n)) orderProof
  unless (← getEnv).contains (base ++ `torsion) do
    checked (base ++ `torsion) (← `(Nat.card $torsionType = $n))
      (← `(torsion_card_eq_of_order_dvd ($bound).2 $horder ($bound).1))
  if let some factors := factors then
    let hf := rootIdent (base ++ `torsion_structure_claim_valid)
    checked (base ++ `torsion_structure)
      (← `($factors = (if $n = 1 then [] else [$n]) ∧
        ∃ e : ZMod $n ≃+ $torsionType,
          (e 1 : (($curve).baseChange ℚ).toAffine.Point) = $generator))
      (← `(⟨$hf, exists_torsion_addEquiv_of_order_dvd ($bound).2 $horder ($bound).1⟩))

/-- Prove that a checked cyclic or two-factor presentation is generated by the submitted family. -/
private def certifyTorsionGeneration (base : Name) (curve : Ident) : CommandElabM Unit := do
  let child := base ++ `torsion_generators
  let env ← getEnv
  let twoFactor := env.contains (base ++ `torsion_structure_equiv)
  let cyclic := env.contains (base ++ `cyclic_torsion_order_valid)
  unless cyclic || twoFactor do return
  unless env.contains (child ++ `point) do return
  let point := rootIdent (child ++ `point)
  let hasOrders := env.contains (child ++ `point_mem_torsion)
  unless hasOrders do
    let coordinates := rootIdent (child ++ `coordinates)
    let empty ← liftTermElabM do
      let size ← Term.elabTerm (← `(($coordinates).length)) (some (mkConst ``Nat))
      Meta.isDefEq size (mkNatLit 0)
    unless empty do return
  let contains ← if hasOrders then
    `(by
      intro p hp
      obtain ⟨i, hi⟩ := hp
      exact hi ▸ $(rootIdent (child ++ `point_mem_torsion)) i)
  else
    `(by
      rintro _ ⟨i, _⟩
      exact i.elim0)
  let target ← `(AddSubgroup.closure (Set.range $point) =
    AddCommGroup.torsion (($curve).baseChange ℚ).toAffine.Point)
  if twoFactor then
    let structureProof := rootIdent (base ++ `torsion_structure)
    checked (child ++ `generates_torsion) target (← `(by
      obtain ⟨e, h₁, h₂⟩ := ($structureProof).2
      refine Certification.closure_eq_of_twoFactor_presentation e $contains ?_ ?_
      · rw [h₁]
        exact AddSubgroup.subset_closure ⟨⟨0, by decide +kernel⟩, rfl⟩
      · rw [h₂]
        exact AddSubgroup.subset_closure ⟨⟨1, by decide +kernel⟩, rfl⟩))
  else
    let bound := rootIdent (base ++ `torsion_bound)
    let horder := rootIdent (base ++ `cyclic_torsion_order_valid)
    checked (child ++ `generates_torsion) target (← `(by
      obtain ⟨e, he⟩ := exists_torsion_addEquiv_of_order_dvd ($bound).2 $horder ($bound).1
      refine Certification.closure_eq_of_cyclic_presentation e $contains ?_
      rw [he]
      first
      | exact AddSubgroup.zero_mem _
      | exact AddSubgroup.subset_closure ⟨⟨0, by decide +kernel⟩, rfl⟩))

/-- Build one invariant-factor presentation indexed by the original submitted family. -/
private def certifyTorsionPresentation (base : Name) (curve : Ident) : CommandElabM Unit := do
  let env ← getEnv
  let sourceName := base ++ `torsion_generators.point
  let source ← if env.contains sourceName then
    `($(rootIdent sourceName))
  else
    `((Fin.elim0 : Fin 0 → (($curve).baseChange ℚ).toAffine.Point))
  let evidence ← if env.contains (base ++ `torsion_structure_equiv) then do
    let second := rootIdent (base ++ `torsion_structure_second_order)
    let divides := rootIdent (base ++ `torsion_structure_first_factor_dvd_second)
    let structureProof := rootIdent (base ++ `torsion_structure)
    `(TorsionPresentation.ofTwoFactor $source ⟨0, by decide +kernel⟩
      ⟨1, by decide +kernel⟩ $second (by decide +kernel) $divides ($structureProof).2)
  else if env.contains (base ++ `cyclic_torsion_order_valid) then do
    let orderName := base ++ `cyclic_torsion_order
    let order := rootIdent orderName
    let trivial ← liftTermElabM <| Meta.isDefEq (mkConst orderName) (mkNatLit 1)
    if trivial then
      `(TorsionPresentation.ofTrivial $source $(rootIdent (base ++ `torsion)))
    else
      let bound := rootIdent (base ++ `torsion_bound)
      let horder := rootIdent (base ++ `cyclic_torsion_order_valid)
      `(TorsionPresentation.ofCyclic $source ⟨0, by decide +kernel⟩ $order (by decide +kernel)
        (exists_torsion_addEquiv_of_order_dvd ($bound).2 $horder ($bound).1))
  else return
  let name := base ++ `torsion_presentation
  emit (← `(def $(rootIdent name) : TorsionPresentation $source := $evidence))
  auditAxioms name

/-- Check one optional equation invariant and return the corresponding proved value. -/
private def certifyTorsionPrimes (base : Name) : CommandElabM Unit := do
  let claim ← bindStored base `torsionPrimes `torsion_primes (← `(List Nat))
  let exactName := base ++ `torsion
  unless (← getEnv).contains exactName do
    if claim.isSome then
      logInfo m!"Unverified {base} torsion_primes: supply an exact torsion cardinality"
    return
  let some order ← (liftTermElabM do
    let type ← inferType (mkConst exactName)
    let some (_, _, value) := type.eq?
      | throwError "Expected an exact torsion cardinality"
    (evalNat (← whnf value)).run)
    | throwError "Expected a closed exact rational torsion order"
  let orderTerm : TSyntax `term := ⟨Syntax.mkNumLit (toString order)⟩
  let primes := rootIdent (base ++ `torsion_primes)
  emit (← `(def $primes : List Nat := (Nat.primeFactorsList $orderTerm).eraseDups))
  if let some claim := claim then
    checked (base ++ `torsion_primes_value_valid)
      (← `($claim = (Nat.primeFactorsList $orderTerm).eraseDups))
      (← `(by decide +kernel))
  let cardinality := rootIdent exactName
  let curve := rootIdent (base ++ `curve)
  let torsionType ← `(AddCommGroup.torsion (($curve).baseChange ℚ).toAffine.Point)
  let hasClaim := (← getEnv).contains (base ++ `claimed_torsion)
  let hasOrder := (← getEnv).contains (base ++ `cyclic_torsion_order)
  let hcardProof ← if hasClaim && hasOrder then
    let claimed := rootIdent (base ++ `claimed_torsion)
    let orderDef := rootIdent (base ++ `cyclic_torsion_order)
    `(by rw [$cardinality:term]; all_goals norm_num [$claimed:term, $orderDef:term])
  else if hasClaim then
    let claimed := rootIdent (base ++ `claimed_torsion)
    `(by rw [$cardinality:term]; all_goals norm_num [$claimed:term])
  else if (← getEnv).contains (base ++ `cyclic_torsion_order) then
    let claimed := rootIdent (base ++ `cyclic_torsion_order)
    `(by rw [$cardinality:term]; all_goals norm_num [$claimed:term])
  else
    `(by rw [$cardinality:term]; all_goals decide +kernel)
  checked (base ++ `torsion_primes_nodup) (← `(($primes).Nodup))
    (← `(by decide +kernel))
  checked (base ++ `torsion_primes_exact)
    (← `(∀ p, p ∈ $primes ↔ p.Prime ∧ p ∣ Nat.card $torsionType))
    (← `(by
      have hcard : $orderTerm = Nat.card $torsionType := $hcardProof
      intro p
      change p ∈ (Nat.primeFactorsList $orderTerm).eraseDups ↔
        p.Prime ∧ p ∣ Nat.card $torsionType
      rw [List.mem_eraseDups, Nat.mem_primeFactorsList (by decide), hcard]))

/-- Check one optional equation invariant and return the corresponding proved value. -/
private def certifyProofFact (base field label : Name) (proofs : Option Ident)
    (valueType lhs : TSyntax `term) : CommandElabM (Option (TSyntax `term)) := do
  let claimed ← bindStored base field label valueType
  let proved ← if let some facts := proofs then do
    let projection := rootIdent (``EllipticProofs ++ field)
    let selected ← `($projection $facts)
    if ← hasOptionalProof selected label then some <$> `(($selected).getD ⟨$lhs, rfl⟩)
    else pure none
  else pure none
  let value := rootIdent (base ++ Name.mkSimple s!"claimed_{label}")
  let some proof ← (match claimed, proved with
    | none, none => pure none
    | some _, none => some <$> `(by decide +kernel)
    | some _, some evidence => some <$> `(by exact ($evidence).property)
    | none, some evidence => do
      emit (← `(def $value : $valueType := ($evidence).val))
      some <$> `(($evidence).property)) | return none
  let equality := rootIdent (base ++ label)
  checked (base ++ label) (← `($lhs = $value)) proof
  some <$> `(some ⟨$value, $equality⟩)

/-- Package all supported checked equation invariants in one indexed record. -/
private def certifyProofFacts (base : Name) (curve : Ident)
    (input : Option (TSyntax `term)) : CommandElabM Unit := do
  let proofs ← input.mapM fun term => do
    let name := rootIdent (base ++ `proofs)
    emit (← `(def $name : EllipticProofs $curve := $term))
    pure name
  let b ← certifyProofFact base `bInvariants `b_invariants proofs
    (← `(Int × Int × Int × Int))
    (← `((($curve).b₂, ($curve).b₄, ($curve).b₆, ($curve).b₈)))
  let c ← certifyProofFact base `cInvariants `c_invariants proofs (← `(Int × Int))
    (← `((($curve).c₄, ($curve).c₆)))
  let d ← certifyProofFact base `discriminant `discriminant proofs (← `(Int))
    (← `(($curve).Δ))
  if d.isSome then
    let witness := rootIdent (base ++ `discriminant_witness)
    let value := rootIdent (base ++ `claimed_discriminant)
    let equality := rootIdent (base ++ `discriminant)
    emit (← `(def $witness : DiscriminantWitness ℤ := ⟨$curve, $value, $equality⟩))
  unless b.isNone && c.isNone && d.isNone do
    let missing ← `(none)
    let combined := rootIdent (base ++ `checked_facts)
    emit (← `(def $combined : EllipticProofs $curve :=
      { bInvariants := $(b.getD missing)
        cInvariants := $(c.getD missing)
        discriminant := $(d.getD missing) }))

/-- Check each supplied invariant against the actual curve, not an LMFDB label. -/
def certifyStoredInvariants (base : Name)
    (proofs : Option (TSyntax `term) := none) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  let hn := rootIdent (base ++ `nonsingular)
  certifyAbcQuality base curve
  certifyTorsionInvariants base curve
  certifyCyclicTorsion base curve
  certifyTorsionPresentation base curve
  certifyTorsionGeneration base curve
  certifyTorsionPrimes base
  certifyProofFacts base curve proofs
  certifyRankZeroRegulator base
  certifyPadicRegulator base curve
  if let some s ← bindStored base `discriminantSign `discriminant_sign (← `(Int)) then
    checked (base ++ `discriminant_sign) (← `(($curve).Δ.sign = $s)) (← `(by decide +kernel))
  if let some j ← bindStored base `jInvariant `j_invariant (← `(Rat)) then
    let hv := rootIdent (base ++ `j_invariant_value_valid)
    checked (base ++ `j_invariant_value_valid)
      (← `((($curve).c₄ : Rat) ^ 3 / (($curve).Δ : Rat) = $j)) (← `(by decide +kernel))
    checked (base ++ `j_invariant) (← `((($curve).baseChange ℚ).j = $j))
      (← `(Certification.j_invariant_of_exact_formula $curve $j $hv))
  if let some integral ← bindStored base `jIntegral `j_integral (← `(Bool)) then
    let hv := rootIdent (base ++ `j_integral_value_valid)
    checked (base ++ `j_integral_value_valid)
      (← `(Certification.jDenominatorIsOne $curve = $integral))
      (← `(by decide +kernel))
    checked (base ++ `j_integral)
      (← `(IsLocalization.IsInteger ℤ (($curve).baseChange ℚ).j ↔ $integral = true))
      (← `(Certification.j_integral_iff_of_check $curve $integral $hv))
  if let some claim ← bindStored base `potentialGoodReduction `potential_good_reduction
      (← `(Bool)) then
    let hv := rootIdent (base ++ `potential_good_reduction_value_valid)
    checked (base ++ `potential_good_reduction_value_valid)
      (← `(Certification.jDenominatorIsOne $curve = $claim)) (← `(by decide +kernel))
    checked (base ++ `potential_good_reduction)
      (← `(HasEverywherePotentialGoodReduction (($curve).baseChange ℚ) ↔ $claim = true))
      (← `(Certification.potential_good_reduction_iff_of_check $curve $claim $hv))
  let hasMinimality := (← optionalInput (base ++ `witness) `minimality).isSome
  let hasLocalData := (← optionalInput (base ++ `witness) `localData).isSome
  let m := rootIdent (base ++ `minimality)
  let hm := rootIdent (base ++ `minimality_valid)
  let d := rootIdent (base ++ `localData)
  let hd := rootIdent (base ++ `local_data_valid)
  certifyReductionInvariants base curve hn m hm hasMinimality hasLocalData
  if let some values ← bindStored base `badPrimes `bad_primes (← `(List Nat)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `bad_primes_value_valid)
      checked (base ++ `bad_primes_value_valid)
        (← `(($values).Nodup ∧ ($values).toFinset = ($m).primes.toFinset))
        (← `(by decide +kernel))
      let hp := rootIdent (base ++ `bad_primes)
      checked (base ++ `bad_primes)
        (← `(∀ p : Nat, p ∈ $values ↔ p.Prime ∧ (p : Int) ∣ ($curve).Δ))
        (← `(by
          intro p
          have he : p ∈ $values ↔ p ∈ ($m).primes := by
            rw [← List.mem_toFinset, ($hv).2, List.mem_toFinset]
          exact he.trans (Certification.minimal_prime_mem_iff $curve $m $hm p)))
      checked (base ++ `bad_reduction_primes)
        (← `(∀ (p : Nat) [Fact p.Prime], p ∈ $values ↔
          ¬ (($curve).baseChange (ZMod p)).IsElliptic))
        (← `(by intro p hp; exact Certification.bad_reduction_prime_iff $curve $values $hp p))
    else
      logInfo m!"Unverified {base} bad_primes: supply minimality evidence"
  if let some n ← bindStored base `numBadPrimes `num_bad_primes (← `(Nat)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `num_bad_primes_value_valid)
      checked (base ++ `num_bad_primes_value_valid)
        (← `(($m).primes.toFinset.card = $n)) (← `(by decide +kernel))
      checked (base ++ `num_bad_primes)
        (← `(($curve).Δ.natAbs.primeFactors.card = $n)) (← `(by
          rw [← Certification.minimal_primes_toFinset $curve $hn $m $hm]
          exact $hv))
    else
      logInfo m!"Unverified {base} num_bad_primes: supply minimality evidence"
  if let some a ← bindStored base `minimalDiscriminantAbs `minimal_discriminant_abs
      (← `(Nat)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `abs_discriminant_value_valid)
      checked (base ++ `abs_discriminant_value_valid)
        (← `(($curve).Δ.natAbs = $a)) (← `(by decide +kernel))
      checked (base ++ `minimal_discriminant_abs)
        (← `(WeierstrassCurve.IsGlobalMinimal (NumberField.RingOfIntegers ℚ)
          (($curve).baseChange ℚ) ∧ ($curve).Δ.natAbs = $a))
        (← `(Certification.minimal_discriminant_abs_of_witness $curve $m $hm $a $hv))
    else
      logInfo m!"Unverified {base} absD: supply minimality evidence"
  if let some values ← bindStored base `dirichletCoefficients `dirichlet_coefficients
      (← `(List Int)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `dirichlet_coefficients_value_valid)
      checked (base ++ `dirichlet_coefficients_value_valid)
        (← `(modelCoefficients $curve ($values).length = $values)) (← `(by decide +kernel))
      checked (base ++ `dirichlet_coefficients)
        (← `((List.range ($values).length).map
          (fun n => (($curve).baseChange ℚ).LFunction (n + 1)) = $values))
        (← `(Certification.coefficients_of_minimal_witness $curve $hn $m $hm $values $hv))
    else
      logInfo m!"Unverified {base} anlist: supply minimality evidence"
  let conductor ← bindStored base `conductor `conductor (← `(Nat))
  let checkedConductor := if hasMinimality && hasLocalData then conductor else none
  if let some n := checkedConductor then
    let hv := rootIdent (base ++ `conductor_claim_valid)
    checked (base ++ `conductor_claim_valid) (← `(wildLevelFast $curve $d = $n))
      (← `(by decide +kernel))
    checked (base ++ `conductor)
      (← `((Modularity.modularWitness $curve $hn).level = $n))
      (← `(Certification.conductor_of_arithmetic_witness $curve $hn $m $hm $d $hd $n $hv)) true
  else if conductor.isSome then
    logInfo m!"Unverified {base} conductor: supply minimality and localData evidence"
  certifyConductorValuations base curve hn checkedConductor
  if let some w ← bindStored base `rootNumber `root_number (← `(Int)) then
    if hasMinimality && hasLocalData then
      let hv := rootIdent (base ++ `root_number_claim_valid)
      checked (base ++ `root_number_claim_valid) (← `(wildSignFast $curve $d = $w))
        (← `(by decide +kernel))
      checked (base ++ `root_number)
        (← `((Modularity.modularWitness $curve $hn).rootNumber = $w))
        (← `(Certification.root_number_of_arithmetic_witness
          $curve $hn $m $hm $d $hd $w $hv)) true
    else
      logInfo m!"Unverified {base} root_number: supply minimality and localData evidence"

end VerifiedLcalc.CertifyEC
