module

public import VerifiedLcalc.Certification.AbcQuality
public import VerifiedLcalc.EllipticCurve.TorsionBound
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import Lean

/-! Internal stored-invariant checks dispatched exclusively by `certify_ec`.
Absent evidence leaves prerequisite-dependent claims explicitly unverified.
Finite equation invariants and minimality use only standard Lean axioms;
conductor/root-number identification retains the documented modularity axiom. -/

public meta section
namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta EllipticCurve NumberField

private def bindStored (base field label : Name) (type : TSyntax `term) :
    CommandElabM (Option Ident) := do
  let some input ← optionalInput (base ++ `witness) field | return none
  let value := rootIdent (base ++ Name.mkSimple s!"claimed_{label}")
  emit (← `(def $value : $type := $input))
  let w := rootIdent (base ++ `witness)
  let projection := rootIdent (``EllipticWitness ++ field)
  checked (base ++ Name.mkSimple s!"{label}_input_eq")
    (← `($projection $w = some $value)) (← `(by rfl))
  return some value

private def certifyReductionInvariants (base : Name) (curve m hm : Ident)
    (hasMinimality : Bool) : CommandElabM Unit := do
  let hglobal := rootIdent (base ++ `global_minimal)
  if let some claim ← bindStored base `semistable `semistable (← `(Bool)) then
    if hasMinimality then
      let hv := rootIdent (base ++ `semistable_value_valid)
      checked (base ++ `semistable_value_valid)
        (← `(decide (Int.gcd ($curve).Δ ($curve).c₄ = 1) = $claim)) (← `(by decide +kernel))
      checked (base ++ `semistable)
        (← `(WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
          (($curve).baseChange ℚ) ↔ $claim = true)) (← `(by
          rw [semistable_iff_coprime_of_isGlobalMinimal $curve $hglobal, ← $hv, decide_eq_true_eq]))
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
    if hasMinimality then
      let hv := rootIdent (base ++ `local_invariants_value_valid)
      checked (base ++ `local_invariants_value_valid)
        (← `(($rows).all (fun row => row.check $curve) = true)) (← `(by decide +kernel))
      checked (base ++ `local_invariants)
        (← `(∀ row ∈ $rows, LocalReductionClaim.Spec row $curve)) (← `(by
          intro row hrow
          exact LocalReductionClaim.check_correct row $curve $hglobal
            (List.all_eq_true.mp $hv row hrow)))
    else
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
  else if claim.isSome then
    logInfo m!"Unverified {base} torsion: the checked divisibility bound is not exact"

/-- Check one optional equation invariant and return the corresponding proved value. -/
private def certifyProofFact (base field label : Name) (proofs : Option Ident)
    (valueType lhs : TSyntax `term) : CommandElabM (Option (TSyntax `term)) := do
  let claimed ← bindStored base field label valueType
  let proved ← if let some facts := proofs then do
    let projection := rootIdent (``EllipticProofs ++ field)
    let selected ← `($projection $facts)
    let provided ← liftTermElabM do
      whnf (← Lean.Elab.Term.elabTerm selected none)
    match provided.getAppFn.constName? with
    | some ``Option.none => pure none
    | some ``Option.some => some <$> `(($selected).getD ⟨$lhs, rfl⟩)
    | _ => throwError "Expected closed optional proof data for {label}"
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
  let b ← certifyProofFact base `bInvariants `b_invariants proofs (← `(Int × Int × Int × Int))
    (← `((($curve).b₂, ($curve).b₄, ($curve).b₆, ($curve).b₈)))
  let c ← certifyProofFact base `cInvariants `c_invariants proofs (← `(Int × Int))
    (← `((($curve).c₄, ($curve).c₆)))
  let d ← certifyProofFact base `discriminant `discriminant proofs (← `(Int)) (← `(($curve).Δ))
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
  certifyProofFacts base curve proofs
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
  certifyReductionInvariants base curve m hm hasMinimality
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
  if let some a ← bindStored base `minimalDiscriminantAbs `minimal_discriminant_abs (← `(Nat)) then
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
        (← `(Certification.root_number_of_arithmetic_witness $curve $hn $m $hm $d $hd $w $hv)) true
    else
      logInfo m!"Unverified {base} root_number: supply minimality and localData evidence"

end VerifiedLcalc.CertifyEC
