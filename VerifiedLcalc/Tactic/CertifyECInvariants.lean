module

public import VerifiedLcalc.Certification.StoredInvariants
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

/-- Check each supplied invariant against the actual curve, not an LMFDB label. -/
def certifyStoredInvariants (base : Name) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  let hn := rootIdent (base ++ `nonsingular)
  certifyTorsionInvariants base curve
  if let some b ← bindStored base `bInvariants `b_invariants (← `(Int × Int × Int × Int)) then
    checked (base ++ `b_invariants)
      (← `((($curve).b₂, ($curve).b₄, ($curve).b₆, ($curve).b₈) = $b))
      (← `(by decide +kernel))
  if let some c ← bindStored base `cInvariants `c_invariants (← `(Int × Int)) then
    checked (base ++ `c_invariants) (← `((($curve).c₄, ($curve).c₆) = $c))
      (← `(by decide +kernel))
  if let some d ← bindStored base `discriminant `discriminant (← `(Int)) then
    checked (base ++ `discriminant) (← `(($curve).Δ = $d)) (← `(by decide +kernel))
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
