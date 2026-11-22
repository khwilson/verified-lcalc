/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.ArithmeticFacts
public import VerifiedLcalc.Tactic.CertifyECCommon

/-! # Assemble checked arithmetic fields

Reuse the kernel-checked declarations from the existing certificate pipeline.
Modular facts take an explicit realization argument.
-/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command EllipticCurve

private def simpleArithmeticFact (base value proof : Name) : CommandElabM (TSyntax `term) := do
  if (← getEnv).contains (base ++ proof) then
    `(some ⟨$(rootIdent (base ++ value)), $(rootIdent (base ++ proof))⟩)
  else
    `(none)

private def modularFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let env ← getEnv
  let gm := rootIdent (base ++ `global_minimal)
  let data := rootIdent (base ++ `localData)
  let hdata := rootIdent (base ++ `local_data_valid)
  let n := rootIdent (base ++ `claimed_conductor)
  let w := rootIdent (base ++ `claimed_root_number)
  let hn := rootIdent (base ++ `conductor_claim_valid)
  let hw := rootIdent (base ++ `root_number_claim_valid)
  let levelProof ← `(fun M =>
    (M.wildLevel_eq $gm $data $hdata).trans ((wildLevel_eq_fast $curve $data).trans $hn))
  let conductor ← if env.contains (base ++ `conductor) then
    `(some ⟨$n, $levelProof⟩)
  else `(none)
  let rootNumber ← if env.contains (base ++ `root_number) then
    `(some ⟨$w, fun M =>
      (M.wildSign_eq $gm $data $hdata).trans ((wildSign_eq_fast $curve $data $hdata).trans $hw)⟩)
  else `(none)
  let exponents ← if env.contains (base ++ `conductor_valuation) then
    let values := rootIdent (base ++ `claimed_conductor_valuations)
    let hv := rootIdent (base ++ `conductor_valuation_value_valid)
    `(some ⟨$values, by
      intro M row hrow
      have he : ∀ A : Modularity.ArithmeticModularRealization $curve, A.level = $n := $levelProof
      rw [he M]
      exact Certification.factorization_of_prime_exponent_check _ _ _
        (List.all_eq_true.mp $hv row hrow)⟩)
  else `(none)
  `(({
    conductor := $conductor
    rootNumber := $rootNumber
    conductorValuations := $exponents } : ModularArithmeticFacts $curve))

private def minimalModelFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let env ← getEnv
  unless env.contains (base ++ `global_minimal) do return ← `(none)
  let m := rootIdent (base ++ `minimality)
  let hm := rootIdent (base ++ `minimality_valid)
  let hglobal := rootIdent (base ++ `global_minimal)
  let absD ← simpleArithmeticFact base `claimed_minimal_discriminant_abs `minimal_discriminant_abs
  let semistable ← simpleArithmeticFact base `claimed_semistable `semistable
  let squarefree ← simpleArithmeticFact base
    `claimed_squarefree_discriminant `squarefree_discriminant
  let numBadPrimes ← simpleArithmeticFact base `claimed_num_bad_primes `num_bad_primes
  let badPrimes ← if env.contains (base ++ `bad_reduction_primes) then
    let hv := rootIdent (base ++ `bad_primes_value_valid)
    `(some ⟨$(rootIdent (base ++ `claimed_bad_primes)), ($hv).1,
      $(rootIdent (base ++ `bad_primes)), $(rootIdent (base ++ `bad_reduction_primes))⟩)
  else `(none)
  let localRows ← if env.contains (base ++ `local_invariants) then
    let values := rootIdent (base ++ `claimed_local_invariants)
    let hrows := rootIdent (base ++ `local_invariants)
    `(some ⟨($values).map (fun row => { row with conductorValuation := none }), by
      intro row hr
      obtain ⟨input, hinput, hEq⟩ := List.mem_map.mp hr
      subst row
      exact ⟨rfl, $hrows input hinput⟩⟩)
  else `(none)
  `(some ({
    minimality := ⟨$m, $hm, $hglobal⟩
    minimalDiscriminantAbs := $absD
    semistable := $semistable
    squarefreeDiscriminant := $squarefree
    badPrimes := $badPrimes
    numBadPrimes := $numBadPrimes
    localRows := $localRows } : MinimalModelArithmeticFacts $curve))

/-- Package verified values and their proofs without retaining unchecked local fields. -/
def arithmeticFactsTerm (base : Name) (curve : Ident) : CommandElabM (TSyntax `term) := do
  let witness := rootIdent (base ++ `witness)
  let minimalModel ← minimalModelFactsTerm base curve
  let localData ← simpleArithmeticFact base `localData `local_data_valid
  let pgr ← simpleArithmeticFact base `claimed_potential_good_reduction `potential_good_reduction
  let ap ← if (← optionalInput (base ++ `witness) `primeCoefficients).isSome then
    `(some ⟨($witness).primeCoefficients.getD [], $(rootIdent (base ++ `ap_correct))⟩)
  else `(none)
  let an ← simpleArithmeticFact base `claimed_dirichlet_coefficients `dirichlet_coefficients
  let modular ← modularFactsTerm base curve
  `(({
    minimalModel := $minimalModel
    localData := $localData
    potentialGoodReduction := $pgr
    primeCoefficients := $ap
    dirichletCoefficients := $an
    modular := $modular } : ArithmeticFacts $curve))

end VerifiedLcalc.CertifyEC
