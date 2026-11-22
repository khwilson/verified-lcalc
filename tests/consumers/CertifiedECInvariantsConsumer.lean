import CertifiedCurves.Invariants
import Lean

/-! Reuse invariant certificates from a compiled certificate module. -/

theorem imported_j_invariant : (Invariants37.curve.baseChange ℚ).j = 110592 / 37 :=
  Invariants37.j_invariant

theorem imported_bad_prime : 37 ∈ Invariants37.claimed_bad_primes :=
  (Invariants37.bad_primes 37).mpr ⟨by decide, by decide⟩

theorem imported_coefficient_prefix :
    (List.range 8).map (fun n => (Invariants37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0] := Invariants37.dirichlet_coefficients

theorem imported_semistability : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (Invariants37.curve.baseChange ℚ) := Invariants37.semistable.mpr rfl

theorem imported_squarefree_discriminant : Squarefree Invariants37.curve.Δ.natAbs :=
  Invariants37.squarefree_discriminant.mpr rfl

theorem imported_local_invariants (row : VerifiedLcalc.LocalReductionClaim)
    (h : row ∈ Invariants37.claimed_local_invariants) :
    row.Spec Invariants37.curve := Invariants37.local_invariants row h

example : VerifiedLcalc.DiscriminantWitness ℤ := ProofCarrying37.discriminant_witness

example : ProofCarrying37.discriminant_witness.curve.Δ = 37 :=
  ProofCarrying37.discriminant_witness.discriminant_eq

example : FileProofCarrying37.curve.Δ = 37 := FileProofCarrying37.discriminant

example : VerifiedLcalc.EllipticProofs ProofCarrying37.curve := ProofCarrying37.checked_facts

example : ProofCarrying37.checked_facts.bInvariants.map Subtype.val = some (0, -2, 1, -1) := rfl
example : ProofCarrying37.checked_facts.cInvariants.map Subtype.val = some (48, -216) := rfl
example : ProofCarrying37.checked_facts.discriminant.map Subtype.val = some 37 := rfl

example : Invariants37.checked_facts.bInvariants.isSome = true := rfl
example : Invariants37.checked_facts.cInvariants.isSome = true := rfl
example : Invariants37.checked_facts.discriminant.isSome = true := rfl

/-- A newly compiled finite projection of a certificate that also checked a modular conductor. -/
theorem imported_aggregate_discriminant :
    Invariants37.curve.Δ = (Invariants37.certificate.equationFacts.discriminant.getD
      ⟨Invariants37.curve.Δ, rfl⟩).val :=
  (Invariants37.certificate.equationFacts.discriminant.getD ⟨Invariants37.curve.Δ, rfl⟩).property

/-- The conductor projection takes an explicit realization of the same curve. -/
theorem imported_aggregate_conductor
    (model : VerifiedLcalc.Modularity.ArithmeticModularRealization Invariants37.curve) :
    model.level = 37 :=
  (Invariants37.certificate.arithmetic.modular.conductor.get (by decide +kernel)).property model

/-- The finite local data carry only the fields covered by their finite proof. -/
theorem imported_aggregate_finite_local_row (row : VerifiedLcalc.LocalReductionClaim)
    (h : row ∈ ((Invariants37.certificate.arithmetic.minimalModel.get
      (by decide +kernel)).localRows.get (by decide +kernel)).val) :
    row.conductorValuation = none ∧ row.kodairaSymbol = none ∧ row.Spec Invariants37.curve :=
  ((Invariants37.certificate.arithmetic.minimalModel.get
    (by decide +kernel)).localRows.get (by decide +kernel)).property row h

/-- The supplied local exponent is accessible through the conditional family. -/
theorem imported_aggregate_conductor_valuation
    (model : VerifiedLcalc.Modularity.ArithmeticModularRealization Invariants37.curve) :
    model.level.factorization 37 = 1 :=
  ((Invariants37.certificate.arithmetic.modular.conductorValuations.get
    (by decide +kernel)).property model (37, 1) (by decide +kernel)).2

open Lean Elab Command in
run_cmd do
  let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
  let conductorAxioms ← liftTermElabM <| Lean.collectAxioms ``Invariants37.conductor
  unless conductorAxioms.contains modularity do
    throwError "The mixed certificate lacks its expected modularity-dependent conductor"
  for fact in [``imported_aggregate_discriminant, ``imported_aggregate_conductor,
      ``imported_aggregate_conductor_valuation, ``imported_aggregate_finite_local_row] do
    let finiteAxioms ← liftTermElabM <| Lean.collectAxioms fact
    for name in finiteAxioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Unexpected aggregate axiom in {fact}: {name}"

example : Invariants37.certificate.rational.jInvariant.map Subtype.val = some (110592 / 37) := rfl
example : Invariants37.certificate.rational.discriminantSign.map Subtype.val = some 1 := rfl
example : ProofCarrying37.certificate.equationFacts.discriminant.map Subtype.val = some 37 := rfl

certify_ec ReusedAggregateFacts from
  { equation := Invariants37.certificate.equation, cInvariants := some (48, -216) }
  with_proofs Invariants37.certificate.equationFacts

example : ReusedAggregateFacts.certificate.equationFacts.bInvariants.map Subtype.val =
    some (0, -2, 1, -1) := rfl
example : ReusedAggregateFacts.certificate.equationFacts.cInvariants.map Subtype.val =
    some (48, -216) := rfl
