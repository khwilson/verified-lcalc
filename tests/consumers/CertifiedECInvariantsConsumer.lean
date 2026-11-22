import CertifiedCurves.Invariants

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

open VerifiedLcalc VerifiedLcalc.EllipticCurve

example : ExactAdditiveKodaira.kodaira_terminals.map (fun fact =>
    ((fact.1 : ℕ), fact.2.translation, fact.2.symbol.val)) =
    [(5, (0, 0, 2), TauCeti.ReductionSymbol.II)] := rfl

/-- The compiled terminal witness proves type II at 5 for LMFDB 50.b3. -/
theorem imported_additive_kodaira :
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    (ExactAdditiveKodaira.curve.baseChange ℚ).reductionSymbol (RationalLocalRing 5) =
      TauCeti.ReductionSymbol.II := by
  let row : LocalReductionClaim :=
    { prime := 5, kodairaSymbol := some 2, kodairaTerminal := some (0, 0, 2) }
  obtain ⟨hp, code, fact, _, hcode, hsymbol⟩ :=
    ExactAdditiveKodaira.kodaira_terminal_symbols row (by decide +kernel) (0, 0, 2) rfl
  have hcode' : code = 2 := by simpa [row] using hcode.symm
  subst code
  have hsymbol' : fact.symbol.val = TauCeti.ReductionSymbol.II := by
    exact congrArg Subtype.val (Option.some.inj hsymbol.symm)
  exact fact.reductionSymbol_eq.trans hsymbol'

example : VerifiedLcalc.EllipticProofs ProofCarrying37.curve := ProofCarrying37.checked_facts

example : ProofCarrying37.checked_facts.bInvariants.map Subtype.val = some (0, -2, 1, -1) := rfl
example : ProofCarrying37.checked_facts.cInvariants.map Subtype.val = some (48, -216) := rfl
example : ProofCarrying37.checked_facts.discriminant.map Subtype.val = some 37 := rfl

example : Invariants37.checked_facts.bInvariants.isSome = true := rfl
example : Invariants37.checked_facts.cInvariants.isSome = true := rfl
example : Invariants37.checked_facts.discriminant.isSome = true := rfl
