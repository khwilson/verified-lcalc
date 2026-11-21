import CertifiedCurves.Invariants

theorem imported_j_invariant : (Invariants37.curve.baseChange ℚ).j = 110592 / 37 :=
  Invariants37.j_invariant

theorem imported_bad_prime : 37 ∈ Invariants37.claimed_bad_primes :=
  (Invariants37.bad_primes 37).mpr ⟨by decide, by decide⟩

theorem imported_coefficient_prefix :
    (List.range 8).map (fun n => (Invariants37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0] := Invariants37.dirichlet_coefficients

#print axioms imported_j_invariant
#print axioms imported_bad_prime
#print axioms imported_coefficient_prefix
