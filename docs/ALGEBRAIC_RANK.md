# Infinite order and algebraic rank

`certify_ec` checks membership of the supplied integer points. The follow-up
commands check stronger facts about those same points. Import
`VerifiedLcalc.Tactic.CertifyEC`; see `CertifiedCurves/Direct.lean` for a compiled
example.

```lean
certify_ec Points37 from
  { equation := ⟨0, 0, 1, -1, 0⟩
    integralCoordinates := some [(0, 0), (6, 14)] }

certify_ec_infinite_order Order37 for Points37 at 1

example : ¬ IsOfFinAddOrder Order37.point := Order37.infinite_order
example : (1 : Cardinal) ≤ Module.rank ℤ (Points37.curve.baseChange ℚ).toAffine.Point :=
  Order37.algebraic_rank_lower_bound
```

Indices are zero-based natural numbers and are bounds-checked. For the selected
integral point `(x,y)`, the checker sets `κ = 2y + a₁x + a₃` and proves
`κ ≠ 0 ∧ ¬ κ² ∣ 4Δ` using `decide +kernel`. TauCeti's proved long-model
Nagell–Lutz discriminant theorem says that torsion would force the opposite
disjunction. Its contrapositive gives infinite order, and Mathlib's integer
linear-independence and module-rank APIs give the rank bound. No modularity or
BSD assumption is involved.

This is a sufficient test. Failure rejects the command as inconclusive; it does
not prove torsion. For example `(0,0)` on 37.a1 fails this test even though it has
infinite order. The checker does not search for multiples with a stronger
obstruction.

## Families of points

For any number of points, supply a proof of their integer linear independence:

```lean
certify_ec_rank Rank37 for Points37 from [1] using (by
  apply LinearIndependent.of_subsingleton' (0 : Fin 1)
  intro a ha
  have hp : a • Order37.point = 0 := by
    simpa [Rank37.points, Rank37.indices, Order37.point, Order37.index] using ha
  by_contra hn
  exact Order37.infinite_order
    (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, hp⟩))
```

The command defines `Rank37.indices : List Nat` and
`Rank37.points : Fin Rank37.indices.length → E(ℚ)`. The supplied proof must have
type `LinearIndependent ℤ Rank37.points`. It exports `points_independent` and
`algebraic_rank_lower_bound`, the latter stating
`(Rank37.indices.length : Cardinal) ≤ Module.rank ℤ E(ℚ)`.
The point-family type uses the concrete numeral for its size, with
`point_count_eq` recording the kernel-checked equality to the input list's length.
The same interface accepts a family of any size. Duplicate or dependent points
cannot satisfy this obligation. Knowing that each point has infinite order is
insufficient: `P` and `2P` are dependent. Stored LMFDB generator or rank labels
are not independence proofs.

`EllipticCurve.independent_of_separating_matrix` supplies a reusable way to
discharge the independence obligation: provide a proved ℤ-linear map
`E(ℚ) →ₗ[ℤ] (Fin n → K)` for a characteristic-zero field `K`, then prove that
the matrix of the selected points' images has nonzero determinant. Mathlib's
determinant criterion and restriction of scalars give independence over ℤ.
`algebraic_rank_lower_bound_of_separating_matrix` combines that result with the
rank bound. A certified Néron–Tate pairing against fixed points can supply such
a map to real coordinates. The proof must connect the checked matrix entries
to the actual map values; a bare matrix cannot certify a rank.

The cardinal-valued rank avoids silently assuming Mordell–Weil finite
generation. `EllipticCurve.algebraic_finrank_lower_bound` supplies the
natural-valued version when a `Module.Finite ℤ E(ℚ)` instance is available.
This uses the actual Mathlib point group and module rank, with no duplicate
curve or rank definition.

## Remaining automation

Infinite-order checking and the arbitrary-family rank implication are proved.
For families of size two or greater, the caller currently supplies an ordinary
Lean independence proof. An automatic independence certificate from numerical
LMFDB data still needs a proved separation method, such as certified
Néron–Tate pairing bounds with a positive-definite Gram matrix, or a suitable
descent certificate. Approximate heights and regulators alone do not discharge
that obligation. TauCeti's `CanonicalHeight`, `MordellWeil/PointModTorsion`, and
`MordellWeil/Regulator` are the intended existing mathematical interfaces for
that extension; they have not been replaced with local height axioms.

All command failures roll back generated declarations. All accepted point and
rank theorems are audited against standard Lean axioms only. Compilation makes
them importable from `.olean` files; `CertifiedECPointsConsumer.lean` checks that
reuse path.
