/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import VerifiedLcalc.Upstream.TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS
import Mathlib.Tactic.LinearCombination

/-!
# The complement of a normalised EDS at a general multiple

Mathlib defines `complEDS b c d k` to witness `_root_.normEDS b c d k ∣ _root_.normEDS b c d (n * k)`, but
proves the witnessing identity `_root_.normEDS b c d k * complEDS b c d k n = _root_.normEDS b c d (n * k)`
only at `k = 2`, as `normEDS_mul_complEDS₂`. This file proves it at every `k`, **unconditionally**:
the induction runs on a nonzerodivisor hypothesis, which is then discharged over `ℤ[B, C, D]` and
specialised away.

That identity is the second conjunct of the TODO Mathlib records at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:70`, "prove that `_root_.normEDS` satisfies
`IsEllipticDvdSequence`". `NormEDS.lean` discharges the first conjunct and names this one as a
slice of its own.

## Main results

* `normEDS_mul_complEDS`: the same identity with **no hypothesis at all**, obtained from the
  private nonzerodivisor form by specialising from the universal parameters.
* `normEDS_dvd_normEDS_mul`: the divisibility it witnesses, `_root_.normEDS b c d k ∣ _root_.normEDS b c d
  (n * k)` — Mathlib's `normEDS_dvd_normEDS_two_mul` at an arbitrary multiplier.
* `isDvdSequence_normEDS`: the same fact as `IsDvdSequence (_root_.normEDS b c d)`, the predicate form
  in which Mathlib's TODO states this conjunct.

## Implementation notes

The nonzerodivisor hypothesis is what the induction consumes. The odd step derives the identity
multiplied through by `_root_.normEDS b c d k`, and cancelling that factor is the only use of `hk`; the
even step and both base cases are unconditional. It is removable by specialising from the
universal parameters, where the sequence is a nonzerodivisor at every **nonzero** index — the
route `NormEDS.lean` takes for `isEllipticNet_normEDS`. It vanishes at `k = 0`, so that case is
split off first and closed by `simp`. The route is now available: `universalNormEDS_ne_zero`
(`NormEDS.lean`) gives the nonvanishing, and `mem_nonZeroDivisors_of_ne_zero` turns it into the
hypothesis this induction consumes, `ℤ[B, C, D]` being a domain.

The elliptic relation is instantiated once, at `ER((j + 2) * k, 1, (j + 1) * k, 0)`. Its middle
term is then `W((2 * j + 3) * k) * W k`, the odd step's right-hand side times the factor to be
cancelled, and its two outer terms are the products the recursion produces.

`IsEllipticNet.rel` holds its indices unnormalised — `W (p + q + s)` at `s = 0`, `W (q - r)`
where the goal has `W (r - q)` — so the instance and the goal disagree on the *arguments* of
`_root_.normEDS`, which are atoms to `ring`. `linear_combination`'s default `ring1` closer does not
descend into an atom's arguments, so the norm is switched to `ring_nf`, which does. That covers
every index mismatch except the reflected one: `W (1 - x) = -W (x - 1)` is `normEDS_neg`, a fact
about the sequence rather than about `ℤ`, and is the single rewrite done by hand.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @ 9fec8eba7652` — the revision
`TauCetiRoadmap/EllipticCurves/README.md` pins for the NagellLutz project. Source declaration
`normEDS_mul_complEDS_of_mem` (`:1324`), `private` in both, the name gaining Mathlib's full
`_of_mem_nonZeroDivisors` suffix. The unconditional form adapts
`normEDS_mul_complEDS` (`:1339`) of that same file, under its source name. The source's divisor
reindexing `normEDS_mul_complEDS_div` (`:1350`) is ported here too, under its source name.

That reverses an earlier decision recorded in this file, and the reason is worth keeping: the
reindexing was left out because what consumers took from it was the divisibility, stated directly
here as `normEDS_dvd_normEDS_mul` and `isDvdSequence_normEDS`, so it had no call site. It has
nine now: the reduced-invariant cancellation in `ReducedInvariant.lean` reindexes one or two
complements through it in each of its six residue branches — once each for the residues `0`, `1`
and `5`, twice each for `2`, `3` and `4`. The source file's
header reads `Authors: David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header.

Three departures from the source, all forced by Mathlib having since absorbed the construction.

The source builds a *general* complement `EllSequence.compl'`, parametric in two sequences `W₁`
and `compl₂`, and obtains this identity by specialising a general lemma about it at
`W₁ := _root_.normEDS b c d` and `compl₂ := compl₂EDS b c d`. Mathlib's `complEDS'` is that construction
with exactly those two arguments already substituted, and Mathlib defines it directly rather than
through a general `compl`, so porting the general version would duplicate `complEDS'` without
making it derivable. The induction is run on `complEDS` itself instead.

The source's hypothesis `b ∈ R⁰` is dropped. It is needed there because the `n = 0` base case
goes through `IsEllSequence.zero`, which asks for `W 2 = b` to be a nonzerodivisor; Mathlib's
`normEDS_zero` gives `W 0 = 0` outright.

The source splits at the `ℕ` level and unfolds `compl'`, because it has no `ℤ`-level recurrence.
Mathlib states `complEDS_even` and `complEDS_odd` over `ℤ`, so the `Int.sign`/`Int.natAbs`
bookkeeping disappears and the even step is four rewrites.
-/

public section

open MvPolynomial NormEDSParam

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {b c d : R}

/- The unconditional complement identity is already in the pinned Mathlib. -/

/-- **A normalised EDS divides itself at every multiple of the index.** This is Mathlib's
`normEDS_dvd_normEDS_two_mul` with the doubling replaced by an arbitrary multiplier, the
complement supplying the cofactor. -/
theorem normEDS_dvd_normEDS_mul (b c d : R) (k n : ℤ) :
    _root_.normEDS b c d k ∣ _root_.normEDS b c d (n * k) :=
  ⟨_, (normEDS_mul_complEDS (b := b) (c := c) (d := d) k n).symm⟩

/-- **A normalised EDS is a divisibility sequence.** This is the second conjunct of the TODO
Mathlib records for `_root_.normEDS`, in the predicate form the TODO states it in; the first conjunct is
`isEllipticSequence_normEDS`. -/
theorem isDvdSequence_normEDS (b c d : R) : IsDvdSequence (_root_.normEDS b c d) := by
  rintro k _ ⟨n, rfl⟩
  rw [mul_comm]
  exact normEDS_dvd_normEDS_mul b c d k n

/-- **The complement at a divisor.** When `k ∣ n`, the `k`-complement at index `n / k` multiplies
`_root_.normEDS b c d k` back up to `_root_.normEDS b c d n`. This is the divisor-indexed form of
`normEDS_mul_complEDS`, which is stated at `n * k`; `Int.ediv_mul_cancel` is
what converts between the two. Unconditional, like the identity it rests on.

Its one consumer is `IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul`; the module
docstring records how often each of its residue branches goes through this. -/
theorem normEDS_mul_complEDS_div (k n : ℤ) (hn : k ∣ n) :
    _root_.normEDS b c d k * complEDS b c d k (n / k) = _root_.normEDS b c d n := by
  rw [normEDS_mul_complEDS, Int.ediv_mul_cancel hn]
