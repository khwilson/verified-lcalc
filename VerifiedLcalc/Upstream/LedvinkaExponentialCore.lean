/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka

Runtime definitions extracted without algorithm changes from mathlib PR #45193,
commit 9c80a26d5b6a5b4ec14d6db0aba596463c6b281f.
Their correctness proofs are in LedvinkaExponential.lean. See README.md.
-/
module

public import Std
public import Init.Data.Dyadic

@[expose] public section

namespace Inclusion.IntervalDyadicReal

/-- Binary search for the highest set bit between two known bounds. -/
def expLogSearch : Nat → Nat → Nat → Nat → Nat
  | 0, _, lb, _ => lb
  | fuel + 1, n, lb, ub =>
    if ub ≤ lb + 1 then lb else
      let mid := (lb + ub) / 2
      if n >>> mid = 0 then expLogSearch fuel n lb mid
      else expLogSearch fuel n mid ub

/-- Bracket the highest set bit by doubling the shift count, then use binary search. -/
def expLogBracket : Nat → Nat → Nat → Nat
  | 0, _, ub => ub
  | fuel + 1, n, ub =>
    if n >>> ub = 0 then expLogSearch (ub.log2 + 1) n (ub / 2) ub
    else expLogBracket fuel n (2 * ub)

/-- The bit length, without the one-bit-per-call recursion of the logical `Nat.log2`. -/
def expBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else expLogBracket n n 1 + 1

/-- The sum of `⌊log₂ k⌋` for `1 ≤ k ≤ n`, a lower bound for `log₂ (n!)`. -/
def expFactorialBits (n : Nat) : Nat :=
  let k := n.log2
  k * (n + 1) + 2 - (1 <<< (k + 1))

/-- Search for the first term whose doubled bound is at most `2⁻prec`. -/
def expTermSearch (prec reduction : Nat) : Nat → Nat → Nat → Nat
  | 0, _, ub => ub
  | fuel + 1, lb, ub =>
    if ub ≤ lb + 1 then ub else
      let mid := (lb + ub) / 2
      if prec + 1 ≤ mid * reduction + expFactorialBits mid then
        expTermSearch prec reduction fuel lb mid
      else expTermSearch prec reduction fuel mid ub

/-- The first omitted Taylor term for an argument in `[0, 2⁻reduction]`, with `reduction ≥ 1`. -/
def expTerms (prec reduction : Nat) : Nat :=
  let ub := (prec + reduction) / reduction
  expTermSearch prec reduction (ub.log2 + 1) 0 ub

/-- Downward-rounded Taylor evaluation at `num / 2^exponent` by Horner's rule. -/
def expHorner (num exponent scale : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => expHorner num exponent scale n
      (scale + ((num * acc) >>> exponent) / (n + 1))

/-- Cache downward-rounded powers in descending order. -/
def expPowers (num exponent : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, result => result
  | n + 1, last, result =>
    let next := (last * num) >>> exponent
    expPowers num exponent n next (next :: result)

/-- Form a Taylor block with a common denominator from powers in descending order. -/
def expBlock : List Nat → Nat → Nat → Nat → Nat × Nat
  | [], _, den, acc => (den, acc)
  | p :: ps, n, den, acc =>
    let den := den * n
    expBlock ps (n - 1) den (acc + den * p)

/-- Evaluate Taylor blocks with one full-width multiplication and one division per block. -/
def expRectangular (powers : List Nat) (prec blockSize : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else
      let len := min blockSize n
      let powers := if len = blockSize then powers else powers.drop (blockSize - len)
      let (den, sum) := expBlock powers.tail n 1 0
      let next := (sum + ((powers.head! * acc) >>> prec)) / den
      expRectangular powers prec blockSize fuel (n - len) next

/-- Form an exact Taylor block, with powers of two kept out of the denominator. -/
def expBinaryBlock (num exponent start : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, den, sum => (den, sum)
  | n + 1, done, den, sum =>
    expBinaryBlock num exponent start n (done + 1) ((start + n + 1) * den)
      (num * ((den <<< (exponent * done)) + sum))

/-- Binary splitting for the Taylor series: return its common denominator and scaled numerator. -/
def expBinarySplit (num exponent : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (1, 0)
  | fuel + 1, start, n =>
    if n ≤ 32 then expBinaryBlock num exponent start n 0 1 0 else
      let len := n / 2
      let (ld, ls) := expBinarySplit num exponent fuel start len
      let (rd, rs) := expBinarySplit num exponent fuel (start + len) (n - len)
      (ld * rd, ((ls * rd) <<< (exponent * (n - len))) + num ^ len * rs)

def expSeries (num exponent prec reduction : Nat) : Nat × Nat :=
  let n := expTerms prec reduction - 1
  let scale := 1 <<< prec
  let short : Bool := num < (1 <<< 64)
  if 65536 ≤ prec && short then
    let (den, sum) := expBinarySplit num exponent (n.log2 + 2) 0 n
    let sum := if prec ≤ exponent * n then sum >>> (exponent * n - prec)
      else sum <<< (prec - exponent * n)
    (scale + sum / den, 2)
  else if prec ≤ 4096 || short then
    (expHorner num exponent scale n scale, 3)
  else
    let blockSize := max 1 n.sqrt
    let powers := expPowers num exponent blockSize scale [scale]
    (expRectangular powers prec blockSize (n / blockSize + 1) n scale, 21)

def expSquare (prec : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, result => result
  | n + 1, (value, error) =>
    expSquare prec n ((value * value) >>> prec,
      ((2 * value * error + error * error) >>> prec) + 2)

/-- Natural-number bounds for `2^prec * exp (±num / 2^exponent)`, for nonzero `num`. -/
def expNatBounds (num : Nat) (exponent : Int) (negative : Bool) (prec : Nat) : Nat × Nat :=
  let magnitude := (expBitLength num : Int) - exponent
  let scale := 1 <<< prec
  if magnitude ≤ -((prec + 1 : Nat) : Int) then
    if negative then (scale - 1, scale) else (scale, scale + 1)
  else if negative && (expBitLength (prec + 1) : Int) < magnitude then (0, 1)
  else
    let integerPart := match exponent with
      | .ofNat n => num >>> n
      | .negSucc n => num <<< (n + 1)
    if negative && prec + 1 ≤ integerPart then (0, 1) else
      -- Since `exp 1 < 2^(3/2)`, this bounds amplification for positive inputs.
      let growth := if negative then 0 else (3 * (integerPart + 1) + 1) / 2
      let target := prec + growth + 16
      let reduction := max 2 (target.sqrt / if target < 65536 then 2 else 3)
      let reduction := if 65536 ≤ target && num < (1 <<< 64) then min 128 reduction else reduction
      let squarings := (magnitude + reduction).toNat
      let working := target + squarings
      let exponent := (exponent + squarings).toNat
      let num := if exponent ≤ working then num else num >>> (exponent - working)
      let (value, error) := expSeries num (min exponent working) working reduction
      -- Truncating the reduced argument contributes less than two working-grid units.
      let error := error + 2
      let initial := if negative then
        ((1 <<< (2 * working)) / (value + error), error + 1)
      else (value, error)
      let (value, error) := expSquare working squarings initial
      let shift := working - prec
      let ub := ((value + error - 1) >>> shift) + 1
      (value >>> shift, if negative then min ub scale else ub)

def expOfNatWithPrec (num prec : Nat) : Dyadic :=
  if num &&& 1 = 1 then Dyadic.ofIntWithPrec num prec else
    let zeros := expBitLength (num - (num &&& (num - 1))) - 1
    Dyadic.ofIntWithPrec (num >>> zeros) ((prec : Int) - zeros)

def expBounds (x : Dyadic) (prec : Nat) : Dyadic × Dyadic :=
  match x with
  | .zero => (1, 1)
  | .ofOdd num exponent _ =>
    let (lb, ub) := expNatBounds num.natAbs exponent (!num.decNonneg.decide) prec
    (expOfNatWithPrec lb prec, expOfNatWithPrec ub prec)

end Inclusion.IntervalDyadicReal
