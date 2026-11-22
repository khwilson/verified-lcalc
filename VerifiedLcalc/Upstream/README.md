# Pinned upstream proof source

`LedvinkaExponential.lean` is David Ledvinka's exponential interval extension from
[mathlib PR #45193](https://github.com/leanprover-community/mathlib4/pull/45193),
head commit `9c80a26d5b6a5b4ec14d6db0aba596463c6b281f`, file
`Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Exponential.lean`.
The GitHub API reported this draft closed and unmerged on 2026-11-17.

The unmodified source's SHA-256 is
`c5a1483e4a3686837b2be161d32175dbc96b0e5e4d775cc38760b5d588a1932b`.
It is licensed under Apache 2.0; its copyright/author header is preserved and
`LICENSE` contains mathlib's license text.

The original port adapted this source to Mathlib
`3440367ed1804626334f13a3a534a9cbb3385a59` and Lean `v4.36.0-rc2`.
See the [build guide](../../docs/BUILD.md) for the current pins.

- Moved the 17 executable definitions unchanged into
  `LedvinkaExponentialCore.lean` (using `Nat`/`Int` instead of notation).
  The core imports only Std/Init; their mathematical proofs remain here.
- Added provenance to the source header and changed the local module path.
- Renamed the strong-induction alternative `h` to `ind` in `nat_lowbit`.
- Replaced three unsupported `.toReal` field-notation uses with the explicit
  `Inclusion.IntervalDyadicReal.Dyadic.toReal` function, retaining the same
  mathematical expressions.

No `sorry`, custom axiom, or native verification shortcut is permitted here.
The implementation includes range reduction, fixed-point Taylor evaluation,
rounded repeated squaring, and Horner/rectangular/binary summation strategies.
Its final `exp_mem` theorem supplies an interval inclusion rule for `Real.exp`.
It is not a logarithm, gamma, or incomplete-gamma evaluator. Helpers named
`expLogSearch` and `expLogBracket` concern integer bit lengths, not `Real.log`.

Keep this module opt-in. In particular, do not add it to the runtime executable's
imports merely to carry erased analytic proofs. Before replacing it with an
upstream import, select a compatible immutable mathlib revision and rerun the
project's build, saved-certificate replay, and axiom audit.
