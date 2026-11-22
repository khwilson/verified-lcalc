module

/-! Raw finite transcripts for minimality and local Tate computations. Their
validation and mathematical interpretation live in the corresponding cores. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A finite, explicit factorization witness. Primes outside this list are good.
Both the factorization and the minimality checks are rechecked in the kernel. -/
structure MinimalityWitness where
  /-- Prime factors, with multiplicity, of the equation discriminant. -/
  primes : List Nat
  deriving Repr, DecidableEq

/-- A finite Tate reduction transcript. Codes: II=2, III=3, IV=4,
I0*=-1, IV*=-4, III*=-3, II*=-2, I_n*=-(4+n). -/
structure TateWitness where
  /-- Initial horizontal translation. -/
  r : Int
  /-- Initial shear in the y-coordinate. -/
  s : Int
  /-- Initial vertical translation. -/
  t : Int
  /-- Vertical translation parameter at the start of the starred cases. -/
  starT : Int := 0
  /-- Candidate repeated root of the cubic. -/
  cubicRoot : Int := 0
  /-- Candidate repeated root of the quadratic. -/
  quadraticRoot : Int := 0
  /-- Repeated roots checked in the starred blow-up sequence. -/
  chain : List Int := []
  /-- Integer code for the proposed Kodaira symbol. -/
  kodaira : Int
  deriving Repr, DecidableEq

/-- Finite transcripts for the only primes requiring wild root-number data. -/
structure WildData where
  /-- Transcript at residue characteristic two, when additive reduction occurs. -/
  atTwo : Option TateWitness
  /-- Transcript at residue characteristic three, when additive reduction occurs. -/
  atThree : Option TateWitness
  deriving Repr, DecidableEq

end VerifiedLcalc.EllipticCurve
