# LMFDB elliptic curves over ℚ through `certify_ec`

The certification target is a mathematical assertion about a supplied
`WeierstrassCurve ℤ` and its base change to ℚ. A field can request an exact
equality, a bound or enclosure, a witness of existence, or a completeness
statement. Each has its own evidence contract. This roadmap covers the EC/Q
tables joined by LMFDB's [underlying data view](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)
and the mathematical interpretation of the facts they expose. Linked entries in
external catalogues may be inputs to relation certificates. Certifying entire
linked catalogues or a conductor-range census is a separate enumeration problem.

## Field inventory

The implementation baseline is verified-lcalc `a74dfee`. For the exact public
inputs, evidence and output theorems at that baseline, see
[LMFDB invariants](../LMFDB_INVARIANTS.md). Status below refers to that baseline.
Interpretations were checked on 2026-11-21 against the live
[curve schema](https://www.lmfdb.org/api/ec_curvedata/), the joined view above,
the [LMFDB renderer](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/web_ec.py)
and the [Cremona data scripts](https://github.com/JohnCremona/ecdata/tree/25cec5ecfec8b9f016eb1631ac633194c2bed39f/scripts).
The producer and row formats vary by dataset. In particular, zero, empty arrays,
nulls, and placeholders such as `?` or a missing join must be interpreted under
the source schema before creating a witness.

| Table and fields | Assertion and coverage |
| --- | --- |
| `ec_curvedata.ainvs, jinv, absD, signD, bad_primes, num_bad_primes` | The integral equation, its rational j, discriminant sign, and the absolute minimal discriminant and complete bad-prime data with a minimality witness. Supported. |
| `ec_curvedata.conductor` and its copies in joined tables | Level of the arithmetic modular realization, conditional on the authorized modularity package and checked local evidence. Supported. L1 adds identification with the canonical algorithmic conductor. |
| `ec_curvedata.semistable, squarefree_disc, potential_good_reduction` | Everywhere good or multiplicative reduction, squarefreeness of the absolute minimal discriminant, and potential good reduction at every finite place. L1. Squarefree discriminant and squarefree conductor are distinct predicates. |
| `ec_localdata.prime, discriminant_valuation, j_denominator_valuation, kodaira_symbol, reduction_type, conductor_valuation, root_number, tamagawa_number` | A prime-indexed row. The valuations are $v_p(\Delta_{\min})$ and $v_p(\operatorname{den}(j))$. Reduction code −1 is nonsplit multiplicative, 0 additive, and 1 split multiplicative on the bad-prime rows. Decode Kodaira codes to typed symbols. The root number is local. L1–L2. |
| `ec_classdata.aplist, anlist` | Initial primes and consecutive arithmetic Dirichlet coefficients. Supported for the represented curve. Transfer to other class members requires the isogeny theorem in I1. |
| `ec_classdata.isogeny_matrix, class_size, class_deg`; copies and `ec_curvedata.isogeny_degrees` | Minimum isogeny degrees between indexed representatives, number of rational isomorphism classes, maximum matrix entry, and distinct entries of the represented curve's row, respectively. I1. |
| `ec_mwbsd.gens, torsion_generators, ngens, rank_bounds`; `ec_curvedata.rank, torsion, torsion_structure, torsion_primes, intrinsic_torsion` | Weighted triples $(a,b,c)$ with $c\ne0$ represent $(a/c^2,b/c^3)$. Generator count is list length. Rank bounds refer to Mordell–Weil rank. Torsion data concern the full rational torsion subgroup. Intrinsic torsion is the radical of the torsion pairing with values in $\mathbf Q^\times\otimes\mathbf Q/\mathbf Z$. Integral infinite-order and supplied independence proofs already give rank lower bounds. M1–M2. |
| `ec_mwbsd.xcoord_integral_points`; `ec_curvedata.num_int_pts` | Finite affine integral solutions in the specified model, with one stored x per fiber and the count over all y. Membership is supported. M3 proves exhaustivity. |
| `ec_curvedata.cm, min_quad_twist_ainvs, min_quad_twist_disc` | Geometric endomorphism ring is ℤ when the CM code is zero, otherwise it is the order of the specified discriminant. Twist data give an integral representative minimizing conductor and a quadratic discriminant (1 for the trivial twist). The producer applies further tie rules, including special j values. I2. |
| `ec_curvedata.degree, manin_constant, optimality` | Degree and differential scaling for the modular parametrization, and optimal-quotient status. The producer's optimality codes above 1 express ambiguity among candidates. Manin data can be conditional on optimality. I3. |
| `ec_curvedata.analytic_rank`; `ec_mwbsd.special_value` | Vanishing order at 1 and leading coefficient $L^{(r)}(1)/r!$ in arithmetic normalization. Rank 0/1 are supported with full checked numerical payloads. Reference data for higher rank may carry uncertainty. A1. |
| `ec_mwbsd.heights, real_period, area, tamagawa_product, sha_an`; `ec_curvedata.regulator, sha, sha_primes` | Canonical heights, full real Néron period, complex period lattice area, product of local Tamagawa numbers, determinant for a Mordell–Weil basis, and analytic BSD quotient. Stored integer `sha` is analytic data, potentially rounded, and `sha_primes` lists its prime divisors. L2 and A2–A3. |
| `ec_curvedata.abc_quality, szpiro_ratio, faltings_height, stable_faltings_height, faltings_ratio, faltings_index` | The coprime abc triple from $j/1728$, the **modified** Szpiro ratio $\log\max(\lvert c_4\rvert^3,\lvert c_6\rvert^2)/\log N$ of a minimal model, the Faltings heights, and the Néron lattice index relative to the least-height curve in the class. The producer's `faltings_index` is an ordering index. A2 and I1. |
| `ec_galrep.prime, modell_image, elladic_image, adelic_image, adelic_gens`; `ec_curvedata.modell_images, elladic_images, modm_images, adelic_level, adelic_index, adelic_genus, nonmax_primes, nonmax_rad, serre_invariants` | Images in a specified torsion basis up to conjugacy, subgroup presentation, conductor-independent image level and index, genus of the associated modular curve, exceptional primes and their radical, and exceptional triples (prime, Serre weight, Serre conductor). The renderer uses prime 0 for an adelic row. A partial label with unknown component can still convey verified numerical invariants if independently justified. G1. |
| `ec_torsion_growth.degree, field, torsion` | Absolute field degree, defining polynomial in ascending coefficient order, and full torsion invariant factors of the base change. G2 distinguishes one field from primitive growth and exhaustivity over a degree range. |
| `ec_iwasawa.iwdata, iwp0` | Prime-indexed ordinary/multiplicative $(\lambda,\mu)$ or supersingular $(\lambda^+,\lambda^-,\mu)$ data, with explicit missing/additive codes. A positive `iwp0` asserts vanishing of all these analytic invariants for good primes at or above that threshold. G3. |
| `ec_padic.p, prec, unit, val` | A p-adic regulator residue for the corresponding curve and normalization, indexed by class. Precision means a p-adic ball, not an exact value. G3. |
| Across tables `id, lmfdb_label, lmfdb_iso, lmfdb_number, Ciso, Clabel, Cnumber, iso_nlabel, trace_hash` | Identifiers, joins, orderings, and fingerprints. Validate their syntax or snapshot consistency in import tooling. If mathematical class or curve identity is requested, check actual rational maps. A hash or catalogue match does not prove identity. |

Derived displays such as equation invariants, local Euler polynomials, the sign
product including the real place, analytic Sha factors, and associations with
modular forms or subgroup labels inherit the appropriate mathematical contracts.
[LMFDB's reliability notes](https://www.lmfdb.org/EllipticCurve/Q/Reliability)
describe which published data are rigorous, rounded, or conjectural. Their
methodology does not supply a Lean witness.

## Source review and upstream routing

The source review used the project's then-current Mathlib revision
`3440367ed1804626334f13a3a534a9cbb3385a59`. See the [build guide](../BUILD.md)
for the active dependency pins.
The [public Mathlib master reduction file](https://github.com/leanprover-community/mathlib4/blob/a495318fed6482b3c90df686de5131b46a70fd5b/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean)
was also checked for the reduction predicates. Both supply
`WeierstrassCurve.IsMinimal`, the reduction classes, and the standard
Weierstrass and affine point types. The TauCeti public main inspected
here is [b608709](https://github.com/TauCetiProject/TauCeti/tree/b608709b45f23ccda55703d572b0adb1fdec30fd/TauCeti/AlgebraicGeometry/EllipticCurve).
API names below refer to that source. The project now imports the
[tagged TauCeti package](../BUILD.md) directly. Reuse candidates require a compatibility and axiom audit
before importing. This review inspected declarations and did not compile a
dependency upgrade.

The [EllipticCurves roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/55dca6d54f7cd2198ee70c90b9c84eeef0f6b952/TauCetiRoadmap/EllipticCurves/README.md)
owns the reduction, isogeny, descent, and height foundations. The
[ModularCurves roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/55dca6d54f7cd2198ee70c90b9c84eeef0f6b952/TauCetiRoadmap/ModularCurves/README.md)
owns level structure and moduli. Each proposal below identifies the input and
conclusion for a reusable theorem or checker. Treat larger items as dependency
specifications for future roadmap revisions. For an upstream implementation,
cite the exact covered roadmap target in the PR and complete TauCeti's
[quality-pass requirements](https://github.com/TauCetiProject/TauCeti/blob/b608709b45f23ccda55703d572b0adb1fdec30fd/AGENTS.md).
When a target has no existing owner, propose the addition for human review under
the [roadmap rules](https://github.com/TauCetiProject/TauCetiRoadmap/blob/55dca6d54f7cd2198ee70c90b9c84eeef0f6b952/README.md#writing-a-roadmap).
These are local proposals.

## Local arithmetic

**L1 · Canonical reduction and potential good reduction.** Use
`isSemistable_iff_forall_valuation_Δ_eq_one_or_valuation_c₄_eq_one` over ℤ
and the complete prime-factor witness for Δ. Prove the resulting finite test
checks both truth values. For a checked local transcript, exhibit a
minimal-equivalent terminal model and `IsTateTerminal`, then apply
`reductionSymbol_eq_of_isTateTerminal` and the terminal reduction-type
equivalences. Reuse `algorithmicOggExponent`, `algorithmicConductor`,
and `count_algorithmicConductor` for (f_p) and the global norm.
The terminal predicate gives an algorithmic symbol and its invariance.
Geometric identification with the special fiber and intrinsic Artin conductor
still needs the bridge in [T2/TC-06](../TAUCETI_BACKLOG.md#tc-06--intrinsic-conductor-and-tame-formula).
For potential good reduction, specialize
`WeierstrassCurve.hasPotentialGoodReduction_iff_isInteger_j` to each
localization of ℤ at a prime, a DVR with fraction field ℚ. The theorem
requires an elliptic curve over that fraction field. Prove the remaining
finite-to-global adapter by showing that $j$ lies in every such localization exactly when
its reduced rational denominator equals one.
[TauCeti potential-good-reduction criterion](https://github.com/TauCetiProject/TauCeti/blob/b608709b45f23ccda55703d572b0adb1fdec30fd/TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/PotentialGoodReduction.lean).
Accept tests for both truth values, good/split/nonsplit reduction, additive
types at 2 and 3, and a semistable curve with nonsquarefree minimal discriminant.

**L2 · Tamagawa numbers and local signs.** Given a validated terminal model
over ℚₚ, prove its checked finite index equals
`E.tamagawaNumber` at p, using TauCeti's
`tamagawaNumber_eq_tateLocalIndex`; use `tamagawaProduct_eq_prod` after
proving all omitted places good. Distinguish rational component-group size
from geometric component count. For signs, retain the arithmetic sign of a
valid transcript and expose a separate intrinsic epsilon-factor conclusion
only after TC-07. The existing global modular sign compatibility does not
imply individual epsilon-factor equalities. Accept split/nonsplit $I_n$,
additive examples with different component counts over the ground and residue
closure, and wild regression cases.

## Mordell–Weil and integral points

**M1 · Full rational torsion.** The [odd-prime specialization](../../VerifiedLcalc/EllipticCurve/TorsionBound.lean)
proves that the full rational torsion order divides each certified point count
at an odd prime of good reduction. It applies pinned TauCeti's
[`card_torsion_dvd_card_reduction`](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/TorsionReduction.lean#L269-L282)
using the ramification bound for odd primes over ℚ. The gcd at 3 and 5
certifies the exact trivial torsion subgroup of 37.a1.

When reduction only gives prime-to-residue torsion injectivity, specialize
TauCeti's
`card_torsionBy_dvd_card_reduction` to a certified point count for each supplied
good prime p and prime power ℓᵏ with ℓ ≠ p. Combine valuations across primes to obtain a global order bound, discharging each
residue-characteristic exception. Given explicit generators $P_i$, prove
`AddEquiv` from the product of cyclic groups of the claimed invariant factors
onto the rational torsion subgroup. Verify the homomorphism, exact orders and
injectivity, then use the upper bound for surjectivity. Accept trivial,
cyclic and noncyclic examples, and rejection of a same-order wrong structure
or a list of dependent generators. For intrinsic torsion, use functions
with divisor $n(P-O)$ and norm evaluation on a disjoint degree-zero divisor
representing $Q-O$. Prove independence of choices and symmetric bilinearity,
then evaluate on a verified torsion basis and compute the radical of the
pairing. Test a nontrivial group with proper radical.
[LMFDB convention](https://www.lmfdb.org/knowledge/show/ec.intrinsic_torsion) and
[Yamazaki et al.](https://arxiv.org/abs/2512.00787).

**M2 · Exact algebraic rank and basis.** Reuse
`moduleFinite_point_of_numberField`, `pow_rank_le_card_selmerGroup₂` and
the Galois-cohomological Selmer API. Given an exhaustive finite Selmer
overgroup of cardinality (u) and certified rational 2-torsion order (t),
prove $2^{\operatorname{rank}}t\le u$ through the Kummer injection. Provide
computable finite local conditions and explicit completeness checks, starting
with 2-descent over the cubic étale algebra and allowing reducible cases.
Pair the upper bound with the existing independence result for exact rank.
A basis certificate additionally proves the subgroup generated by the supplied
points and torsion has index one. Start with a finite index bound and
prime-by-prime saturation, using a proved height estimate or another verified
index bound. Accept rank zero and positive rank, and reject an independent
family of the right rank but index greater than one for basis claims. Consult
TauCeti's `WorkedExamples/X3SubXAddOne/Rank` for a rank proof and
`WorkedExamples/Curve37a1` for an independent lower-bound example.

**M3 · Integral-point completeness.** Prove the finite reconstruction lemma
for each x by completing the square:
$(2y+a_1x+a_3)^2=(a_1x+a_3)^2+4(x^3+a_2x^2+a_4x+a_6)$.
Check parity, both square roots and the double-root case. Given a proved
global bound on x or on Mordell–Weil coefficients for every integral point,
a checked sieve/exhaustive enumeration must give a set equivalence with all
integral affine points. Use M2 for coefficient bounds, and specify the
effective height bound or covering descent separately. Accept two-point and
one-point fibers and rejection when a valid x is omitted.

## Isogenies, twists and modular parametrizations

**I1 · Isogeny-class graph.** Reuse `TauCeti.Isogeny.degree`,
`degree_comp`, Vélu descent and `LFunction_eq`. First prove existence and
degree for each supplied map, and rational nonisomorphism of distinct
representatives. To certify a complete graph, prove exhaustivity of rational
prime-degree neighbors at every vertex via a proved possible-prime bound and
Galois-stable cyclic kernels, and prove that every rational isogeny connection
is generated by these steps. Certify minimum degrees by excluding smaller
candidate degrees or proving an appropriate weighted-path theorem. Then derive
the stored row, maximum, and class size. Accept a
class with multiple vertices and an indirect composite-degree minimum.

**I2 · Geometric CM and minimal quadratic twists.** Use
`GeometricEnd`, `HasGeometricCM`, `CMAction` and
`QuadraticTwist/Classification`. Prove a ring isomorphism with the specified
imaginary quadratic order, or surjectivity of the integer endomorphism map.
An exhibited CM action proves an inclusion; exact order requires an
endomorphism-ring upper bound. A certified rational singular-modulus
classification could give the non-CM exclusion and exact-order lookup, with
local endomorphism proofs as a second route. For twists check the squareclass
represented by the fundamental discriminant, an explicit variable change to
the proposed global minimal model, and
$N(E^{D_0})\le N(E^D)$ for every quadratic squareclass D.
Provide local conductor comparisons giving a finite search with all excluded
support accounted for, including 2, 3 and j = 0 or 1728. If asserting the exact
catalogue representative, also check the producer's tie rule on the complete
minimal-conductor set. Accept two distinct equal-conductor twists and at least
one special-j case.

**I3 · Optimal quotient and Manin constant.** Specify the $X_0(N)$ Jacobian,
rational newform quotient and normalized map (cusp at infinity sent to the
identity). Show the quotient has connected kernel for an optimality claim.
For a given map prove its actual degree and
$\phi^*\omega_E=c\,2\pi i f(z)\,dz$, with the integral minimal
differential and $a_1(f)=1$. Requires the modular curves, Jacobian and
quotient comparison plus effective modular-symbol lattice certificates.
The existing analytic modular realization supplies no map or connected
kernel. Accept a positive degree and scaling comparison on an optimal and
a nonoptimal member of the same class.

## Analytic and BSD data

**A1 · Higher derivatives and rank.** Extend
[A4 in the analytic roadmap](MODULAR_LFUNCTION_EVALUATION.md) with
verified log-moment quadrature, truncation bounds and a triangular conversion
from the completed function to raw arithmetic derivatives. Given the checked
nonzero enclosure for $L^{(r)}(1)$ and exact zeros of all earlier derivatives,
export analytic order r and the enclosure divided by (r!).
Use functional-equation parity on the completed derivatives with the proved
conversion. An enclosure inside a cutoff expresses only a numerical result.
An exact upgrade via `CurvePrecisionClaim.Hypotheses` requires an explicit
curve, derivative prefix, cutoff and nonzero gap strictly larger than the
cutoff. Such a hypothesis stays visible in the theorem. An exact rank claim
still requires the next nonvanishing. Accept positive and negative Fricke
signs, include order two and three enclosures, and reject ambiguous intervals
and precision records with mismatched curve or normalization.

**A2 · Real and complex invariants.** The abc-quality check proves a
rational error bound about the reported LMFDB decimal using the checked prime
factorization of the reduced abc product and directed dyadic logarithms.
Reuse
`minimalRealPeriod`, `canonicalHeightQuadratic`,
`Point.exists_abs_naiveHeight_nsmul_div_sq_sub_le`,
`regulator_eq_abs_det_neronTateGramMatrix`, `abcQuality`, and the
modified expression in `Szpiro.lean`. Prove a computable rational error
bound for the height limit, including the factor relating that normalization
to the stored heights, then enclose the pairing and determinant for an M2
basis. Prove period integrals with tail/error bounds for both real-component
types, plus a comparison between the complex area integral and covolume of
the Néron period lattice. Use the verified metrics to evaluate Faltings height
and the change to semistable base change for stable height. An exact Faltings
ratio requires actual lattice inclusion and index or a rigorously isolated
integer under a proved integrality theorem. Pin the additive constants and
the differential normalization against each source before accepting any
decimal. Accept exact rank-zero regulator $1$, a positive-rank interval,
both signs of Δ for periods and a case with different stable and unstable
Faltings heights.

**A3 · Analytic quotient and algebraic Sha.** Given A1–A2 and L2/M1 evidence,
enclose the following quotient with a strictly positive denominator.

$$\frac{L^{(r)}(1)}{r!}
  \frac{\lvert E(\mathbf Q)_{\rm tors}\rvert^2}
       {\Omega_E\operatorname{Reg}(E)\prod_p c_p}.$$
 If the entire enclosure lies inside an integer's rounding cell,
certify that rounding and separately check the prime divisors of the
integer. An exact rational equality needs a proof of normalization and an
exact formula, for example normalized modular symbols in rank zero. Reuse
`shafarevichTateGroup` for algebraic claims. A separate result must prove
finiteness and cardinality, or state the certified primary component using a
Selmer exact sequence and a complete descent. A rank agreement or rounded
analytic quotient supplies neither. Accept a nontrivial analytic value and
a component-level algebraic claim with independent proofs.

## Galois representations, torsion growth and p-adic data

**G1 · Galois images and Serre data.** Reuse
`tateModuleGaloisRepresentation` and finite torsion bases and Weil pairing.
For modulus m construct the actual representation on $E[m]$, check a basis
and prove conjugacy of its image with the subgroup generated by the supplied
matrices. One proof route computes the splitting field of coordinates of
the torsion basis and checks its full Galois action. Finite-level evidence
alone gives a finite-level conclusion. For an ℓ-adic or adelic equality
prove an inverse-image theorem for the supplied level, including its
minimality, residual surjectivity outside the checked exceptional primes and
cross-prime entanglement. A nonmaximal-prime list needs a completeness
theorem and a convention for the CM case. Fix notation for Serre triples
from the producer; derive group index, associated modular-curve genus and
each triple under the appropriate subgroup and modular-curve comparison.
Accept conjugate bases, a proper image, and an adelic entanglement example
where prime-wise images alone lose information.

**G2 · Torsion growth.** Given irreducible $f\in\mathbb Q[X]$, build its
number field, verify $[K:\mathbf Q]=\deg f$, and prove an isomorphism
between the full torsion of (E_K) and the given finite product of cyclic
groups. Generalize M1 using reduction at good places with checked residue
degrees. A complete growth assertion over a prescribed degree set requires
a proved order bound, classification of the relevant torsion-field stabilizers
from G1, a check that no proper subfield has the same growth, and identification of the represented fields up to the stated
equivalence. Accept strict growth, another field of the same degree without
that growth, and duplicate presentations of an isomorphic field.

**G3 · Iwasawa invariants and p-adic regulator.** Start with the analytic
$p$-adic L-series using normalized modular symbols, including the signed
supersingular variants. Identify its bounded power series with the source's
convention. Check $\mu$ by certifying coefficient divisibility throughout
the series and $\lambda$ by proving the index of the first coefficient
of minimal valuation. Such a check needs a proven global bound or a
structural argument in addition to a finite prefix. For the threshold field,
prove the vanishing claim at every good prime in the stated range.
[LMFDB Iwasawa conventions](https://www.lmfdb.org/knowledge/show/ec.iwasawa_invariants).
To make a separate algebraic claim, specify the cyclotomic Selmer local
conditions and prove the characteristic-ideal comparison. For regulators define the normalized p-adic height pairing
and its determinant on an M2 basis, with source-specific prime and
normalization restrictions. Check a congruence to $p^v u$ modulo
$p^{v+k}\mathbf Z_p$ **when** k counts relative digits of the unit; pin the
actual `prec` convention before mapping it. Accept negative valuations,
rank-zero normalization, ordinary and signed examples, and explicit missing
records. A class join requires evidence for the curve used and for any
transport along an isogeny.

## Implementation order

1. Land L1 as a few small certificate PRs, first finite semistability,
   squarefree discriminant and j-denominator checks, then local reduction
   exports. Add L2 as the terminal-index bridge becomes available.
2. Deliver M1, then M2's first finite descent/saturation path and M3's y-fiber
   checker, with integral-point exhaustivity after a bound. Run A1 and the
   small A2 log-ratio work in parallel. Develop I1 and I2 against existing
   isogeny and twist APIs.
3. Build the remaining A2–A3 and I3/G1–G3 dependency contracts before claiming
   coverage of the corresponding reference tables.

Each integration uses the existing shared optional-field witness for Lean
and exact JSON, with supplied evidence and atomic rollback on failed checks.
Exercise accepted, wrong, absent and insufficient evidence, including
backward compatibility for existing witnesses. Verify the resulting
mathematical statements in compiled consumers and audit finite results
separately from results using `ellipticModularity` or explicit precision
hypotheses. Use the prescribed Lean and Python validation targets for
implementation PRs. Stored expected ranks and rounded data may be compared
with finished results. Witness construction uses independent evidence.
