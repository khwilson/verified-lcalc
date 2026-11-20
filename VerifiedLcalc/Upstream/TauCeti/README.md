# Selected TauCeti ports

This directory ports a small arithmetic dependency chain rather than adding
TauCeti as a package and changing this project's mathlib pin. The proof bodies
are checked against this project's Lean 4.36.0-rc2 / mathlib
3440367ed1804626334f13a3a534a9cbb3385a59.

Source repository: https://github.com/TauCetiProject/TauCeti

- The local-polynomial dependency chain and completion residue-field proof come from the clean local checkout at
  d01c9825761c7e6168457c383458afa8668196a7.
- The multiplicativity excerpt in LFunction/Basic.lean comes from
  0642eae29e0a59ef798d04de325386445906e755. Its continuation theorem and import
  were omitted; its arithmetic proof bodies are unchanged.
- The integral-point membership excerpt in `Affine/Point/Integral.lean` comes
  from `8794ab329bb60340fa690a2902cf995f0571721b`. It retains declarations through
  `neg_mem_integralPoints_iff`, including the construction of rational points
  from integer solutions and the `integralPoints` set. Later searches and
  change-of-variables results are omitted; the retained proof bodies are unchanged.

PROVENANCE.json records each original source hash, source revision, destination,
ported hash, and adaptations. The port rewrites import paths, narrows one broad
tactic import, and replaces an obsolete polynomial coefficient projection with
a typed lambda. Original theorem namespaces are retained. Copyright headers
are preserved. The Apache 2.0 license is in LICENSES/TauCeti-Apache-2.0.txt at
the project root.

Our adapter is VerifiedLcalc/EllipticCurve/TauCeti.lean. Its local-factor theorem
requires an actual residue-field isomorphism identifying the input equation
with the reduction of a minimal local model. This hypothesis is not supplied
by the modularity axiom. The adapter proves local polynomial, local inverse
power-series, and local Dirichlet-factor coefficient identities. Global
multiplicativity reduces all coefficients and their bounds to prime-power
identifications.

The completion port identifies the residue field of the completed valuation
ring with the original ideal quotient; the unused Henselian import is omitted.

Validation:

    lake build VerifiedLcalc.EllipticCurve.TauCeti VerifiedLcalc.Certification.CentralEvaluator
    lake env lean AuditIntegration.lean

The integration audit guards that the imported arithmetic and general analytic
implications have only propext, Classical.choice and Quot.sound, without the
project's modularity axiom, sorryAx, or native-reduction verification axioms.
The modularity axiom remains isolated in its original opt-in module.

The selected MinimalModel/Basic excerpt now also supplies the minimal-model
valuation comparison and unit-scaling lemmas. It retains declarations through
`VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul`, with original
proof bodies, and omits unused imports and subsequent declarations. This
is recorded together with the other selected excerpts and hashes in
PROVENANCE.json.

See NOTICE.md for the minimal-model excerpt's additional Kevin Buzzard/Imperial FLT attribution, retained from TauCeti's source provenance.

The canonical global-minimality interface and the localization/fraction-field
instances and valuation-integers identification are also selected from
`d01c9825761c7e6168457c383458afa8668196a7`. The predicate and theorem namespaces
are unchanged. Unused semi-global minimality and integrality-descent results
are omitted; the deprecated adic-valuation umbrella import is narrowed to its
valuation component. `EllipticCurve/GlobalMinimality.lean` proves the checked
witness criteria directly in these localizations. No localization/completion
minimality equivalence is assumed by the integration.
