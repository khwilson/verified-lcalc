# Additional attribution for the minimal-model excerpt

TauCeti's `AlgebraicGeometry/EllipticCurve/MinimalModel/Basic.lean` records that
its minimality and minimal-model valuation comparisons were ported/adapted from
Kevin Buzzard's work in Imperial College London's FLT project, licensed under
Apache 2.0:

- Repository: https://github.com/ImperialCollegeLondon/FLT
- Source revision: `bc2fe8ff7396469a16c2a6d51d6117f5825d93a0`
- Source: `FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`
- FLT PR #1088: "Quadratic twist to split multiplicative reduction"

The declarations included in our excerpt that TauCeti attributes to that
source are `isMinimal_of_valuation_c₄_eq_one`, the valuation inequality renamed
`valuation_Δ_le_of_isMinimal_smul`, `valuation_Δ_eq_of_isMinimal_smul`, and
`valuation_u_eq_one_of_isMinimal_smul`. The excerpt also retains TauCeti's
intervening orbit/comparison and unit-lifting lemmas. TauCeti documents its
adaptations in the original file's Provenance section. We retain those proof
bodies unchanged, while selecting the smaller excerpt and imports recorded in
PROVENANCE.json.

The source copyright header credits the Tau Ceti contributors. This notice
preserves its additional Kevin Buzzard/FLT attribution. The Apache 2.0 license
text distributed with these ports is `LICENSES/TauCeti-Apache-2.0.txt` at the
project root.
