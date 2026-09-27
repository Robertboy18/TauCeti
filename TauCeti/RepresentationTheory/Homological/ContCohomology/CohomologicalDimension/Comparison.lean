/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# Cohomological dimension read on the explicit cohomology

The vanishing predicate `CohomologicalDimensionLE p G n` is stated against Mathlib's continuous
cohomology `continuousCohomology i (ofDiscreteModule ℤ G M)`, while the low-degree theory of
`LowDegree.lean` works with the explicit cocycle models `H¹(G, M)` and `H²(G, M)`. This file
transfers the vanishing through the comparison of `CohomologyComparison.lean`: for a locally
compact group `G` with `cd_p G ≤ 1`, the explicit `H²(G, A)` of every discrete `p`-primary
`G`-module `A` is trivial, and for a compact `G` with `cd_p G ≤ 2` the explicit coefficient map
`H²(G, B) → H²(G, C)` of a short exact sequence `0 → A → B → C → 0` with `A` `p`-primary is
surjective: the canonical connecting map `H²(G, C) → H³(G, A)` is zero, and the comparison
transports the resulting exactness statement to the explicit model, where no `H³` exists.

The coefficients live in the universe of `G`: the continuous-cohomology side needs them in a
universe containing that of `G`, and the explicit comparison is stated for coefficients in
exactly that universe.

## Main results

* `TauCeti.CohomologicalDimensionLE.subsingleton_H2`: `cd_p G ≤ 1` kills the explicit `H²` of
  every discrete `p`-primary `G`-module.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitCoeff2_proj_surjective_of_subsingleton` and
  `TauCeti.CohomologicalDimensionLE.explicitCoeff2_proj_surjective`: vanishing of `H³(G, A)`, in
  particular `cd_p G ≤ 2` with `A` `p`-primary, makes the explicit `H²(G, B) → H²(G, C)`
  surjective.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- **`cd_p G ≤ 1` kills the explicit `H²`** of every discrete `p`-primary `G`-module. -/
theorem CohomologicalDimensionLE.subsingleton_H2 (hcd : CohomologicalDimensionLE.{u} p G 1)
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
    [ContinuousSMul G A] (hA : IsPPrimaryTorsion p A) : Subsingleton (H2 G A) :=
  have := cohomologicalDimensionLE_iff.mp hcd A hA 2 one_lt_two
  (explicitH2AddEquivContinuousCohomology G A).toEquiv.subsingleton

section Surjective

variable [CompactSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  [ContinuousSMul G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)

omit [ContinuousSMul G A] in
/-- **Vanishing of `H³(G, A)` makes `H²(G, B) → H²(G, C)` surjective** on the explicit second
cohomology. The canonical connecting map `H²(G, C) → H³(G, A)` is zero, so exactness of the
canonical long exact sequence at `H²(G, C)` makes the canonical coefficient map onto, and the
degree-two comparison carries it to the explicit coefficient map. -/
theorem ContCohomology.DiscreteShortExact.explicitCoeff2_proj_surjective_of_subsingleton
    [Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G A))] :
    Function.Surjective
      (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology) := by
  intro y
  obtain ⟨x, hx⟩ := (S.longExact_exact₃ 2 (explicitH2AddEquivContinuousCohomology G C y)).1
    (Subsingleton.elim _ _)
  refine ⟨(explicitH2AddEquivContinuousCohomology G B).symm x, ?_⟩
  -- the comparison is stated for the equivariant hom `S.projDistribMulActionHom`, the long exact
  -- sequence for the underlying `S.proj`; the two coefficient maps agree
  have hmap : ofDiscreteModuleMap S.projDistribMulActionHom.toAddMonoidHom.toIntLinearMap
      (fun g m ↦ map_smul S.projDistribMulActionHom g m) =
      ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant := by
    congr 1
    exact congrArg AddMonoidHom.toIntLinearMap (AddMonoidHom.ext S.projDistribMulActionHom_apply)
  apply (explicitH2AddEquivContinuousCohomology G C).injective
  rw [← explicitH2AddEquivContinuousCohomology_coeffMap, AddEquiv.apply_symm_apply, hmap]
  exact hx

/-- **`cd_p G ≤ 2` makes `H²(G, B) → H²(G, C)` surjective** on the explicit second cohomology,
for every short exact sequence `0 → A → B → C → 0` of discrete `G`-modules whose kernel `A` is
`p`-primary. -/
theorem CohomologicalDimensionLE.explicitCoeff2_proj_surjective
    (hcd : CohomologicalDimensionLE.{u} p G 2) (hA : IsPPrimaryTorsion p A) :
    Function.Surjective
      (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology) :=
  have := cohomologicalDimensionLE_iff.mp hcd A hA 3 (by norm_num)
  S.explicitCoeff2_proj_surjective_of_subsingleton

end Surjective

end TauCeti
