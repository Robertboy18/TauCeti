/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Projective
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# Extensions of a projective pro-`p` group split, and its `H²` vanishes

Let `G` be a projective pro-`p` group: every continuous homomorphism from `G` into a quotient of
a profinite pro-`p` group lifts continuously (`TauCeti.IsProjective`). An extension
`1 → M → E → G → 1` of topological groups with profinite total group `E` and pro-`p` kernel `M`
has pro-`p` total group, so projectivity lifts the identity of `G` through the projection `E ↠ G`
to a continuous homomorphic section: the extension splits
(`GroupExtension.exists_splitting_continuous_of_isProjective`).

Read through the classification of profinite extensions by continuous `H²`, this is the vanishing
of the second continuous cohomology of `G` with coefficients in any profinite pro-`p` abelian
`G`-module `M` (`TauCeti.IsProjective.subsingleton_H2`): every class of the explicit `H²(G, M)` is
the class of a profinite extension of `G` by `M`, and the class of a split extension is zero. The
extension dictionary reads its abelian kernel multiplicatively, so the vanishing is first stated
for a `CommGroup` `M`; an `AddCommGroup` `M` is `Additive (Multiplicative M)`, and
`TauCeti.IsProjective.subsingleton_H2_of_isPPrimaryTorsion` restates the vanishing for it.
Transported through the degree-two comparison with Mathlib's `continuousCohomology`, the
statement takes its canonical form for a finite discrete `p`-primary `G`-module
(`TauCeti.IsProjective.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`), which is the
input to `cd_p G ≤ 1` in
`TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension`.

The free pro-`p` groups, on a type or on a pointed profinite space, are projective, and the
vanishing of their `H²` in `TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology` is the
instance of these statements at `freeProP p X`.

## Main results

* `GroupExtension.exists_splitting_continuous_of_isProjective`: every profinite extension of a
  projective pro-`p` group by a pro-`p` group splits by a continuous homomorphic section.
* `TauCeti.IsProjective.subsingleton_H2`: **`H²(G, M) = 0`** for `G` projective pro-`p` and `M` a
  profinite pro-`p` abelian `G`-module.
* `TauCeti.IsProjective.subsingleton_H2_of_isPPrimaryTorsion`: the same for a profinite
  `p`-primary torsion abelian `G`-module written additively.
* `TauCeti.IsProjective.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`: the same in
  Mathlib's continuous cohomology, for a finite discrete `p`-primary `G`-module.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4 and §5.9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.6.
-/

public section

namespace TauCeti

universe u v

open ContCohomology

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Extensions split -/

section Splitting

variable [T2Space G] {M : Type*} [Group M] [TopologicalSpace M]
  {E : Type v} [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [TotallyDisconnectedSpace E]

/-- **Extensions of a projective pro-`p` group by a pro-`p` group split.** An extension
`1 → M → E → G → 1` of topological groups with profinite total group and pro-`p` kernel, over a
projective pro-`p` Hausdorff group `G`, has a continuous homomorphic section: the total group is
pro-`p`, and projectivity lifts the identity of `G` through the projection. -/
theorem _root_.GroupExtension.exists_splitting_continuous_of_isProjective
    (S : GroupExtension M E G) (hinl : Continuous S.inl) (hrh : Continuous S.rightHom)
    (hM : IsProP p M) (hG : IsProP p G) (hproj : IsProjective.{u, v, u} p G) :
    ∃ s : S.Splitting, Continuous ⇑s := by
  have hE : IsProP p E := S.isProP hinl hrh hM hG
  -- The projection, bundled with its continuity; it evaluates as `S.rightHom` by construction.
  let π : E →ₜ* G := ⟨S.rightHom, hrh⟩
  have hπ : ∀ z, π z = S.rightHom z := fun _ ↦ rfl
  obtain ⟨s, hs⟩ :=
    hproj.exists_continuous_lift hE π S.rightHom_surjective (ContinuousMonoidHom.id G)
  exact ⟨GroupExtension.Splitting.mk s.toMonoidHom fun y ↦ by
    simpa [hπ] using DFunLike.congr_fun hs y, s.continuous⟩

end Splitting

namespace IsProjective

/-! ### The vanishing of `H²` -/

variable [CompactSpace G] [TotallyDisconnectedSpace G]

section Cohomology

variable {M : Type v} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [CompactSpace M]
  [TotallyDisconnectedSpace M] [MulDistribMulAction G M] [ContinuousSMul G M]

/-- **`H²` of a projective pro-`p` group vanishes.** For `G` projective pro-`p` and `M` a profinite
pro-`p` abelian group with a continuous action of `G`, the explicit second continuous cohomology
group `H²(G, M)` is zero: every class is the class of a profinite extension of `G` by `M`, which
splits. -/
theorem subsingleton_H2 (hproj : IsProjective.{u, max u v, u} p G) (hG : IsProP p G)
    (hM : IsProP p M) : Subsingleton (H2 G (Additive M)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨Y, rfl⟩ := ProfiniteGroupExtension.exists_contCohomologyClass_eq c
  rw [ProfiniteGroupExtension.contCohomologyClass_def,
    ← Y.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]
  exact Y.toGroupExtension.exists_splitting_continuous_of_isProjective Y.continuous_inl
    Y.continuous_rightHom hM hG hproj

end Cohomology

section Additive

variable {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [TotallyDisconnectedSpace M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **`H²` of a projective pro-`p` group vanishes, additive form.** For `G` projective pro-`p` and
`M` a profinite `p`-primary torsion abelian group, written additively, with a continuous action of
`G`, the explicit second continuous cohomology group `H²(G, M)` is zero. -/
theorem subsingleton_H2_of_isPPrimaryTorsion (hproj : IsProjective.{u, max u v, u} p G)
    (hG : IsProP p G) (hM : IsPPrimaryTorsion p M) : Subsingleton (H2 G M) :=
  -- `Additive (Multiplicative M)` is `M` with the same instances, so the multiplicative statement
  -- applies as it stands; `isPPrimaryTorsion_additive_iff` reads the hypothesis the same way.
  hproj.subsingleton_H2 hG (M := Multiplicative M)
    (IsPGroup.isProP ((isPPrimaryTorsion_additive_iff (M := Multiplicative M)).1 hM))

end Additive

/-- **`H²` of a projective pro-`p` group vanishes on finite coefficients**, in Mathlib's continuous
cohomology: for `G` projective pro-`p` and `M` a finite discrete `p`-primary torsion abelian group
with a continuous action of `G`, the canonical `continuousCohomology 2` of the topological
representation attached to `M` is zero. -/
theorem subsingleton_continuousCohomology_two_of_isPPrimaryTorsion
    (hproj : IsProjective.{u, u, u} p G) (hG : IsProP p G) (M : Type u) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M] [DistribMulAction G M]
    [ContinuousSMul G M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G M)) :=
  haveI := hproj.subsingleton_H2_of_isPPrimaryTorsion hG hM
  (explicitH2AddEquivContinuousCohomology G M).toEquiv.symm.subsingleton

end IsProjective

end TauCeti
