/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Topological closure of subgroups

Basic facts about the topological closure of a subgroup of a topological group.

Two theorems of Mathlib are registered as instances, so that the quotient of a topological group
by the topological closure of a normal subgroup is found to be a Hausdorff topological group by
instance search alone: the closure of a subgroup is closed, and the closure of a normal subgroup
is normal.

The **closed normal closure** of a set `s`, the topological closure of `Subgroup.normalClosure s`,
is the least closed normal subgroup containing `s`
(`Subgroup.topologicalClosure_normalClosure_le_iff`). In particular it lies in the kernel of
every continuous homomorphism to a `T1` monoid that kills `s`
(`Subgroup.topologicalClosure_normalClosure_le_ker`), which is the fact behind the universal
property of a group presented by generators and relators inside a category of topological
groups: the quotient by the closed normal closure of the relators receives a continuous
homomorphism from every continuous homomorphism that kills the relators.

Finally, converting a subgroup to an additive subgroup commutes with topological closure. This
connects topological generation in a group with additive generation on its `Additive` type tag.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The topological closure of a subgroup is closed. -/
instance instIsClosedTopologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) :=
  s.isClosed_topologicalClosure

/-- The topological closure of a normal subgroup is normal. -/
instance instNormalTopologicalClosure (N : Subgroup G) [N.Normal] : N.topologicalClosure.Normal :=
  N.is_normal_topologicalClosure

/-- A closed normal subgroup contains the closed normal closure of `s` exactly when it contains
`s`: the closed normal closure is the least closed normal subgroup containing `s`. -/
theorem topologicalClosure_normalClosure_le_iff {s : Set G} {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) : (normalClosure s).topologicalClosure ≤ N ↔ s ⊆ N :=
  ⟨fun h ↦ subset_normalClosure.trans ((normalClosure s).le_topologicalClosure.trans h),
    fun h ↦ (normalClosure s).topologicalClosure_minimal (normalClosure_le_normal h) hN⟩

/-- The closed normal closure of the carrier of a closed normal subgroup is that subgroup. -/
theorem topologicalClosure_normalClosure_eq_self (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) : (normalClosure (N : Set G)).topologicalClosure = N :=
  le_antisymm ((topologicalClosure_normalClosure_le_iff hN).2 subset_rfl)
    (le_normalClosure.trans (normalClosure (N : Set G)).le_topologicalClosure)

/-- A continuous homomorphism to a `T1` monoid that kills `s` kills the closed normal closure of
`s`. -/
theorem topologicalClosure_normalClosure_le_ker {M : Type*} [MulOneClass M] [TopologicalSpace M]
    [T1Space M] {f : G →* M} (hf : Continuous f) {s : Set G} (h : ∀ r ∈ s, f r = 1) :
    (normalClosure s).topologicalClosure ≤ f.ker :=
  (topologicalClosure_normalClosure_le_iff (f.coe_ker ▸ isClosed_singleton.preimage hf)).2
    fun r hr ↦ MonoidHom.mem_ker.mpr (h r hr)

/-- Converting a subgroup to an additive subgroup commutes with topological closure. -/
@[simp]
theorem toAddSubgroup_topologicalClosure (S : Subgroup G) :
    S.topologicalClosure.toAddSubgroup = S.toAddSubgroup.topologicalClosure :=
  -- `Additive G` inherits the topology of `G`, and both subgroup closures use the
  -- set-theoretic closure of the same carrier. The definitional reduction is confined
  -- to this bridge so consumers can rewrite without unfolding these representations.
  (rfl)

end Subgroup
