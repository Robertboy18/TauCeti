/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Subgroups and topological closure

This file records how subgroup constructions interact with topological closure. It also provides
normality of the closure of a normal closure, the kernel criterion for a closed normal closure,
and compatibility of multiplicative and additive subgroup closures.

Mathlib's theorem that the topological closure of a subgroup is closed is registered as an
instance, so that the quotient of a topological group by the topological closure of a normal
subgroup is found to be a Hausdorff topological group by instance search alone.

The **closed normal closure** of a set `s`, the topological closure of `Subgroup.normalClosure s`,
is the least closed normal subgroup containing `s`
(`Subgroup.topologicalClosure_normalClosure_le_iff`), and it is `N` itself when `s` is the carrier
of a closed normal subgroup `N` (`Subgroup.topologicalClosure_normalClosure_eq_self`). This is the
fact behind the universal property of a group presented by generators and relators inside a
category of topological groups.

## Main results

* `Subgroup.instIsClosedTopologicalClosure`: the topological closure of a subgroup is closed.
* `TauCeti.instNormal_topologicalClosure_normalClosure`: the closure of a normal closure is
  normal.
* `TauCeti.topologicalClosure_normalClosure_le_ker`: relators killed by a continuous map have
  closed normal closure in its kernel.
* `Subgroup.topologicalClosure_normalClosure_le_iff`: the closed normal closure is the least closed
  normal subgroup containing the set.
* `Subgroup.topologicalClosure_normalClosure_eq_self`: the closed normal closure of a closed normal
  subgroup is that subgroup.
* `Subgroup.toAddSubgroup_topologicalClosure`: converting to an additive subgroup commutes with
  topological closure.
-/

public section

namespace TauCeti

/-- The closure of the normal closure of a set is a normal subgroup. -/
instance instNormal_topologicalClosure_normalClosure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (s : Set G) :
    ((Subgroup.normalClosure s).topologicalClosure).Normal := by
  exact Subgroup.is_normal_topologicalClosure _

end TauCeti

namespace TauCeti

/-- The closed normal closure of relators lies in the kernel of a continuous homomorphism that
kills them. -/
theorem topologicalClosure_normalClosure_le_ker {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [T1Space H] {s : Set G}
    {f : G →ₜ* H} (hf : ∀ r ∈ s, f r = 1) :
    (Subgroup.normalClosure s).topologicalClosure ≤ f.toMonoidHom.ker := by
  exact Subgroup.topologicalClosure_minimal (Subgroup.normalClosure s)
    (Subgroup.normalClosure_le_normal fun r hr ↦ MonoidHom.mem_ker.mpr (hf r hr))
    (isClosed_singleton.preimage f.continuous)

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The topological closure of a subgroup is closed. -/
instance instIsClosedTopologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) :=
  s.isClosed_topologicalClosure

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

/-- Converting a subgroup to an additive subgroup commutes with topological closure. -/
@[simp]
theorem toAddSubgroup_topologicalClosure (S : Subgroup G) :
    S.topologicalClosure.toAddSubgroup = S.toAddSubgroup.topologicalClosure :=
  -- `Additive G` inherits the topology of `G`, and both subgroup closures use the
  -- set-theoretic closure of the same carrier. The definitional reduction is confined
  -- to this bridge so consumers can rewrite without unfolding these representations.
  (rfl)

end Subgroup
