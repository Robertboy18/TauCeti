/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Distributive actions on the quotient by a stable additive subgroup

Let a group `G` act distributively on an additive commutative group `M`, and let `N` be an
additive subgroup of `M` that is `G`-stable, in the sense that `g • x ∈ N` for every `g : G` and
`x ∈ N`. Then `G` acts distributively on the quotient `M ⧸ N` by `g • ↑x = ↑(g • x)`. Mathlib
provides this action for submodules (`Submodule.Quotient.distribMulAction`) but not for a bare
`G`-stable additive subgroup, where the stability is a hypothesis rather than an instance, so
the action is a definition rather than an instance.

The file also records that stability passes to `N ⊔ zmultiples x` when the class of `x` is fixed
by `G` modulo `N`, which is what lets a `G`-stable subgroup be enlarged one element at a time.

## Main declarations

* `AddSubgroup.quotientDistribMulAction`: the action of `G` on `M ⧸ N` for a `G`-stable `N`.
* `AddSubgroup.quotientDistribMulAction_smul_mk`: its defining equation `g • ↑x = ↑(g • x)`.
* `TauCeti.smul_mem_sup_zmultiples`: if `N` is `G`-stable and `g • x - x ∈ N` for every `g`,
  then `N ⊔ zmultiples x` is `G`-stable.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- The action of `G` on the quotient of `M` by a `G`-stable additive subgroup `N`, with
`g • ↑x = ↑(g • x)`. It is a definition rather than an instance because it depends on the
stability hypothesis. See note [reducible non-instances]. -/
abbrev _root_.AddSubgroup.quotientDistribMulAction (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) : DistribMulAction G (M ⧸ N) where
  smul g := QuotientAddGroup.map N N (DistribSMul.toAddMonoidHom M g) fun x hx ↦ hN g x hx
  one_smul x :=
    QuotientAddGroup.induction_on x fun x ↦ congrArg QuotientAddGroup.mk (one_smul G x)
  mul_smul g h x :=
    QuotientAddGroup.induction_on x fun x ↦ congrArg QuotientAddGroup.mk (mul_smul g h x)
  smul_zero g := map_zero (QuotientAddGroup.map N N (DistribSMul.toAddMonoidHom M g) _)
  smul_add g := map_add (QuotientAddGroup.map N N (DistribSMul.toAddMonoidHom M g) _)

/-- The defining equation of `AddSubgroup.quotientDistribMulAction` on the class of an
element. -/
@[simp]
theorem _root_.AddSubgroup.quotientDistribMulAction_smul_mk (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (g : G) (x : M) :
    letI := N.quotientDistribMulAction hN
    g • (x : M ⧸ N) = ((g • x : M) : M ⧸ N) :=
  rfl

/-- If `N` is `G`-stable and `g • x - x ∈ N` for every `g`, then `N ⊔ zmultiples x` is
`G`-stable. -/
theorem smul_mem_sup_zmultiples {N : AddSubgroup M} (hN : ∀ g : G, ∀ y ∈ N, g • y ∈ N) {x : M}
    (hx : ∀ g : G, g • x - x ∈ N) (g : G) {y : M} (hy : y ∈ N ⊔ AddSubgroup.zmultiples x) :
    g • y ∈ N ⊔ AddSubgroup.zmultiples x := by
  obtain ⟨n, hn, m, hm, rfl⟩ := AddSubgroup.mem_sup.mp hy
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  have : g • (n + k • x) = (g • n + k • (g • x - x)) + k • x := by
    rw [smul_add, smul_comm, zsmul_sub, add_assoc, sub_add_cancel]
  rw [this]
  exact AddSubgroup.add_mem _
    (AddSubgroup.mem_sup_left
      (AddSubgroup.add_mem _ (hN g n hn) (AddSubgroup.zsmul_mem _ (hx g) k)))
    (AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples x) k))

end TauCeti
