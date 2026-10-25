/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Compatible lifts of automorphisms of a group extension

For an extension `S` and an action `ρ` on its quotient, `S.compatibleLifts ρ` is the subgroup
of pairs consisting of an automorphism of the middle group and an element of the acting group.
The automorphism fixes the included kernel pointwise and induces the specified quotient action.
Its projection need not be surjective: `CompatibleLifts.toLiftable` restricts its codomain to
the subgroup of elements that have a lift.

The action `ρ` need not be faithful. In particular, the projection remembers the acting-group
element even when different elements induce the same quotient automorphism. Each compatible
lift also supplies a native equivalence with the quotient-relabeled extension.
-/

public section

namespace GroupExtension

variable {N E G A : Type*} [Group N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)

/-- Automorphisms fixing the included kernel, paired with the element whose quotient action
they induce. -/
def compatibleLifts : Subgroup (MulAut E × A) where
  carrier := {x | (∀ n, x.1 (S.inl n) = S.inl n) ∧
    ∀ e, S.rightHom (x.1 e) = ρ x.2 (S.rightHom e)}
  one_mem' := ⟨fun _ => rfl, fun _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxn, hxg⟩ ⟨hyn, hyg⟩
    constructor
    · intro n
      change x.1 (y.1 (S.inl n)) = S.inl n
      rw [hyn, hxn]
    · intro e
      change S.rightHom (x.1 (y.1 e)) = ρ (x.2 * y.2) (S.rightHom e)
      rw [hxg, hyg, map_mul]
      rfl
  inv_mem' := by
    rintro x ⟨hxn, hxg⟩
    constructor
    · intro n
      change x.1.symm (S.inl n) = S.inl n
      apply x.1.injective
      rw [MulEquiv.apply_symm_apply, hxn]
    · intro e
      change S.rightHom (x.1.symm e) = ρ x.2⁻¹ (S.rightHom e)
      apply (ρ x.2).injective
      simpa only [map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply] using
        (hxg (x.1.symm e)).symm

@[simp]
theorem mem_compatibleLifts (x : MulAut E × A) :
    x ∈ S.compatibleLifts ρ ↔ (∀ n, x.1 (S.inl n) = S.inl n) ∧
      ∀ e, S.rightHom (x.1 e) = ρ x.2 (S.rightHom e) :=
  Iff.rfl

namespace CompatibleLifts

/-- The action of a compatible lift on the middle group. -/
def toCoverAut : S.compatibleLifts ρ →* MulAut E :=
  (MonoidHom.fst (MulAut E) A).comp (S.compatibleLifts ρ).subtype

theorem toCoverAut_apply (x : S.compatibleLifts ρ) :
    toCoverAut S ρ x = x.val.1 :=
  (rfl)

/-- The quotient-action element recorded by a compatible lift. -/
def projection : S.compatibleLifts ρ →* A :=
  (MonoidHom.snd (MulAut E) A).comp (S.compatibleLifts ρ).subtype

theorem projection_apply (x : S.compatibleLifts ρ) :
    projection S ρ x = x.val.2 :=
  (rfl)

/-- The subgroup of acting-group elements that admit a compatible lift. -/
def liftableSubgroup : Subgroup A :=
  (projection S ρ).range

/-- Projection onto the actual subgroup of elements admitting a lift. -/
def toLiftable : S.compatibleLifts ρ →* liftableSubgroup S ρ :=
  (projection S ρ).rangeRestrict

@[simp]
theorem coe_toLiftable (x : S.compatibleLifts ρ) :
    (toLiftable S ρ x : A) = projection S ρ x :=
  (rfl)

theorem toLiftable_surjective : Function.Surjective (toLiftable S ρ) :=
  (projection S ρ).rangeRestrict_surjective

theorem ker_toLiftable : (toLiftable S ρ).ker = (projection S ρ).ker := by
  ext x
  simp only [MonoidHom.mem_ker, Subtype.ext_iff, coe_toLiftable, OneMemClass.coe_one]

theorem toCoverAut_inl (x : S.compatibleLifts ρ) (n : N) :
    toCoverAut S ρ x (S.inl n) = S.inl n :=
  x.property.1 n

theorem rightHom_toCoverAut (x : S.compatibleLifts ρ) (e : E) :
    S.rightHom (toCoverAut S ρ x e) = ρ (projection S ρ x) (S.rightHom e) :=
  x.property.2 e

/-- A compatible lift is an equivalence from the quotient-relabeled extension to the
original extension. -/
def toExtensionEquiv (x : S.compatibleLifts ρ) :
    (S.relabelQuotient (ρ (projection S ρ x))).Equiv S where
  toMulEquiv := toCoverAut S ρ x
  inl_comm := by
    ext n
    simpa only [Function.comp_apply, relabelQuotient_inl] using toCoverAut_inl S ρ x n
  rightHom_comm := by
    ext e
    simpa only [Function.comp_apply, relabelQuotient_rightHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] using rightHom_toCoverAut S ρ x e

@[simp]
theorem toExtensionEquiv_apply (x : S.compatibleLifts ρ) (e : E) :
    toExtensionEquiv S ρ x e = toCoverAut S ρ x e :=
  (rfl)

end CompatibleLifts

end GroupExtension
