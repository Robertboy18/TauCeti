/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Character

/-!
# Transport of compatible lifts

An equivalence of group extensions fixing the kernel and quotient transports compatible
lifts by conjugating their automorphisms of the middle group. It preserves the recorded
acting-group element and, for central extensions, the character twists.
-/

public section

namespace TauCeti.CompatibleLifts

open _root_.GroupExtension

variable {N E E' G A : Type*} [Group N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (ρ : A →* MulAut G) (F : S.Equiv S')

/-- Conjugation by a native extension equivalence transports compatible lifts. -/
def mapEquiv : S.compatibleLifts ρ →* S'.compatibleLifts ρ where
  toFun x := ⟨(MulAut.congr F.toMulEquiv (toMulAut S ρ x), projection S ρ x), by
    rw [mem_compatibleLifts]
    constructor
    · intro n
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, Equiv.toMulEquiv_eq_coe,
        Equiv.coe_toMulEquiv, Equiv.coe_symm]
      rw [F.symm.map_inl, toMulAut_inl, F.map_inl]
    · intro e
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, Equiv.toMulEquiv_eq_coe,
        Equiv.coe_toMulEquiv, Equiv.coe_symm]
      rw [F.rightHom_map, rightHom_toMulAut, F.symm.rightHom_map]⟩
  map_one' := by
    apply ext S' ρ
    · simpa only [toMulAut_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        OneMemClass.coe_one, Prod.fst_one] using
        ((MulAut.congr F.toMulEquiv).toMonoidHom.comp (toMulAut S ρ)).map_one
    · simp only [projection_apply, OneMemClass.coe_one, Prod.snd_one]
  map_mul' x y := by
    apply ext S' ρ
    · simp only [map_mul, toMulAut_apply]
    · simp only [map_mul, projection_apply]

@[simp]
theorem toMulAut_mapEquiv (x : S.compatibleLifts ρ) :
    toMulAut S' ρ (mapEquiv ρ F x) =
      MulAut.congr F.toMulEquiv (toMulAut S ρ x) :=
  toMulAut_apply S' ρ _

@[simp]
theorem projection_mapEquiv (x : S.compatibleLifts ρ) :
    projection S' ρ (mapEquiv ρ F x) = projection S ρ x :=
  projection_apply S' ρ _

theorem toMulAut_mapEquiv_apply (x : S.compatibleLifts ρ) (e : E') :
    toMulAut S' ρ (mapEquiv ρ F x) e = F (toMulAut S ρ x (F.symm e)) := by
  simp only [toMulAut_mapEquiv, MulAut.congr_apply, MulEquiv.trans_apply, Equiv.toMulEquiv_eq_coe,
    Equiv.coe_toMulEquiv, Equiv.coe_symm]

@[simp]
theorem mapEquiv_symm_mapEquiv (x : S.compatibleLifts ρ) :
    mapEquiv ρ F.symm (mapEquiv ρ F x) = x := by
  apply ext S ρ
  · ext e
    rw [toMulAut_mapEquiv_apply, toMulAut_mapEquiv_apply]
    -- Expose the underlying equivalence so its two inverse laws apply.
    change F.toMulEquiv.symm
      (F.toMulEquiv (toMulAut S ρ x (F.toMulEquiv.symm (F.toMulEquiv e)))) = _
    simp only [MulEquiv.symm_apply_apply]
  · rw [projection_mapEquiv, projection_mapEquiv]

/-- Equivalent extensions have equivalent groups of compatible lifts. -/
def congr : S.compatibleLifts ρ ≃* S'.compatibleLifts ρ where
  toFun := mapEquiv ρ F
  invFun := mapEquiv ρ F.symm
  left_inv := mapEquiv_symm_mapEquiv ρ F
  right_inv x := by
    -- Taking the inverse twice preserves the underlying extension equivalence definitionally.
    exact mapEquiv_symm_mapEquiv ρ F.symm x
  map_mul' := (mapEquiv ρ F).map_mul

@[simp]
theorem congr_apply (x : S.compatibleLifts ρ) :
    congr ρ F x = mapEquiv ρ F x :=
  (rfl)

@[simp]
theorem congr_symm_apply (x : S'.compatibleLifts ρ) :
    (congr ρ F).symm x = mapEquiv ρ F.symm x :=
  (rfl)

/-- Transport through an extension equivalence preserves each character twist. -/
theorem congr_twist (hcentral : S.inl.range ≤ Subgroup.center E) (χ : G →* N) :
    MulAut.congr F.toMulEquiv (twist S hcentral χ) =
      twist S' (F.inl_range_le_center hcentral) χ := by
  ext e
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, Equiv.toMulEquiv_eq_coe,
    Equiv.coe_toMulEquiv,
    Equiv.coe_symm, twist_apply, map_mul, F.map_inl, F.symm.rightHom_map]
  simpa only [Equiv.toMulEquiv_eq_coe, Equiv.coe_toMulEquiv, Equiv.coe_symm] using
    congrArg (S'.inl (χ (S'.rightHom e)) * ·) (F.toMulEquiv.apply_symm_apply e)

end TauCeti.CompatibleLifts

namespace TauCeti.CompatibleLifts

open _root_.GroupExtension

variable {N E E' G A : Type*} [CommGroup N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (ρ : A →* MulAut G) (F : S.Equiv S') (hcentral : S.inl.range ≤ Subgroup.center E)

@[simp]
theorem mapEquiv_character (χ : G →* N) :
    mapEquiv ρ F (character S ρ hcentral χ) =
      character S' ρ (F.inl_range_le_center hcentral) χ := by
  apply ext S' ρ
  · rw [toMulAut_mapEquiv, toMulAut_character, toMulAut_character, congr_twist]
  · rw [projection_mapEquiv, projection_character, projection_character]

end TauCeti.CompatibleLifts
