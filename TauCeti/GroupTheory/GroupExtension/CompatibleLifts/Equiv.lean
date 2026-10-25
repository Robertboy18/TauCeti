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

namespace GroupExtension.CompatibleLifts

variable {N E E' G A : Type*} [Group N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (ρ : A →* MulAut G) (F : S.Equiv S')

/-- Conjugation by a native extension equivalence transports compatible lifts. -/
def mapEquiv : S.compatibleLifts ρ →* S'.compatibleLifts ρ where
  toFun x := ⟨(MulAut.congr F.toMulEquiv (toCoverAut S ρ x), projection S ρ x), by
    rw [mem_compatibleLifts]
    constructor
    · intro n
      change F (toCoverAut S ρ x (F.symm (S'.inl n))) = S'.inl n
      rw [F.symm.map_inl, toCoverAut_inl, F.map_inl]
    · intro e
      change S'.rightHom (F (toCoverAut S ρ x (F.symm e))) =
        ρ (projection S ρ x) (S'.rightHom e)
      rw [F.rightHom_map, rightHom_toCoverAut, F.symm.rightHom_map]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · change MulAut.congr F.toMulEquiv (toCoverAut S ρ 1) = 1
      rw [map_one, map_one]
    · exact (projection S ρ).map_one
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change MulAut.congr F.toMulEquiv (toCoverAut S ρ (x * y)) =
        MulAut.congr F.toMulEquiv (toCoverAut S ρ x) *
          MulAut.congr F.toMulEquiv (toCoverAut S ρ y)
      rw [map_mul, map_mul]
    · exact (projection S ρ).map_mul x y

@[simp]
theorem toCoverAut_mapEquiv (x : S.compatibleLifts ρ) :
    toCoverAut S' ρ (mapEquiv ρ F x) =
      MulAut.congr F.toMulEquiv (toCoverAut S ρ x) := by
  rw [toCoverAut_apply]
  rfl

@[simp]
theorem projection_mapEquiv (x : S.compatibleLifts ρ) :
    projection S' ρ (mapEquiv ρ F x) = projection S ρ x := by
  rw [projection_apply]
  rfl

theorem toCoverAut_mapEquiv_apply (x : S.compatibleLifts ρ) (e : E') :
    toCoverAut S' ρ (mapEquiv ρ F x) e = F (toCoverAut S ρ x (F.symm e)) := by
  rw [toCoverAut_mapEquiv, MulAut.congr_apply]
  rfl

@[simp]
theorem mapEquiv_symm_mapEquiv (x : S.compatibleLifts ρ) :
    mapEquiv ρ F.symm (mapEquiv ρ F x) = x := by
  have h : toCoverAut S ρ (mapEquiv ρ F.symm (mapEquiv ρ F x)) =
      toCoverAut S ρ x := by
    ext e
    rw [toCoverAut_mapEquiv_apply, toCoverAut_mapEquiv_apply]
    change F.toMulEquiv.symm
      (F.toMulEquiv (toCoverAut S ρ x (F.toMulEquiv.symm (F.toMulEquiv e)))) = _
    simp only [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  apply Prod.ext
  · simpa only [toCoverAut_apply] using h
  · simpa only [projection_apply] using
      (projection_mapEquiv ρ F.symm (mapEquiv ρ F x)).trans (projection_mapEquiv ρ F x)

/-- Equivalent extensions have equivalent groups of compatible lifts. -/
def congr : S.compatibleLifts ρ ≃* S'.compatibleLifts ρ where
  toFun := mapEquiv ρ F
  invFun := mapEquiv ρ F.symm
  left_inv := mapEquiv_symm_mapEquiv ρ F
  right_inv x := by
    change mapEquiv ρ F.symm.symm (mapEquiv ρ F.symm x) = x
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

include F in
/-- A native equivalence transfers centrality of the included kernel. -/
theorem central_of_equiv (hcentral : ∀ n e, Commute (S.inl n) e) :
    ∀ n e, Commute (S'.inl n) e := by
  intro n e
  obtain ⟨f, rfl⟩ := F.toMulEquiv.surjective e
  have h := (hcentral n f).map F.toMulEquiv.toMonoidHom
  change Commute (F (S.inl n)) (F f) at h
  rw [F.map_inl] at h
  exact h

end GroupExtension.CompatibleLifts

namespace GroupExtension.CompatibleLifts

variable {N E E' G A : Type*} [CommGroup N] [Group E] [Group E'] [Group G] [Group A]
  {S : GroupExtension N E G} {S' : GroupExtension N E' G}
  (ρ : A →* MulAut G) (F : S.Equiv S') (hcentral : ∀ n e, Commute (S.inl n) e)

/-- Transport through an extension equivalence preserves each character twist. -/
theorem congr_twist (χ : G →* N) :
    MulAut.congr F.toMulEquiv (twist S hcentral χ) =
      twist S' (central_of_equiv F hcentral) χ := by
  ext e
  rw [MulAut.congr_apply]
  change F (twist S hcentral χ (F.symm e)) = _
  rw [twist_apply, map_mul, F.map_inl, F.symm.rightHom_map, twist_apply]
  change S'.inl (χ (S'.rightHom e)) * F.toMulEquiv (F.toMulEquiv.symm e) = _
  rw [MulEquiv.apply_symm_apply]

@[simp]
theorem mapEquiv_character (χ : G →* N) :
    mapEquiv ρ F (character S ρ hcentral χ) =
      character S' ρ (central_of_equiv F hcentral) χ := by
  have h : toCoverAut S' ρ (mapEquiv ρ F (character S ρ hcentral χ)) =
      toCoverAut S' ρ (character S' ρ (central_of_equiv F hcentral) χ) := by
    rw [toCoverAut_mapEquiv, toCoverAut_character, toCoverAut_character, congr_twist]
  apply Subtype.ext
  apply Prod.ext
  · simpa only [toCoverAut_apply] using h
  · have hp : projection S' ρ (mapEquiv ρ F (character S ρ hcentral χ)) =
        projection S' ρ (character S' ρ (central_of_equiv F hcentral) χ) := by
      rw [projection_mapEquiv, projection_character, projection_character]
    simpa only [projection_apply] using hp

end GroupExtension.CompatibleLifts
