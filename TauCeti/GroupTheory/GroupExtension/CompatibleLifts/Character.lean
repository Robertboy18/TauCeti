/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Basic
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# Characters in the kernel of compatible lifts

A character of the quotient of a central extension acts on the middle group by multiplying
each element by its character value in the included kernel. These twists account for every
compatible lift lying over the identity.
-/

public section

namespace TauCeti.GroupExtension.CompatibleLifts

open _root_.GroupExtension

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : S.inl.range ≤ Subgroup.center E)

/-- Characters define compatible lifts with acting-group coordinate equal to one. -/
def character : (G →* N) →* S.compatibleLifts ρ where
  toFun χ := ⟨(twist S hcentral χ, 1), by
    rw [mem_compatibleLifts]
    constructor
    · exact twist_inl S hcentral χ
    · intro e
      simp⟩
  map_one' := by
    apply ext S ρ
    · ext e
      simp [toMulAut_apply]
    · simp only [projection_apply, OneMemClass.coe_one, Prod.snd_one]
  map_mul' χ ψ := by
    apply ext S ρ
    · ext e
      simp [toMulAut_apply, mul_assoc]
    · simp [projection_apply]

@[simp]
theorem toMulAut_character (χ : G →* N) :
    toMulAut S ρ (character S ρ hcentral χ) = twist S hcentral χ :=
  toMulAut_apply S ρ _

@[simp]
theorem projection_character (χ : G →* N) :
    projection S ρ (character S ρ hcentral χ) = 1 :=
  projection_apply S ρ _

theorem character_injective : Function.Injective (character S ρ hcentral) := by
  intro χ ψ h
  ext g
  obtain ⟨e, rfl⟩ := S.rightHom_surjective g
  have he := congrArg (fun x => toMulAut S ρ x e) h
  simpa only [toMulAut_character, twist_apply, mul_left_inj, S.inl_injective.eq_iff] using he

/-- The displacement of a lift over the identity, expressed in the included kernel. -/
private noncomputable def kernelDeviation (x : (projection S ρ).ker) (e : E) : N :=
  inlInv S (toMulAut S ρ x.val e * e⁻¹)

private theorem inl_kernelDeviation (x : (projection S ρ).ker) (e : E) :
    S.inl (kernelDeviation S ρ x e) = toMulAut S ρ x.val e * e⁻¹ := by
  apply inl_inlInv
  rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, rightHom_toMulAut, MonoidHom.mem_ker.mp x.property,
    map_one, MulAut.one_apply, mul_inv_cancel]

/-- The displacement is multiplicative because the included kernel is central. -/
private noncomputable def kernelDeviationHom (x : (projection S ρ).ker) : E →* N where
  toFun := kernelDeviation S ρ x
  map_one' := by
    apply S.inl_injective
    simp [inl_kernelDeviation]
  map_mul' e f := by
    apply S.inl_injective
    rw [map_mul, inl_kernelDeviation, inl_kernelDeviation, inl_kernelDeviation, map_mul,
      mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp (hcentral ⟨kernelDeviation S ρ x f, rfl⟩) e⁻¹
    rw [inl_kernelDeviation] at hc
    calc
      toMulAut S ρ x.val e * toMulAut S ρ x.val f * (f⁻¹ * e⁻¹) =
          toMulAut S ρ x.val e * ((toMulAut S ρ x.val f * f⁻¹) * e⁻¹) := by
        simp only [mul_assoc]
      _ = toMulAut S ρ x.val e * (e⁻¹ * (toMulAut S ρ x.val f * f⁻¹)) := by
        rw [hc]
      _ = (toMulAut S ρ x.val e * e⁻¹) * (toMulAut S ρ x.val f * f⁻¹) :=
        (mul_assoc _ _ _).symm

@[simp]
private theorem kernelDeviationHom_apply (x : (projection S ρ).ker) (e : E) :
    kernelDeviationHom S ρ hcentral x e = kernelDeviation S ρ x e :=
  (rfl)

private theorem ker_rightHom_le_ker_kernelDeviationHom (x : (projection S ρ).ker) :
    S.rightHom.ker ≤ (kernelDeviationHom S ρ hcentral x).ker := by
  intro e he
  rw [← S.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, rfl⟩ := he
  rw [MonoidHom.mem_ker, kernelDeviationHom_apply]
  apply S.inl_injective
  rw [inl_kernelDeviation, toMulAut_inl, mul_inv_cancel, map_one]

/-- Recover the quotient character of a lift over the identity by descending its displacement. -/
noncomputable def kernelCharacter (x : (projection S ρ).ker) : G →* N :=
  S.rightHom.liftOfSurjective S.rightHom_surjective
    ⟨kernelDeviationHom S ρ hcentral x, ker_rightHom_le_ker_kernelDeviationHom S ρ hcentral x⟩

private theorem kernelCharacter_rightHom (x : (projection S ρ).ker) (e : E) :
    kernelCharacter S ρ hcentral x (S.rightHom e) = kernelDeviation S ρ x e := by
  simp [kernelCharacter]

theorem inl_kernelCharacter_rightHom (x : (projection S ρ).ker) (e : E) :
    S.inl (kernelCharacter S ρ hcentral x (S.rightHom e)) =
      toMulAut S ρ x.val e * e⁻¹ := by
  rw [kernelCharacter_rightHom, inl_kernelDeviation]

/-- The recovered character can be evaluated on any set-theoretic section. -/
theorem inl_kernelCharacter_section (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    S.inl (kernelCharacter S ρ hcentral x g) =
      toMulAut S ρ x.val (σ g) * (σ g)⁻¹ := by
  simpa only [Section.rightHom_section] using
    inl_kernelCharacter_rightHom S ρ hcentral x (σ g)

/-- Character twists, with their codomain restricted to the kernel of the projection. -/
def characterToKernel : (G →* N) →* (projection S ρ).ker :=
  (character S ρ hcentral).codRestrict _ (fun χ => projection_character S ρ hcentral χ)

@[simp]
theorem coe_characterToKernel (χ : G →* N) :
    (characterToKernel S ρ hcentral χ : S.compatibleLifts ρ) = character S ρ hcentral χ :=
  (rfl)

@[simp]
theorem kernelCharacter_characterToKernel (χ : G →* N) :
    kernelCharacter S ρ hcentral (characterToKernel S ρ hcentral χ) = χ := by
  ext g
  obtain ⟨e, rfl⟩ := S.rightHom_surjective g
  apply S.inl_injective
  rw [inl_kernelCharacter_rightHom, coe_characterToKernel, toMulAut_character, twist_apply,
    mul_inv_cancel_right]

@[simp]
theorem character_kernelCharacter (x : (projection S ρ).ker) :
    character S ρ hcentral (kernelCharacter S ρ hcentral x) = x.val := by
  apply ext S ρ
  · apply MulEquiv.ext
    intro e
    rw [toMulAut_character, twist_apply, inl_kernelCharacter_rightHom, inv_mul_cancel_right]
  · rw [projection_character]
    exact (MonoidHom.mem_ker.mp x.property).symm

/-- The full kernel of compatible lifts is the group of characters of the quotient. The inverse
is the descended displacement `kernelCharacter`, with no choice of a normalized section. -/
noncomputable def kernelEquiv : (G →* N) ≃* (projection S ρ).ker where
  toFun := characterToKernel S ρ hcentral
  invFun := kernelCharacter S ρ hcentral
  left_inv := kernelCharacter_characterToKernel S ρ hcentral
  right_inv x := Subtype.ext (character_kernelCharacter S ρ hcentral x)
  map_mul' := (characterToKernel S ρ hcentral).map_mul

@[simp]
theorem kernelEquiv_apply (χ : G →* N) :
    kernelEquiv S ρ hcentral χ = characterToKernel S ρ hcentral χ :=
  (rfl)

@[simp]
theorem kernelEquiv_symm_apply (x : (projection S ρ).ker) :
    (kernelEquiv S ρ hcentral).symm x = kernelCharacter S ρ hcentral x :=
  (rfl)

/-- The native extension over precisely those acting-group elements that have lifts. -/
noncomputable def extension :
    GroupExtension (G →* N) (S.compatibleLifts ρ) (liftableSubgroup S ρ) :=
  GroupExtension.ofMulEquivKer (toLiftable_surjective S ρ)
    ((kernelEquiv S ρ hcentral).trans (MulEquiv.subgroupCongr (ker_toLiftable S ρ).symm))

@[simp]
theorem extension_rightHom :
    (extension S ρ hcentral).rightHom = toLiftable S ρ := by
  rw [extension, GroupExtension.ofMulEquivKer_rightHom]

@[simp]
theorem extension_inl (χ : G →* N) :
    (extension S ρ hcentral).inl χ = character S ρ hcentral χ := by
  rw [extension, GroupExtension.ofMulEquivKer_inl]
  -- The transported kernel equivalence preserves the underlying compatible lift.
  rfl

/-- When every acting-group element admits a lift, the same kernel describes an extension
over the whole acting group. -/
noncomputable def extensionOfSurjective (h : Function.Surjective (projection S ρ)) :
    GroupExtension (G →* N) (S.compatibleLifts ρ) A :=
  GroupExtension.ofMulEquivKer h (kernelEquiv S ρ hcentral)

@[simp]
theorem extensionOfSurjective_rightHom (h : Function.Surjective (projection S ρ)) :
    (extensionOfSurjective S ρ hcentral h).rightHom = projection S ρ := by
  rw [extensionOfSurjective, GroupExtension.ofMulEquivKer_rightHom]

@[simp]
theorem extensionOfSurjective_inl (h : Function.Surjective (projection S ρ)) (χ : G →* N) :
    (extensionOfSurjective S ρ hcentral h).inl χ = character S ρ hcentral χ := by
  rw [extensionOfSurjective, GroupExtension.ofMulEquivKer_inl]
  -- Kernel restriction changes only the membership proof.
  rfl

/-- The kernel action of compatible lifts is the inverse-pullback action on characters. -/
theorem conjugate_character (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * character S ρ hcentral χ * x⁻¹ =
      character S ρ hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom) := by
  apply ext S ρ
  · simpa only [map_mul, map_inv, toMulAut_character] using conjugate_twist S ρ hcentral x χ
  · simp only [map_mul, map_inv, projection_character, mul_one, mul_inv_cancel]

/-- Two lifts of the same acting-group element differ by a unique source character twist. -/
theorem existsUnique_eq_mul_character (x y : S.compatibleLifts ρ)
    (h : projection S ρ x = projection S ρ y) :
    ∃! χ : G →* N, y = x * character S ρ hcentral χ := by
  let z : (projection S ρ).ker := ⟨x⁻¹ * y, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]⟩
  have hz := character_kernelCharacter S ρ hcentral z
  refine ⟨kernelCharacter S ρ hcentral z, ?_, ?_⟩
  · dsimp only
    rw [hz]
    exact (mul_inv_cancel_left x y).symm
  · intro ψ hψ
    apply character_injective S ρ hcentral
    apply mul_left_cancel (a := x)
    rw [← hψ, hz]
    exact (mul_inv_cancel_left x y).symm

/-- A source character twist multiplies the image of each element by its original character
value, since a compatible lift fixes the included kernel. -/
theorem toMulAut_mul_character (x : S.compatibleLifts ρ) (χ : G →* N) (e : E) :
    toMulAut S ρ (x * character S ρ hcentral χ) e =
      S.inl (χ (S.rightHom e)) * toMulAut S ρ x e := by
  rw [map_mul, MulAut.mul_apply, toMulAut_character, twist_apply, map_mul, toMulAut_inl]

include hcentral in
/-- Two lifts of the same acting-group element differ pointwise by a unique quotient character. -/
theorem existsUnique_toMulAut_eq_inl_mul (x y : S.compatibleLifts ρ)
    (h : projection S ρ x = projection S ρ y) :
    ∃! χ : G →* N, ∀ e, toMulAut S ρ y e =
      S.inl (χ (S.rightHom e)) * toMulAut S ρ x e := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_eq_mul_character S ρ hcentral x y h
  refine ⟨χ, ?_, ?_⟩
  · intro e
    rw [hχ, toMulAut_mul_character]
  · intro ψ hψ
    apply huniq ψ
    apply ext S ρ
    · apply MulEquiv.ext
      intro e
      rw [toMulAut_mul_character]
      exact hψ e
    · rw [map_mul, projection_character, mul_one]
      exact h.symm

/-- Moving a source twist past a lift replaces its character by inverse pullback. -/
theorem mul_character_eq_character_mul (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * character S ρ hcentral χ =
      character S ρ hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom) * x := by
  rw [← conjugate_character]
  simp only [inv_mul_cancel_right]

end TauCeti.GroupExtension.CompatibleLifts
