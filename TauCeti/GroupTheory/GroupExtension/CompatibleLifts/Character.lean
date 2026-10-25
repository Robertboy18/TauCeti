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

namespace GroupExtension.CompatibleLifts

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : ∀ n e, Commute (S.inl n) e)

/-- The automorphism obtained by multiplying each element by its character value. -/
def twist (χ : G →* N) : MulAut E where
  toFun e := S.inl (χ (S.rightHom e)) * e
  invFun e := S.inl (χ (S.rightHom e))⁻¹ * e
  left_inv e := by simp
  right_inv e := by simp
  map_mul' e f := by
    simp only [map_mul]
    exact (hcentral (χ (S.rightHom f)) e).mul_mul_mul_comm _ _

@[simp]
theorem twist_apply (χ : G →* N) (e : E) :
    twist S hcentral χ e = S.inl (χ (S.rightHom e)) * e :=
  (rfl)

@[simp]
theorem twist_symm_apply (χ : G →* N) (e : E) :
    (twist S hcentral χ).symm e = S.inl (χ (S.rightHom e))⁻¹ * e :=
  (rfl)

theorem twist_inl (χ : G →* N) (n : N) :
    twist S hcentral χ (S.inl n) = S.inl n := by
  simp

theorem rightHom_twist (χ : G →* N) (e : E) :
    S.rightHom (twist S hcentral χ e) = S.rightHom e := by
  simp

/-- Characters define compatible lifts with acting-group coordinate equal to one. -/
def character : (G →* N) →* S.compatibleLifts ρ where
  toFun χ := ⟨(twist S hcentral χ, 1), by
    rw [mem_compatibleLifts]
    constructor
    · exact twist_inl S hcentral χ
    · intro e
      simp⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · ext e
      simp
    · rfl
  map_mul' χ ψ := by
    apply Subtype.ext
    apply Prod.ext
    · ext e
      simp [mul_assoc]
    · simp

@[simp]
theorem toCoverAut_character (χ : G →* N) :
    toCoverAut S ρ (character S ρ hcentral χ) = twist S hcentral χ := by
  rw [toCoverAut_apply]
  rfl

@[simp]
theorem projection_character (χ : G →* N) :
    projection S ρ (character S ρ hcentral χ) = 1 := by
  rw [projection_apply]
  rfl

theorem character_injective : Function.Injective (character S ρ hcentral) := by
  intro χ ψ h
  ext g
  obtain ⟨e, rfl⟩ := S.rightHom_surjective g
  have he := congrArg (fun x => toCoverAut S ρ x e) h
  simpa only [toCoverAut_character, twist_apply, mul_left_inj, S.inl_injective.eq_iff] using he

/-- The displacement of a lift over the identity, expressed in the included kernel. -/
noncomputable def kernelDeviation (x : (projection S ρ).ker) (e : E) : N :=
  Function.invFun S.inl (toCoverAut S ρ x.val e * e⁻¹)

theorem inl_kernelDeviation (x : (projection S ρ).ker) (e : E) :
    S.inl (kernelDeviation S ρ x e) = toCoverAut S ρ x.val e * e⁻¹ := by
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, rightHom_toCoverAut, MonoidHom.mem_ker.mp x.property,
    map_one, MulAut.one_apply, mul_inv_cancel]

/-- The displacement is multiplicative because the included kernel is central. -/
noncomputable def kernelDeviationHom (x : (projection S ρ).ker) : E →* N where
  toFun := kernelDeviation S ρ x
  map_one' := by
    apply S.inl_injective
    simp [inl_kernelDeviation]
  map_mul' e f := by
    apply S.inl_injective
    rw [map_mul, inl_kernelDeviation, inl_kernelDeviation, inl_kernelDeviation, map_mul,
      mul_inv_rev]
    have hc := hcentral (kernelDeviation S ρ x f) e⁻¹
    rw [inl_kernelDeviation] at hc
    calc
      toCoverAut S ρ x.val e * toCoverAut S ρ x.val f * (f⁻¹ * e⁻¹) =
          toCoverAut S ρ x.val e * ((toCoverAut S ρ x.val f * f⁻¹) * e⁻¹) := by
        simp only [mul_assoc]
      _ = toCoverAut S ρ x.val e * (e⁻¹ * (toCoverAut S ρ x.val f * f⁻¹)) := by
        rw [hc.eq]
      _ = (toCoverAut S ρ x.val e * e⁻¹) * (toCoverAut S ρ x.val f * f⁻¹) :=
        (mul_assoc _ _ _).symm

@[simp]
theorem kernelDeviationHom_apply (x : (projection S ρ).ker) (e : E) :
    kernelDeviationHom S ρ hcentral x e = kernelDeviation S ρ x e :=
  (rfl)

theorem ker_rightHom_le_ker_kernelDeviationHom (x : (projection S ρ).ker) :
    S.rightHom.ker ≤ (kernelDeviationHom S ρ hcentral x).ker := by
  intro e he
  rw [← S.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, rfl⟩ := he
  change kernelDeviation S ρ x (S.inl n) = 1
  apply S.inl_injective
  rw [inl_kernelDeviation, toCoverAut_inl, mul_inv_cancel, map_one]

/-- Recover the quotient character of a lift over the identity by descending its displacement. -/
noncomputable def kernelCharacter (x : (projection S ρ).ker) : G →* N :=
  S.rightHom.liftOfSurjective S.rightHom_surjective
    ⟨kernelDeviationHom S ρ hcentral x, ker_rightHom_le_ker_kernelDeviationHom S ρ hcentral x⟩

theorem kernelCharacter_rightHom (x : (projection S ρ).ker) (e : E) :
    kernelCharacter S ρ hcentral x (S.rightHom e) = kernelDeviation S ρ x e := by
  simp [kernelCharacter]

theorem inl_kernelCharacter_rightHom (x : (projection S ρ).ker) (e : E) :
    S.inl (kernelCharacter S ρ hcentral x (S.rightHom e)) =
      toCoverAut S ρ x.val e * e⁻¹ := by
  rw [kernelCharacter_rightHom, inl_kernelDeviation]

/-- The recovered character can be evaluated on any set-theoretic section. -/
theorem inl_kernelCharacter_section (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    S.inl (kernelCharacter S ρ hcentral x g) =
      toCoverAut S ρ x.val (σ g) * (σ g)⁻¹ := by
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
  rw [inl_kernelCharacter_rightHom, coe_characterToKernel, toCoverAut_character, twist_apply,
    mul_inv_cancel_right]

@[simp]
theorem character_kernelCharacter (x : (projection S ρ).ker) :
    character S ρ hcentral (kernelCharacter S ρ hcentral x) = x.val := by
  apply Subtype.ext
  apply Prod.ext
  · apply MulEquiv.ext
    intro e
    change twist S hcentral (kernelCharacter S ρ hcentral x) e = x.val.val.1 e
    rw [twist_apply, inl_kernelCharacter_rightHom, inv_mul_cancel_right, toCoverAut_apply]
  · change 1 = x.val.val.2
    simpa only [projection_apply] using (MonoidHom.mem_ker.mp x.property).symm

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
  rfl

theorem rightHom_toCoverAut_symm (x : S.compatibleLifts ρ) (e : E) :
    S.rightHom ((toCoverAut S ρ x).symm e) =
      (ρ (projection S ρ x)).symm (S.rightHom e) := by
  apply (ρ (projection S ρ x)).injective
  simpa only [MulEquiv.apply_symm_apply] using
    (rightHom_toCoverAut S ρ x ((toCoverAut S ρ x).symm e)).symm

/-- Conjugating a character twist pulls the character back by the inverse quotient action. -/
theorem conjugate_twist (x : S.compatibleLifts ρ) (χ : G →* N) :
    toCoverAut S ρ x * twist S hcentral χ * (toCoverAut S ρ x)⁻¹ =
      twist S hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom) := by
  ext e
  change toCoverAut S ρ x (twist S hcentral χ ((toCoverAut S ρ x).symm e)) = _
  rw [twist_apply, map_mul, toCoverAut_inl, MulEquiv.apply_symm_apply, twist_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, rightHom_toCoverAut_symm]

/-- The kernel action of compatible lifts is the inverse-pullback action on characters. -/
theorem conjugate_character (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * character S ρ hcentral χ * x⁻¹ =
      character S ρ hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom) := by
  apply Subtype.ext
  apply Prod.ext
  · change x.val.1 * twist S hcentral χ * x.val.1⁻¹ =
      twist S hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom)
    simpa only [toCoverAut_apply] using conjugate_twist S ρ hcentral x χ
  · change x.val.2 * 1 * x.val.2⁻¹ = 1
    simp

/-- Two lifts of the same acting-group element differ by a unique source character twist. -/
theorem existsUnique_eq_mul_character (x y : S.compatibleLifts ρ)
    (h : projection S ρ x = projection S ρ y) :
    ∃! χ : G →* N, y = x * character S ρ hcentral χ := by
  let z : (projection S ρ).ker := ⟨x⁻¹ * y, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]⟩
  have hz := character_kernelCharacter S ρ hcentral z
  refine ⟨kernelCharacter S ρ hcentral z, ?_, ?_⟩
  · change y = x * character S ρ hcentral (kernelCharacter S ρ hcentral z)
    rw [hz]
    exact (mul_inv_cancel_left x y).symm
  · intro ψ hψ
    apply character_injective S ρ hcentral
    apply mul_left_cancel (a := x)
    rw [← hψ, hz]
    exact (mul_inv_cancel_left x y).symm

/-- A source character twist multiplies the image of each element by its original character
value, since a compatible lift fixes the included kernel. -/
theorem toCoverAut_mul_character (x : S.compatibleLifts ρ) (χ : G →* N) (e : E) :
    toCoverAut S ρ (x * character S ρ hcentral χ) e =
      S.inl (χ (S.rightHom e)) * toCoverAut S ρ x e := by
  rw [map_mul, MulAut.mul_apply, toCoverAut_character, twist_apply, map_mul, toCoverAut_inl]

include hcentral in
/-- Two lifts of the same acting-group element differ pointwise by a unique quotient character. -/
theorem existsUnique_toCoverAut_eq_inl_mul (x y : S.compatibleLifts ρ)
    (h : projection S ρ x = projection S ρ y) :
    ∃! χ : G →* N, ∀ e, toCoverAut S ρ y e =
      S.inl (χ (S.rightHom e)) * toCoverAut S ρ x e := by
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_eq_mul_character S ρ hcentral x y h
  refine ⟨χ, ?_, ?_⟩
  · intro e
    rw [hχ, toCoverAut_mul_character]
  · intro ψ hψ
    apply huniq ψ
    apply Subtype.ext
    apply Prod.ext
    · apply MulEquiv.ext
      intro e
      have he := hψ e
      rw [← toCoverAut_mul_character S ρ hcentral] at he
      simpa only [toCoverAut_apply] using he
    · have hp : projection S ρ y = projection S ρ (x * character S ρ hcentral ψ) := by
        rw [map_mul, projection_character, mul_one]
        exact h.symm
      simpa only [projection_apply] using hp

/-- Moving a source twist past a lift replaces its character by inverse pullback. -/
theorem mul_character_eq_character_mul (x : S.compatibleLifts ρ) (χ : G →* N) :
    x * character S ρ hcentral χ =
      character S ρ hcentral (χ.comp (ρ (projection S ρ x)).symm.toMonoidHom) * x := by
  rw [← conjugate_character]
  simp only [inv_mul_cancel_right]

end GroupExtension.CompatibleLifts
