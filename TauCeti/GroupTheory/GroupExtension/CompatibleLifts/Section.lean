/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Character
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# Section differences of compatible lifts

A compatible lift with acting-group coordinate one transports each section to another section
of the same extension. The native difference of these two sections is its recovered character.
The sections need not be normalized or multiplicative.
-/

public section

namespace GroupExtension.CompatibleLifts

variable {N E G A : Type*} [Group N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)

/-- Transport a section by a compatible lift with acting-group coordinate one. -/
def kernelSection (x : (projection S ρ).ker) (σ : S.Section) : S.Section :=
  σ.monoidHomComp (toCoverAut S ρ x.val).toMonoidHom (by
    ext e
    change S.rightHom (toCoverAut S ρ x.val e) = S.rightHom e
    rw [rightHom_toCoverAut, MonoidHom.mem_ker.mp x.property, map_one, MulAut.one_apply])

@[simp]
theorem kernelSection_apply (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    kernelSection S ρ x σ g = toCoverAut S ρ x.val (σ g) := by
  simp only [kernelSection, Section.monoidHomComp_apply, MulEquiv.coe_toMonoidHom]

end GroupExtension.CompatibleLifts

namespace GroupExtension.CompatibleLifts

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : ∀ n e, Commute (S.inl n) e)

/-- The native section difference of a kernel lift is its quotient character. -/
theorem sectionDiff_kernelSection (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    TauCeti.GroupExtension.sectionDiff (kernelSection S ρ x σ) σ g =
      kernelCharacter S ρ hcentral x g := by
  apply S.inl_injective
  rw [TauCeti.GroupExtension.inl_sectionDiff, kernelSection_apply,
    inl_kernelCharacter_section]

end GroupExtension.CompatibleLifts
