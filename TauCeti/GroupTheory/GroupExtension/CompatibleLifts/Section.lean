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

namespace TauCeti.CompatibleLifts

open _root_.GroupExtension

variable {N E G A : Type*} [Group N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)

/-- Transport a section by a compatible lift with acting-group coordinate one. -/
def kernelSection (x : (projection S ρ).ker) (σ : S.Section) : S.Section :=
  σ.monoidHomComp (toMulAut S ρ x.val).toMonoidHom (by
    ext e
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [rightHom_toMulAut, MonoidHom.mem_ker.mp x.property, map_one, MulAut.one_apply])

@[simp]
theorem kernelSection_apply (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    kernelSection S ρ x σ g = toMulAut S ρ x.val (σ g) := by
  simp only [kernelSection, Section.monoidHomComp_apply, MulEquiv.coe_toMonoidHom]

end TauCeti.CompatibleLifts

namespace TauCeti.CompatibleLifts

open _root_.GroupExtension

variable {N E G A : Type*} [CommGroup N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)
  (hcentral : S.inl.range ≤ Subgroup.center E)

/-- The native section difference of a kernel lift is its quotient character. -/
theorem sectionDiff_kernelSection (x : (projection S ρ).ker) (σ : S.Section) (g : G) :
    TauCeti.GroupExtension.sectionDiff (kernelSection S ρ x σ) σ g =
      kernelCharacter S ρ hcentral x g := by
  apply S.inl_injective
  rw [TauCeti.GroupExtension.inl_sectionDiff, kernelSection_apply,
    inl_kernelCharacter_section]

end TauCeti.CompatibleLifts
