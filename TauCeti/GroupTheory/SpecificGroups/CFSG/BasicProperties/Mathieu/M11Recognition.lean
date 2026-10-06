/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.LowerBound
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11Finiteness

/-! Order 7920 and faithful permutation recognition of the M11 presentation. -/

public section

namespace TauCeti.Sporadic.Mathieu

/-- The exact presentation has 7920 elements. -/
theorem card_m11Presentation : Nat.card m11Presentation.Group = 7920 := by
  have := finite_m11Presentation
  exact le_antisymm card_m11Presentation_le m11_natCard_ge

/-- The presentation map is bijective onto its concrete permutation image. -/
theorem m11PermutationHom_rangeRestrict_bijective :
    Function.Bijective m11PermutationHom.rangeRestrict := by
  have := finite_m11Presentation
  exact m11PermutationHom.rangeRestrict_surjective.bijective_of_nat_card_le
    (card_m11Presentation_le.trans m11PermutationHom_range_natCard_ge)

/-- The recorded permutation representation of the exact presentation is faithful. -/
theorem m11PermutationHom_injective : Function.Injective m11PermutationHom := by
  intro x y h
  apply m11PermutationHom_rangeRestrict_bijective.injective
  exact Subtype.ext h

/-- The exact presentation is isomorphic to its concrete permutation image. -/
@[expose]
noncomputable def m11MulEquivRange :
    m11Presentation.Group ≃* m11PermutationHom.range :=
  MulEquiv.ofBijective m11PermutationHom.rangeRestrict
    m11PermutationHom_rangeRestrict_bijective

/-- Recognition preserves the specified permutation map. -/
@[simp]
theorem coe_m11MulEquivRange_apply (x : m11Presentation.Group) :
    (m11MulEquivRange x : Equiv.Perm (Fin 11)) = m11PermutationHom x := rfl

/-- The permutation image has order 7920. -/
theorem card_m11PermutationHom_range : Nat.card m11PermutationHom.range = 7920 :=
  (Nat.card_congr m11MulEquivRange.toEquiv).symm.trans card_m11Presentation

/-- The permutation representation has trivial kernel. -/
theorem m11PermutationHom_ker_eq_bot : m11PermutationHom.ker = ⊥ :=
  m11PermutationHom.ker_eq_bot m11PermutationHom_injective

end TauCeti.Sporadic.Mathieu
