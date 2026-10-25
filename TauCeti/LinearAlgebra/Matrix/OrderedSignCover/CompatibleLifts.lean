/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.CompatibleLifts.Character
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover

/-!
# Character twists of the ordered sign cover

The character-kernel construction for a central extension applies to the existing ordered sign
cover of any integer matrix. A character twist preserves the lattice coordinate and multiplies
the sign coordinate by the character value. No symmetry, parity, or ADE hypothesis is needed.
-/

public section

namespace Matrix.SignCover

open TauCeti GroupExtension.CompatibleLifts

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)

attribute [local instance] trivialMulDistribMulAction

/-- The included signs commute with every element of the ordered sign cover. -/
theorem inl_commute (n : ℤˣ) (x : SignCover B) :
    Commute ((signFactorSet B).groupExtension.inl n) x := by
  rw [FactorSet.groupExtension_inl]
  exact (Subgroup.mem_center_iff.mp
    (FactorSet.inl_range_le_center _ trivialMulDistribMulAction_smul ⟨n, rfl⟩) x).symm

/-- The twist of the existing sign cover by a character of its lattice. -/
noncomputable def characterTwist (χ : Multiplicative (I → ℤ) →* ℤˣ) :
    MulAut (SignCover B) :=
  twist (signFactorSet B).groupExtension (inl_commute B) χ

@[simp]
theorem characterTwist_right (χ : Multiplicative (I → ℤ) →* ℤˣ) (x : SignCover B) :
    (characterTwist B χ x).right = x.right := by
  simp [characterTwist, twist_apply]

@[simp]
theorem characterTwist_left (χ : Multiplicative (I → ℤ) →* ℤˣ) (x : SignCover B) :
    (characterTwist B χ x).left = χ x.right * x.left := by
  simp [characterTwist, twist_apply]

end Matrix.SignCover
