/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.GroupTheory.Perm.AlternatingCharacter
public import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The linear characters of the symmetric group on three points

`Equiv.Perm (Fin 3)` is the symmetric group `S₃`, the smallest non-commutative group, and this
file records what that does to its linear characters, the homomorphisms `S₃ →* Mˣ` into the units
of a commutative monoid `M`. The commutator subgroup of `S₃` is the alternating subgroup `A₃`, so
the abelianization has order two and exponent two, every linear character kills the three-cycle,
and once `M` has a primitive square root of unity there are exactly two linear characters: the
trivial character and the sign.

The consequence the file exists for is that **column orthogonality fails on `S₃`**. For a finite
commutative group `G`, `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` says that the tagged sum
`∑ χ, (χ σ)⁻¹ * χ g` over the characters is `#G` when `g = σ` and `0` otherwise; it is what turns
the indicator of one Frobenius fibre into a sum over characters in the cyclotomic case of the
Chebotarev density theorem. On `S₃`, at the tag `σ = 1` and `g` the three-cycle, the sum is `2`
and not `0`: the linear characters of a non-commutative group do not separate its elements, and
the orthogonality formula cannot be applied to a Galois group that is not abelian. The general form
of the failure is `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`; this file exhibits it on the
smallest example, with the offending value computed.

## Main results

* `TauCeti.commutator_perm_fin_three`: the commutator subgroup of `S₃` is `A₃`.
* `TauCeti.card_abelianization_perm_fin_three` and
  `TauCeti.exponent_abelianization_perm_fin_three`: the abelianization of `S₃` has order two and
  exponent two.
* `TauCeti.monoidHom_apply_finRotate_three`: every linear character of `S₃` kills the three-cycle.
* `TauCeti.card_monoidHom_perm_fin_three`: **`S₃` has exactly two linear characters** valued in a
  commutative monoid with a primitive square root of unity.
* `TauCeti.sum_monoidHom_apply_finRotate_three`: the character sum of `S₃` at the three-cycle is
  `2`.
* `TauCeti.sum_inv_mul_monoidHom_apply_finRotate_three_ne_ite`: **column orthogonality fails on
  `S₃`** at the tag `1` and the three-cycle.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 2, where the
  linear characters of `G` are identified with the characters of `G / G'`.
-/

public section

open Equiv
open scoped commutatorElement

namespace TauCeti

/-- The three-cycle of `Fin 3` is the commutator of the transposition `(0 1)` with the rotation
`finRotate 3`: a transposition inverts the rotation, so `t c t⁻¹ c⁻¹ = c⁻¹ * c⁻¹ = c`. -/
private theorem commutatorElement_swap_finRotate_three :
    ⁅swap (0 : Fin 3) 1, finRotate 3⁆ = finRotate 3 := by
  decide

/-- **The commutator subgroup of `S₃` is `A₃`.** The commutator subgroup of any permutation group
lies in the alternating subgroup, and on three points the alternating subgroup consists of the
identity and the two rotations, each of which is a commutator. -/
theorem commutator_perm_fin_three : commutator (Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  refine le_antisymm alternatingGroup.commutator_perm_le fun g hg ↦ ?_
  have hrot : finRotate 3 ∈ commutator (Perm (Fin 3)) :=
    commutatorElement_swap_finRotate_three ▸
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  -- the even permutations of three points are the identity and the two rotations
  have key : ∀ g : Perm (Fin 3), Perm.sign g = 1 →
      g = 1 ∨ g = finRotate 3 ∨ g = (finRotate 3)⁻¹ := by
    decide
  rcases key g (Perm.mem_alternatingGroup.mp hg) with rfl | rfl | rfl
  · exact one_mem _
  · exact hrot
  · exact inv_mem hrot

/-- **The abelianization of `S₃` has order two.** The commutator subgroup is `A₃`, of order `3`
inside a group of order `6`. -/
theorem card_abelianization_perm_fin_three : Nat.card (Abelianization (Perm (Fin 3))) = 2 := by
  have hcomm : Nat.card (commutator (Perm (Fin 3))) = 3 := by
    rw [commutator_perm_fin_three, card_alternatingGroup_fin_three]
  have hsix : Nat.card (Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hsplit : Nat.card (Perm (Fin 3)) =
      Nat.card (Abelianization (Perm (Fin 3))) * Nat.card (commutator (Perm (Fin 3))) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hsix, hcomm] at hsplit
  omega

/-- **The abelianization of `S₃` has exponent two**: it is a group of prime order two. -/
theorem exponent_abelianization_perm_fin_three :
    Monoid.exponent (Abelianization (Perm (Fin 3))) = 2 := by
  have : IsCyclic (Abelianization (Perm (Fin 3))) :=
    isCyclic_of_prime_card card_abelianization_perm_fin_three
  rw [IsCyclic.exponent_eq_card, card_abelianization_perm_fin_three]

section CommMonoid

variable {M : Type*} [CommMonoid M]

/-- **Every linear character of `S₃` kills the three-cycle.** The three-cycle is even, and every
homomorphism from a permutation group to a commutative monoid is trivial on the alternating
subgroup (`MonoidHom.alternatingGroup_le_ker`). -/
@[simp]
theorem monoidHom_apply_finRotate_three (χ : Perm (Fin 3) →* M) : χ (finRotate 3) = 1 :=
  MonoidHom.mem_ker.mp <| χ.alternatingGroup_le_ker <| Perm.mem_alternatingGroup.mpr (by decide)

variable (M) [HasEnoughRootsOfUnity M 2]

/-- **`S₃` has exactly two linear characters** valued in a commutative monoid with a primitive
square root of unity: the trivial character and the sign. Every linear character factors through
the abelianization, which has order two by `TauCeti.card_abelianization_perm_fin_three`, and a
finite commutative group with enough roots of unity in `M` has as many characters as elements. -/
theorem card_monoidHom_perm_fin_three : Nat.card (Perm (Fin 3) →* Mˣ) = 2 := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (Perm (Fin 3)))) := by
    rw [exponent_abelianization_perm_fin_three]
    infer_instance
  rw [card_monoidHom_eq_card_abelianization, card_abelianization_perm_fin_three]

end CommMonoid

section Domain

variable (M : Type*) [CommRing M] [IsDomain M] [HasEnoughRootsOfUnity M 2]

/-- **The character sum of `S₃` at the three-cycle is `2`**: the number of linear characters, each
of which takes the value `1` there. -/
theorem sum_monoidHom_apply_finRotate_three :
    ∑ χ : Perm (Fin 3) →* Mˣ, (χ (finRotate 3) : M) = 2 := by
  simp only [monoidHom_apply_finRotate_three, Units.val_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card, card_monoidHom_perm_fin_three,
    Nat.cast_ofNat]

/-- **Column orthogonality fails on `S₃`.** At the tag `σ = 1` and the three-cycle `g`, the sum
`∑ χ, (χ σ)⁻¹ * χ g` over the linear characters of `S₃` is `2`, whereas the identity
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` for finite commutative groups would return `0`,
since `g ≠ σ`. The linear characters of `S₃` do not separate its elements, so the orthogonality
formula does not extend to a Galois group that is not abelian. -/
theorem sum_inv_mul_monoidHom_apply_finRotate_three_ne_ite :
    ∑ χ : Perm (Fin 3) →* Mˣ, (((χ 1)⁻¹ : Mˣ) : M) * ((χ (finRotate 3) : Mˣ) : M) ≠
      if finRotate 3 = (1 : Perm (Fin 3)) then (Nat.card (Perm (Fin 3)) : M) else 0 := by
  -- a domain with a primitive square root of unity does not have characteristic two
  have h2 : (2 : M) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot M 2
    exact_mod_cast hζ.neZero'.out
  rw [ite_eq_right (by decide)]
  simpa only [map_one, inv_one, Units.val_one, one_mul, sum_monoidHom_apply_finRotate_three]
    using h2

end Domain

end TauCeti
