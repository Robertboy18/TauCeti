/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `IsCyclic.monoidHom_equiv_self` identifies the character group of a finite cyclic group with
-- the group itself.
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
-- `IsCyclic.card_pow_eq_one_le` bounds the solutions of `x ^ n = 1` in a cyclic group.
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The character group of a finite cyclic group

Let `G` be a finite cyclic group and `M` a commutative monoid with enough roots of unity of order
`|G|`, so that Mathlib's `IsCyclic.monoidHom_equiv_self` identifies the character group
`G →* Mˣ` with `G`. This file records two consequences: the character group is itself cyclic,
and, for `n > 1`, at most `n - 1` characters are fixed by precomposition with the `n`-th power
map `g ↦ g ^ n`, since such a character `χ` satisfies `χ ^ (n - 1) = 1`.

The second statement is what bounds the number of characters of `𝔽_{q²}ˣ` fixed by the Frobenius
`u ↦ u ^ q`, which parametrise the reducible part of the cuspidal series of `GL₂(𝔽_q)`.

## Main results

* `IsCyclic.monoidHom`: the character group of a finite cyclic group is cyclic.
* `IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le`: for `n > 1`, at most `n - 1` characters
  are fixed by precomposition with the `n`-th power map.
-/

public section

namespace IsCyclic

variable (G M : Type*) [CommGroup G] [Finite G] [IsCyclic G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Nat.card G)]

/-- **The character group of a finite cyclic group is cyclic**, being isomorphic to the group
itself when the coefficient monoid has enough roots of unity. -/
theorem monoidHom : IsCyclic (G →* Mˣ) :=
  let e := (IsCyclic.monoidHom_equiv_self G M).some
  isCyclic_of_surjective e.symm e.symm.surjective

/-- **At most `n - 1` characters of a finite cyclic group are fixed by the `n`-th power map**
(`n > 1`): a character `χ` with `χ (g ^ n) = χ g` for all `g` satisfies `χ ^ (n - 1) = 1`, and a
cyclic group has at most `n - 1` solutions of that equation. -/
theorem natCard_monoidHom_comp_powMonoidHom_eq_le {n : ℕ} (hn : 1 < n) :
    Nat.card {χ : G →* Mˣ // χ.comp (powMonoidHom n) = χ} ≤ n - 1 := by
  classical
  have := IsCyclic.monoidHom G M
  have : Finite (G →* Mˣ) := Finite.of_equiv G (IsCyclic.monoidHom_equiv_self G M).some.symm
  let := Fintype.ofFinite (G →* Mˣ)
  have hfix : ∀ χ : G →* Mˣ, χ.comp (powMonoidHom n) = χ ↔ χ ^ (n - 1) = 1 := by
    intro χ
    have hpow : χ.comp (powMonoidHom n) = χ ^ (n - 1) * χ := by
      refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.mul_apply, MonoidHom.pow_apply, ← pow_succ, Nat.sub_add_cancel hn.le,
        MonoidHom.comp_apply, powMonoidHom_apply, map_pow]
    rw [hpow]
    exact ⟨fun h => mul_right_cancel (h.trans (one_mul χ).symm), fun h => by rw [h, one_mul]⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le (Nat.sub_pos_of_lt hn)

end IsCyclic
