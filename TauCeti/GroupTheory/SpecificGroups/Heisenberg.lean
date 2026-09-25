/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.PGroup
public import TauCeti.GroupTheory.PLowerCentralSeries

/-!
# The Heisenberg group over a commutative ring

The **Heisenberg group** `HeisenbergGroup R` over a commutative ring `R` is the group of unipotent
upper triangular `3 × 3` matrices over `R`, written in the coordinates `(x, y, z)` of the strictly
upper triangle, so that

  `(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')`.

It is nilpotent of class two: every commutator lies on the `z`-axis, which is central, and the
commutator of `(x, y, z)` and `(x', y', z')` is `(0, 0, x * y' - x' * y)`. Over a ring of
characteristic `p` the `p`-th power of every element lies on the `z`-axis as well, so the second
term of the lower `p`-central series is trivial; over `𝔽_p` the group has order `p ^ 3`. This is
the smallest nonabelian `p`-group of `p`-class two, and it detects brackets in the degree-one
graded piece of the lower `p`-series of a free pro-`p` group.

## Main definitions

* `TauCeti.HeisenbergGroup`: the Heisenberg group over a commutative ring, with its group
  structure.
* `TauCeti.HeisenbergGroup.zAxis`: the central subgroup of elements `(0, 0, z)`.

## Main results

* `TauCeti.HeisenbergGroup.commutatorElement_eq`: the commutator formula.
* `TauCeti.HeisenbergGroup.pow_eq`: the power formula
  `(x, y, z) ^ n = (n • x, n • y, n • z + (n choose 2) • (x * y))`.
* `TauCeti.HeisenbergGroup.pLowerCentralSeries_top_two_eq_bot`: over a ring of characteristic
  `p`, the second term of the lower `p`-central series is trivial.
* `TauCeti.HeisenbergGroup.isPGroup_zmod`: over `ZMod p` the Heisenberg group is a `p`-group.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

/-- The **Heisenberg group** over a commutative ring `R`: triples `(x, y, z)` with the
multiplication `(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')`, the group of
unipotent upper triangular `3 × 3` matrices in the coordinates of the strictly upper triangle. -/
@[ext]
structure HeisenbergGroup (R : Type*) where
  /-- The `(1, 2)` matrix entry. -/
  x : R
  /-- The `(2, 3)` matrix entry. -/
  y : R
  /-- The `(1, 3)` matrix entry. -/
  z : R

namespace HeisenbergGroup

variable {R : Type*}

/-- The Heisenberg group is the product `R × R × R` as a type. -/
def equivProd : HeisenbergGroup R ≃ R × R × R where
  toFun a := (a.x, a.y, a.z)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

instance [Fintype R] : Fintype (HeisenbergGroup R) := Fintype.ofEquiv _ equivProd.symm

instance [Finite R] : Finite (HeisenbergGroup R) := Finite.of_equiv _ equivProd.symm

theorem card_eq : Nat.card (HeisenbergGroup R) = Nat.card R ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

variable [CommRing R]

instance : Mul (HeisenbergGroup R) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩
instance : One (HeisenbergGroup R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (HeisenbergGroup R) := ⟨fun a => ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

@[simp] theorem mul_x (a b : HeisenbergGroup R) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : HeisenbergGroup R) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_z (a b : HeisenbergGroup R) : (a * b).z = a.z + b.z + a.x * b.y := rfl
@[simp] theorem one_x : (1 : HeisenbergGroup R).x = 0 := rfl
@[simp] theorem one_y : (1 : HeisenbergGroup R).y = 0 := rfl
@[simp] theorem one_z : (1 : HeisenbergGroup R).z = 0 := rfl
@[simp] theorem inv_x (a : HeisenbergGroup R) : a⁻¹.x = -a.x := rfl
@[simp] theorem inv_y (a : HeisenbergGroup R) : a⁻¹.y = -a.y := rfl
@[simp] theorem inv_z (a : HeisenbergGroup R) : a⁻¹.z = -a.z + a.x * a.y := rfl

instance : Group (HeisenbergGroup R) where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

/-- **The commutator formula**: `⁅(x, y, z), (x', y', z')⁆ = (0, 0, x * y' - x' * y)`. -/
theorem commutatorElement_eq (a b : HeisenbergGroup R) :
    ⁅a, b⁆ = ⟨0, 0, a.x * b.y - b.x * a.y⟩ := by
  ext <;> simp [commutatorElement_def]
  ring

/-- **The power formula**: `(x, y, z) ^ n = (n • x, n • y, n • z + (n choose 2) • (x * y))`. -/
theorem pow_eq (a : HeisenbergGroup R) (n : ℕ) :
    a ^ n = ⟨n • a.x, n • a.y, n • a.z + n.choose 2 • (a.x * a.y)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    ext <;> simp [add_smul]
    ring

/-- The **`z`-axis** `{(0, 0, z)}`, a central subgroup. -/
def zAxis : Subgroup (HeisenbergGroup R) where
  carrier := {a | a.x = 0 ∧ a.y = 0}
  mul_mem' := by
    rintro a b ⟨hax, hay⟩ ⟨hbx, hby⟩
    simp [hax, hay, hbx, hby]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨hax, hay⟩
    simp [hax, hay]

@[simp]
theorem mem_zAxis_iff {a : HeisenbergGroup R} : a ∈ zAxis ↔ a.x = 0 ∧ a.y = 0 := Iff.rfl

/-- The `z`-axis is central. -/
theorem zAxis_le_center : zAxis ≤ center (HeisenbergGroup R) := by
  rintro a ⟨hax, hay⟩
  rw [Subgroup.mem_center_iff]
  intro b
  ext <;> simp [hax, hay, add_comm]

/-- Every commutator lies on the `z`-axis: the Heisenberg group is nilpotent of class two. -/
theorem commutatorElement_mem_zAxis (a b : HeisenbergGroup R) : ⁅a, b⁆ ∈ zAxis := by
  rw [commutatorElement_eq]
  exact ⟨rfl, rfl⟩

/-- The commutator of an element of the `z`-axis with any element is trivial. -/
theorem commutatorElement_eq_one_of_mem_zAxis {a : HeisenbergGroup R} (ha : a ∈ zAxis)
    (b : HeisenbergGroup R) : ⁅a, b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp (zAxis_le_center ha) b).symm)

section CharP

variable (p : ℕ) [CharP R p]

/-- In characteristic `p`, the `p`-th power of every element lies on the `z`-axis. -/
theorem pow_char_mem_zAxis (a : HeisenbergGroup R) : a ^ p ∈ zAxis := by
  rw [pow_eq, mem_zAxis_iff]
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

/-- In characteristic `p`, the `p`-th power of an element of the `z`-axis is trivial. -/
theorem pow_char_eq_one_of_mem_zAxis {a : HeisenbergGroup R} (ha : a ∈ zAxis) : a ^ p = 1 := by
  obtain ⟨hax, hay⟩ := mem_zAxis_iff.mp ha
  rw [pow_eq]
  ext <;> simp [hax, hay, nsmul_eq_mul, CharP.cast_eq_zero]

/-- In characteristic `p`, the first term of the lower `p`-central series lies on the `z`-axis. -/
theorem pLowerCentralSeries_top_one_le_zAxis :
    (⊤ : Subgroup (HeisenbergGroup R)).pLowerCentralSeries p 1 ≤ zAxis :=
  Subgroup.pLowerCentralSeries_succ_le_iff.mpr
    ⟨fun a _ => pow_char_mem_zAxis p a, fun a _ b _ => commutatorElement_mem_zAxis a b⟩

/-- **The Heisenberg group has `p`-class two** in characteristic `p`: the second term of its
lower `p`-central series is trivial. -/
theorem pLowerCentralSeries_top_two_eq_bot :
    (⊤ : Subgroup (HeisenbergGroup R)).pLowerCentralSeries p 2 = ⊥ := by
  refine le_bot_iff.mp (Subgroup.pLowerCentralSeries_succ_le_iff.mpr ⟨fun a ha => ?_, ?_⟩)
  · rw [mem_bot]
    exact pow_char_eq_one_of_mem_zAxis p (pLowerCentralSeries_top_one_le_zAxis p ha)
  · intro a ha b _
    rw [mem_bot]
    exact commutatorElement_eq_one_of_mem_zAxis (pLowerCentralSeries_top_one_le_zAxis p ha) b

end CharP

/-- The Heisenberg group over `ZMod p` is a `p`-group, of order `p ^ 3`. -/
theorem isPGroup_zmod (p : ℕ) [Fact p.Prime] : IsPGroup p (HeisenbergGroup (ZMod p)) :=
  IsPGroup.of_card (n := 3) (by rw [card_eq, Nat.card_zmod])

end HeisenbergGroup

end TauCeti
