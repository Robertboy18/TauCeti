/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The carry from `ℤ/4` to `𝔽₂`, and the doubling map from `𝔽₂` to `ℤ/4`

A residue `x` modulo four has canonical representative `x.val ∈ {0, 1, 2, 3}`, whose binary digits
are `x mod 2` and the carry `⌊x.val / 2⌋`. Reducing the carry modulo two gives the function
`ZMod.carryFour : ℤ/4 → 𝔽₂`. Its failure to be additive is measured by the product of the
residues modulo two: `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`. This is the identity behind
the vanishing of the cup square of a class of `H¹(G, 𝔽₂)` that lifts to a character to `ℤ/4`.

In the other direction, doubling `x ↦ 2x` embeds `𝔽₂` into `ℤ/4` as the subgroup `2ℤ/4ℤ`, which is
the kernel of reduction modulo two (`ZMod.twoMulCastAddHom`). It is the inclusion of the kernel in
the extension `0 → 𝔽₂ → ℤ/4 → 𝔽₂ → 0`.

## Main results

* `ZMod.carryFour`: the carry `⌊x.val / 2⌋ : ℤ/4 → 𝔽₂`.
* `ZMod.carryFour_add`: **the carry identity** `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)`.
* `ZMod.carryFour_zero`: the carry of `0` is `0`.
* `ZMod.twoMulCastAddHom`: the doubling map `𝔽₂ →+ ℤ/4`, `x ↦ 2x`; it is injective
  (`ZMod.twoMulCastAddHom_injective`) and its range is the kernel of reduction modulo two
  (`ZMod.range_twoMulCastAddHom`).
-/

public section

namespace ZMod

/-- The carry `⌊x.val / 2⌋ : ℤ/4 → 𝔽₂`: the binary digit of weight two of the canonical
representative of a residue modulo four. -/
def carryFour (x : ZMod 4) : ZMod 2 := ((x.val / 2 : ℕ) : ZMod 2)

/-- The carry of `0` is `0`. -/
@[simp]
theorem carryFour_zero : carryFour 0 = 0 := by
  decide

/-- **The carry identity in `ℤ/4`**: `⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)` in `𝔽₂`. -/
@[simp]
theorem carryFour_add (u v : ZMod 4) :
    carryFour (u + v) =
      carryFour u + carryFour v +
        castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) u *
          castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) v := by
  revert u v
  decide

/-- **The doubling map `𝔽₂ →+ ℤ/4`**, `x ↦ 2x`: the inclusion of `𝔽₂` as the subgroup `2ℤ/4ℤ`. -/
def twoMulCastAddHom : ZMod 2 →+ ZMod 4 where
  toFun x := 2 * x.cast
  map_zero' := by decide
  map_add' := by decide

@[simp]
theorem twoMulCastAddHom_apply (x : ZMod 2) : twoMulCastAddHom x = 2 * x.cast :=
  (rfl)

/-- The doubling map `𝔽₂ →+ ℤ/4` is injective. -/
theorem twoMulCastAddHom_injective : Function.Injective twoMulCastAddHom := by
  intro x y h
  rw [twoMulCastAddHom_apply, twoMulCastAddHom_apply] at h
  revert x y h
  decide

/-- **The range of the doubling map is the kernel of reduction modulo two**: the sequence
`0 → 𝔽₂ → ℤ/4 → 𝔽₂ → 0` is exact in the middle. -/
theorem range_twoMulCastAddHom :
    twoMulCastAddHom.range = (castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom.ker := by
  ext y
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  simp only [twoMulCastAddHom_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  revert y
  decide

end ZMod
