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

/-- **The doubling map `𝔽₂ →+ ℤ/4`**, `x ↦ 2x`: the inclusion of `𝔽₂` as the subgroup `2ℤ/4ℤ`. It
is the homomorphism `ZMod.lift` induces from the doubling `ℤ →+ ℤ/4`, which kills `2`. -/
def twoMulCastAddHom : ZMod 2 →+ ZMod 4 :=
  lift 2 ⟨2 • Int.castAddHom (ZMod 4), by decide⟩

@[simp]
theorem twoMulCastAddHom_apply (x : ZMod 2) : twoMulCastAddHom x = 2 * x.cast := by
  nth_rw 1 [← intCast_zmod_cast x]
  rw [twoMulCastAddHom, lift_coe]
  simp only [AddMonoidHom.nsmul_apply, Int.coe_castAddHom, intCast_cast, nsmul_eq_mul,
    Nat.cast_ofNat]

/-- The doubling map `𝔽₂ →+ ℤ/4` is injective: if `4 ∣ 2m` then `2 ∣ m`. -/
theorem twoMulCastAddHom_injective : Function.Injective twoMulCastAddHom :=
  (lift_injective 2).2 fun m hm => by
    have h4 : ((2 * m : ℤ) : ZMod 4) = 0 := by
      simpa only [AddMonoidHom.nsmul_apply, Int.coe_castAddHom, nsmul_eq_mul, Nat.cast_ofNat,
        Int.cast_mul, Int.cast_ofNat] using hm
    rw [intCast_zmod_eq_zero_iff_dvd] at h4 ⊢
    omega

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
