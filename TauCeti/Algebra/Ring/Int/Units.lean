/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Order.Units

/-!
# Equality of signs

The group `ℤˣ = {±1}` has exponent two, so two signs are equal exactly when their product is `1`.
This is the form in which an equality of two products of Hilbert symbols is checked, by expanding
both sides into one common product of symbols.

## Main results

* `Int.units_eq_iff_mul_eq_one`: `u = v ↔ u * v = 1` for signs `u v : ℤˣ`.
-/

public section

namespace TauCeti

/-- Two signs are equal exactly when their product is `1`. -/
theorem _root_.Int.units_eq_iff_mul_eq_one (u v : ℤˣ) : u = v ↔ u * v = 1 := by
  rw [mul_eq_one_iff_eq_inv, Int.units_inv_eq_self]

end TauCeti
