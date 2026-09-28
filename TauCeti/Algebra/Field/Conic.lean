/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Points on the conics `a² + δ b² = 1`

Over a field `K` the conic `a² + δ b² = 1` always has the points `(±1, 0)`. This file shows that
in characteristic zero it also has a point with both coordinates nonzero, for every `δ`. The
rational parametrisation `t ↦ ((1 - δ t²) / (1 + δ t²), 2t / (1 + δ t²))` at `t = 1` gives such a
point unless `δ = ±1`, and the circle `a² + b² = 1` and the hyperbola `a² - b² = 1` carry the points
`(3/5, 4/5)` and `(5/4, 3/4)`.

The statement is what makes a binary form `⟨1, δ⟩` represent `1` with both coordinates nonzero; it
supplies the even unitary units `a + b • ω` outside the Lipschitz group in
`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six.lean`.

## Main results

* `TauCeti.exists_sq_add_sq_mul_eq_one`: the conic `a² + b² δ = 1` has a point with both
  coordinates nonzero over every field of characteristic zero.
-/

public section

namespace TauCeti

/-- **The conic `a² + b² δ = 1` has a point with both coordinates nonzero over every field of
characteristic zero.** -/
theorem exists_sq_add_sq_mul_eq_one {K : Type*} [Field K] [CharZero K] (δ : K) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 2 + b ^ 2 * δ = 1 := by
  -- The rational parametrisation `t ↦ ((1 - δt²)/(1 + δt²), 2t/(1 + δt²))` at `t = 1` works
  -- unless `δ = ±1`; those two conics carry the points `(3/5, 4/5)` and `(5/4, 3/4)`.
  by_cases h₁ : δ = 1
  · exact ⟨3 / 5, 4 / 5, by norm_num, by norm_num, by rw [h₁]; norm_num⟩
  by_cases h₂ : δ = -1
  · exact ⟨5 / 4, 3 / 4, by norm_num, by norm_num, by rw [h₂]; norm_num⟩
  have h₁' : 1 + δ ≠ 0 := fun h => h₂ (by linear_combination h)
  have h₂' : 1 - δ ≠ 0 := fun h => h₁ (by linear_combination -h)
  refine ⟨(1 - δ) / (1 + δ), 2 / (1 + δ), div_ne_zero h₂' h₁', div_ne_zero two_ne_zero h₁', ?_⟩
  field_simp
  ring

end TauCeti
