/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The finite cyclic subgroup used by the M11 coset certificate. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open Relations

/-- Both concrete subgroup words represent powers of `x` in the exact group. -/
theorem subgroup_words_mem : ∀ w ∈ ([[0, 3], [1, 2]] : List (List (Fin 4))),
    (w.map letterValue).prod ∈ Subgroup.zpowers x := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [prod_letterValue, eval_abinv]
    exact Subgroup.mem_zpowers x
  · rw [prod_letterValue, eval_bainv]
    exact (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)

/-- The cyclic subgroup is finite, independently of any finite-image computation. -/
theorem finite_zpowers_x : Finite (Subgroup.zpowers x) :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨8, by decide, x_pow_eight⟩).finite_zpowers

/-- The order of the cyclic subgroup is at most eight. -/
theorem card_zpowers_x_le : Nat.card (Subgroup.zpowers x) ≤ 8 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) x_pow_eight

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
