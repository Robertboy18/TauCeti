/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Splitting a sum over all subsets of a finite type

A sum over all finite subsets of a finite type with at least two elements splits into four parts:
the empty set, the singletons, the subsets with at least two elements other than the whole type,
and the whole type. This is the bookkeeping behind expansions of the form
`∏_{i} (1 + x_i) = ∑_{S} ∏_{i ∈ S} x_i`, where the four parts are the constant term, the linear
terms, the mixed terms, and the top-degree term.

## Main results

* `TauCeti.sum_finset_eq_add_sum_singleton_add_sum_filter_add`: the four-part splitting.
-/

public section

namespace TauCeti

open Finset

/-- **A sum over the subsets of a finite type with at least two elements splits into four parts**:
the empty set, the singletons, the subsets with at least two elements other than `univ`, and
`univ`. -/
theorem sum_finset_eq_add_sum_singleton_add_sum_filter_add {α M : Type*} [Fintype α]
    [DecidableEq α] [AddCommMonoid M] (hα : 1 < Fintype.card α) (f : Finset α → M) :
    ∑ S : Finset α, f S = f ∅ + ∑ a : α, f {a} +
      ∑ S ∈ univ.filter (fun S : Finset α ↦ 1 < S.card ∧ S ≠ univ), f S + f univ := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  rw [← add_sum_erase _ _ (mem_univ (∅ : Finset α)),
    ← add_sum_erase (univ.erase ∅) _ (mem_erase.2 ⟨univ_nonempty.ne_empty, mem_univ _⟩),
    ← sum_filter_add_sum_filter_not ((univ.erase ∅).erase univ) fun S ↦ S.card = 1]
  -- The subsets of cardinality one are the singletons.
  have hsing : ((univ.erase ∅).erase univ).filter (fun S : Finset α ↦ S.card = 1) =
      univ.image fun a : α ↦ ({a} : Finset α) := by
    ext S
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_image, true_and, card_eq_one]
    constructor
    · rintro ⟨-, a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨⟨fun h ↦ ?_, singleton_ne_empty a⟩, a, rfl⟩
      have hcard := congrArg Finset.card h
      rw [card_singleton, card_univ] at hcard
      omega
  -- The remaining nonempty proper subsets are those with at least two elements.
  have hbig : ((univ.erase ∅).erase univ).filter (fun S : Finset α ↦ ¬ S.card = 1) =
      univ.filter fun S : Finset α ↦ 1 < S.card ∧ S ≠ univ := by
    ext S
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ← nonempty_iff_ne_empty,
      ← card_pos]
    constructor
    · rintro ⟨⟨hu, hpos⟩, h1⟩
      exact ⟨by omega, hu⟩
    · rintro ⟨h1, hu⟩
      exact ⟨⟨hu, by omega⟩, by omega⟩
  rw [hsing, hbig, sum_image fun _ _ _ _ h ↦ singleton_inj.1 h]
  ac_rfl

end TauCeti
