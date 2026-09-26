/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Length

/-!
# The exchange condition for the Weyl group of a Tits system

Let `(B, N)` be a Tits system with Weyl group `W`, simple reflections `S`, and length function `ℓ`.
This file proves that the pair `(W, S)` satisfies the **exchange condition**: if `s` is a simple
reflection, `w = s₁ ⋯ s_q` is a product of simple reflections, and `ℓ (s w) < ℓ w`, then

```text
s w = s₁ ⋯ ŝ_j ⋯ s_q
```

for some `j`, that is, `s w` is spelled by the same word with one letter deleted. No reducedness is
assumed of the word `s₁ ⋯ s_q`; when it is reduced, the shortened word is reduced as well, because
`ℓ (s w) + 1 = ℓ w` by `TauCeti.TitsSystem.wordLength_simple_mul`.

The proof is the one of Bourbaki. The key step is a rank-one statement about cells: if
`(B s B)(B w B) = B (s w) B` but `(B s B)(B w s' B)` is not the single cell `B (s w s') B`, then
`s w = w s'`. Indeed the cell `B (w s') B` then lies in `(B s B)(B w s' B) ⊆ (B s B)(B w B)(B s' B)
= (B (s w) B)(B s' B) ⊆ B (s w s') B ∪ B (s w) B`, so by the disjointness of distinct cells
`w s' = s w s'`, which is impossible as `s ≠ 1`, or `w s' = s w`. Peeling letters off the right of
the word `s₁ ⋯ s_q` and using that `(B s B)(B w B) = B (s w) B` holds exactly when `s` increases
the length of `w` gives the exchange condition.

## Main declarations

* `TauCeti.TitsSystem.simple_mul_eq_mul_simple_of_bruhatCell_mul_ne`: the rank-one exchange step
  on cells.
* `TauCeti.TitsSystem.exists_eraseIdx_prod_eq_of_bruhatCell_mul_ne`: the exchange condition
  phrased with cells, for any word whose product `w` has `(B s B)(B w B) ≠ B (s w) B`.
* `TauCeti.TitsSystem.exists_eraseIdx_prod_eq_of_wordLength_lt`: **the exchange condition** for
  the Weyl group of a Tits system.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, no. 5 and §2, no. 4,
  Theorem 2.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.3.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-- **The rank-one exchange step.** If `(B s B)(B w B)` is the single cell `B (s w) B` while
`(B s B)(B w s' B)` is not the single cell `B (s w s') B`, then `s w = w s'`. -/
theorem simple_mul_eq_mul_simple_of_bruhatCell_mul_ne {s s' w : T.WeylGroup} (hs : s ∈ T.simple)
    (hs' : s' ∈ T.simple) (hw : T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w))
    (hws' : T.bruhatCell s * T.bruhatCell (w * s') ≠ T.bruhatCell (s * (w * s'))) :
    s * w = w * s' := by
  have hunion := (T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs (w * s')).resolve_left hws'
  have hsub : T.bruhatCell (w * s') ⊆ T.bruhatCell (s * w * s') ∪ T.bruhatCell (s * w) := by
    calc T.bruhatCell (w * s') ⊆ T.bruhatCell s * T.bruhatCell (w * s') := by
          rw [hunion]
          exact Set.subset_union_right
      _ ⊆ T.bruhatCell s * (T.bruhatCell w * T.bruhatCell s') :=
          Set.mul_subset_mul_left (T.subset_bruhatCell_mul_of_mem_simple_right w hs')
      _ = T.bruhatCell (s * w) * T.bruhatCell s' := by rw [← mul_assoc, hw]
      _ ⊆ T.bruhatCell (s * w * s') ∪ T.bruhatCell (s * w) :=
          T.bruhatCell_mul_subset_union_of_mem_simple_right (s * w) hs'
  rcases T.eq_or_eq_of_bruhatCell_subset_union hsub with h | h
  · exact absurd (mul_right_cancel h) fun h' ↦ T.simple_ne_one hs (by simpa using h')
  · exact h.symm

/-- **The exchange condition, in terms of cells.** If `w` is the product of a list of simple
reflections and `(B s B)(B w B)` is not the single cell `B (s w) B`, then `s w` is the product of
the list with one letter deleted. -/
theorem exists_eraseIdx_prod_eq_of_bruhatCell_mul_ne {s : T.WeylGroup} (hs : s ∈ T.simple)
    {l : List T.WeylGroup} (hl : ∀ x ∈ l, x ∈ T.simple)
    (h : T.bruhatCell s * T.bruhatCell l.prod ≠ T.bruhatCell (s * l.prod)) :
    ∃ j < l.length, s * l.prod = (l.eraseIdx j).prod := by
  induction l using List.reverseRecOn with
  | nil =>
    exact absurd (by rw [List.prod_nil, mul_one, T.bruhatCell_one, T.bruhatCell_mul_subgroupB]) h
  | append_singleton l' s' ih =>
    rw [List.forall_mem_append, List.forall_mem_singleton] at hl
    obtain ⟨hl', hs'⟩ := hl
    rw [List.prod_append, List.prod_singleton] at h ⊢
    by_cases hP : T.bruhatCell s * T.bruhatCell l'.prod = T.bruhatCell (s * l'.prod)
    · -- The last letter is the one to delete.
      refine ⟨l'.length, by simp, ?_⟩
      rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_zero,
        List.tail_cons, List.append_nil, ← mul_assoc,
        T.simple_mul_eq_mul_simple_of_bruhatCell_mul_ne hs hs' hP h, T.mul_simple_mul_simple _ hs']
    · -- The letter to delete lies in the shorter word.
      obtain ⟨j, hj, hprod⟩ := ih hl' hP
      refine ⟨j, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [List.eraseIdx_append_of_lt_length hj, List.prod_append, List.prod_singleton, ← hprod,
        mul_assoc]

/-- **The exchange condition.** If `w` is the product of a list of simple reflections and the
simple reflection `s` decreases its length, then `s w` is the product of the list with one letter
deleted. -/
theorem exists_eraseIdx_prod_eq_of_wordLength_lt {s : T.WeylGroup} (hs : s ∈ T.simple)
    {l : List T.WeylGroup} (hl : ∀ x ∈ l, x ∈ T.simple) (h : ℓ (s * l.prod) < ℓ l.prod) :
    ∃ j < l.length, s * l.prod = (l.eraseIdx j).prod :=
  T.exists_eraseIdx_prod_eq_of_bruhatCell_mul_ne hs hl
    (by rw [Ne, T.bruhatCell_mul_eq_iff_wordLength_lt hs]; omega)

end TauCeti.TitsSystem
