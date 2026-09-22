/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Iterates of inflationary maps on the finsets of a finite type

A map `f` on the finsets of a finite type `α` that enlarges every finset, `s ⊆ f s`, can grow a
finset only `Fintype.card α` times before it stops. This file records the resulting bound: the
`Fintype.card α`-th iterate of `f` at any starting finset is a fixed point of `f`. It is the
termination argument behind every closure computed by "repeat until nothing changes" on a finite
carrier, stated once so that such computations can iterate a fixed number of times and remain
executable.

Mathlib's `Finset.image_iterate_stabilises_le_card` is the analogous statement for the decreasing
sequence of images of a finset under the iterates of a self-map of `α`; here the sequence is
increasing and the map acts on finsets.

## Main results

* `Finset.isFixedPt_iterate_card`: for `f` with `s ⊆ f s` for all `s`, the finset
  `f^[Fintype.card α] s` is a fixed point of `f`.
-/

public section

namespace TauCeti

variable {α : Type*} [Fintype α]

/-- An inflationary self-map of the finsets of a finite type reaches a fixed point after
`Fintype.card α` iterations, whatever the starting finset: the iterates form an increasing chain
of finsets, and such a chain can grow strictly at most `Fintype.card α` times. -/
theorem _root_.Finset.isFixedPt_iterate_card {f : Finset α → Finset α} (hf : ∀ s, s ⊆ f s)
    (s : Finset α) : Function.IsFixedPt f (f^[Fintype.card α] s) := by
  set N := Fintype.card α
  by_contra h
  -- No iterate below `N` is a fixed point either, since a fixed point stays fixed forever.
  have hne : ∀ k ≤ N, f^[k] s ≠ f^[k + 1] s := by
    intro k hk heq
    apply h
    have hfix : f^[N - k] (f^[k] s) = f^[k] s :=
      Function.iterate_fixed (by rw [← Function.iterate_succ_apply' f k s, heq]) _
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk] at hfix
    rw [Function.IsFixedPt, hfix, ← Function.iterate_succ_apply' f k s, heq]
  -- So the iterates grow strictly at every step up to `N`, which the size of `α` forbids.
  have hcard : ∀ k ≤ N + 1, k ≤ (f^[k] s).card := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro hk
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨by rw [Function.iterate_succ_apply']; exact hf _, hne k (by omega)⟩)
      have := ih (by omega)
      omega
  exact absurd (hcard (N + 1) le_rfl) (by have := Finset.card_le_univ (f^[N + 1] s); omega)

end TauCeti
