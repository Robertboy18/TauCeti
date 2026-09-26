/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Topology.Algebra.Group.Units

/-!
# Connectedness in the unit groups of archimedean completions

Let `w` be an infinite place of a number field `K`.  The completion `w.Completion` is isometric to
`ℝ` when `w` is real and to `ℂ` when `w` is complex.  Consequently the unit group `w.Completionˣ`
is connected at a complex place, being homeomorphic to `ℂ ∖ {0}`, while at a real place the units
of positive real part form a preconnected set, homeomorphic to the positive half-line.

These are the archimedean inputs to the description of the open subgroups of the idele class
group: an open subgroup is also closed, so it contains every connected set of ideles through the
identity, and in particular the whole unit group at each complex place and the positive units at
each real place.

## Main results

* `NumberField.InfinitePlace.Completion.connectedSpace_units_of_isComplex`: the unit group of a
  complex completion is connected.
* `NumberField.InfinitePlace.Completion.isPreconnected_setOf_pos_units_of_isReal`: the positive
  units of a real completion form a preconnected set.
-/

public section

namespace NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {w : InfinitePlace K}

/-- **The unit group of a complex completion is connected**: it is homeomorphic to `ℂ ∖ {0}`. -/
theorem connectedSpace_units_of_isComplex (hw : w.IsComplex) : ConnectedSpace w.Completionˣ := by
  have h : IsPreconnected ((Units.val : w.Completionˣ → w.Completion) ⁻¹' {0}ᶜ) := by
    refine IsPreconnected.preimage_units_val ?_ (by simp)
    have h0 : IsPreconnected ({0}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) 0).isPreconnected
    convert (isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.mpr h0
      using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage]
    exact (map_eq_zero (extensionEmbedding w)).symm.not
  have huniv : ((Units.val : w.Completionˣ → w.Completion) ⁻¹' {0}ᶜ) = Set.univ :=
    Set.eq_univ_of_forall fun u ↦ u.ne_zero
  rw [huniv] at h
  exact connectedSpace_iff_univ.mpr ⟨Set.univ_nonempty, h⟩

/-- **The positive units of a real completion form a preconnected set**: they are homeomorphic to
the positive real half-line. -/
theorem isPreconnected_setOf_pos_units_of_isReal (hw : w.IsReal) :
    IsPreconnected {u : w.Completionˣ | 0 < extensionEmbeddingOfIsReal hw u} := by
  rw [← Set.preimage_ofPred_eq (p := fun x : w.Completion ↦ 0 < extensionEmbeddingOfIsReal hw x)
    (f := (Units.val : w.Completionˣ → w.Completion))]
  refine IsPreconnected.preimage_units_val ?_ (by simp)
  exact (isometryEquivRealOfIsReal hw).toHomeomorph.isPreconnected_preimage.mpr isPreconnected_Ioi

end NumberField.InfinitePlace.Completion
