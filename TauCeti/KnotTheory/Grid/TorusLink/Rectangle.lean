/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.Basic
public import TauCeti.KnotTheory.Grid.Unblocked
public import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Rectangles into the `X`-marking state of a torus link grid

In the standard torus link grid `torusLink p q` the `X`-markings occupy the diagonal shifted up by
`q + 1` rows, so the `X`-marking permutation is a power of the cyclic shift `finRotate`. Powers of
the cyclic shift preserve the cyclic intervals of the grid
(`Grid.mem_cIco_finRotate_pow_finRotate_pow`), which pins down every rectangle into the
`X`-marking state `G.X`, the grid state whose points are the lower-left corners of the `X`-marked
squares.

A rectangle from a grid state `y` to `G.X` has its two `G.X`-corners at the upper-left and
lower-right, so its rows form the cyclic interval from `G.X` of its right column to `G.X` of its
left column, while the `X`-markings of its covered columns occupy the complementary interval.
Hence every such rectangle avoids the `X`-markings and, for the same reason, contains no point of
`y` in its interior (`disjoint_coveredSquares_XSet_of_target_X_torusLink`,
`isEmpty_of_target_X_torusLink`).
The rectangles counted by the unblocked differential from `y` to `G.X` are therefore all the
rectangles from `y` to `G.X` (`unblockedRectangles_torusLink_X`), of which there are none or two
(`even_card_unblockedRectangles_torusLink_X`). This parity is the hypothesis under which the class
of `G.X` in unblocked grid homology is not torsion.

## Main results

* `TauCeti.GridDiagram.unblockedRectangles_torusLink_X`: every rectangle into the `X`-marking
  state of a torus link grid is empty and avoids the `X`-markings.
* `TauCeti.GridDiagram.even_card_unblockedRectangles_torusLink_X`: each grid state has an even
  number of counted rectangles into the `X`-marking state.

## References

The diagram follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3; the
`X`-marking state is the canonical generator of Chapter 6 there.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {p q : ℕ}

/-- The `X`-marking permutation of a torus link grid preserves and reflects membership in
half-open cyclic intervals. -/
theorem torusLink_X_mem_cIco_iff (a b c : Fin (p + 1 + (q + 1))) :
    (torusLink p q).X c ∈ Grid.cIco ((torusLink p q).X a) ((torusLink p q).X b) ↔
      c ∈ Grid.cIco a b := by
  simp only [torusLink_X_apply]
  exact Grid.mem_cIco_finRotate_pow_finRotate_pow _ _ _ _

/-- The `X`-marking permutation of a torus link grid preserves and reflects membership in open
cyclic intervals. -/
theorem torusLink_X_mem_cIoo_iff (a b c : Fin (p + 1 + (q + 1))) :
    (torusLink p q).X c ∈ Grid.cIoo ((torusLink p q).X a) ((torusLink p q).X b) ↔
      c ∈ Grid.cIoo a b := by
  simp only [torusLink_X_apply]
  exact Grid.mem_cIoo_finRotate_pow_finRotate_pow _ _ _ _

variable {y : GridState (p + 1 + (q + 1))} (r : GridRectangleBetween y (torusLink p q).X)

/-- A rectangle into the `X`-marking state of a torus link grid covers no `X`-marking: the
`X`-markings of its covered columns lie in the cyclic interval of rows complementary to the one it
covers. -/
theorem disjoint_coveredSquares_XSet_of_target_X_torusLink :
    Disjoint r.toGridRectangle.coveredSquares (torusLink p q).XSet := by
  rw [Finset.disjoint_left]
  rintro ⟨c, s⟩ hcs hX
  rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, r.bottom_def, r.top_def, ← r.map_right,
    ← r.map_left] at hcs
  rw [mk_mem_XSet] at hX
  obtain ⟨hc, hs⟩ := hcs
  rw [← hX, torusLink_X_mem_cIco_iff] at hs
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap r.left r.right) hc hs

/-- A rectangle into the `X`-marking state of a torus link grid is empty: the points of its source
state in the columns strictly between its sides are `X`-corners, which lie in the cyclic interval
of rows complementary to the one it spans. -/
theorem isEmpty_of_target_X_torusLink : r.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hcy
  rw [← r.map_of_ne c (Grid.ne_left_of_mem_cIoo hc) (Grid.ne_right_of_mem_cIoo hc),
    r.bottom_def, r.top_def, ← r.map_right, ← r.map_left, torusLink_X_mem_cIoo_iff] at hcy
  exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap r.left r.right) hc hcy

variable (y)

/-- The unblocked differential of a torus link grid counts every rectangle into the `X`-marking
state. -/
theorem unblockedRectangles_torusLink_X :
    (torusLink p q).unblockedRectangles y (torusLink p q).X =
      GridRectangleBetween.all y (torusLink p q).X := by
  ext r
  simp [isEmpty_of_target_X_torusLink, disjoint_coveredSquares_XSet_of_target_X_torusLink]

/-- Every grid state of a torus link grid has an even number, zero or two, of rectangles into the
`X`-marking state counted by the unblocked differential. -/
theorem even_card_unblockedRectangles_torusLink_X :
    Even ((torusLink p q).unblockedRectangles y (torusLink p q).X).card := by
  rw [unblockedRectangles_torusLink_X]
  rcases (GridRectangleBetween.all y (torusLink p q).X).eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty]
    exact Even.zero
  · rw [GridRectangleBetween.card_all_eq_two_of_nonempty h]
    exact even_two

end GridDiagram

end TauCeti
